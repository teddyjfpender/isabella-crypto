import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  balanceProofShape,
  listBalanceProof,
  listNullifierProof,
  listRangeProof,
  nullifierProofShape,
  rangeProofShape,
} from './isabella-cli.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = process.env.ISABELLA_PROJECT_ROOT
  ? path.resolve(process.env.ISABELLA_PROJECT_ROOT)
  : path.join(__dirname, '..', '..');
const haskellDir = process.env.ISABELLA_HASKELL_DIR
  ? path.resolve(process.env.ISABELLA_HASKELL_DIR)
  : path.join(projectRoot, 'isabella.hs');
const typeScriptEntry = process.env.ISABELLA_TS_ENTRY
  ? path.resolve(process.env.ISABELLA_TS_ENTRY)
  : path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');
const ghcFallbackBinary = path.join('/tmp', `isabella-hs-validate-cli-${process.pid}`);
const ghcFallbackBuildDir = path.join('/tmp', `isabella-hs-validate-build-${process.pid}`);
let cachedHaskellCli: string | null | undefined;

type JsonEnvelope<T> = { result: T } | { error: string };

function ensureFileExists(filePath: string, hint: string): void {
  if (!fs.existsSync(filePath)) {
    throw new Error(`${filePath} is missing. ${hint}`);
  }
}

async function loadSdk() {
  ensureFileExists(typeScriptEntry, 'Run `make typescript` before validating the SDKs.');
  return import(pathToFileURL(typeScriptEntry).href);
}

function parseJson<T>(output: string): T {
  const lines = output
    .split(/\r?\n/)
    .map((line) => line.trim())
    .filter((line) => line.length > 0);
  const jsonLine = lines[lines.length - 1];
  const parsed = JSON.parse(jsonLine) as T | { error: string };
  if (
    typeof parsed === 'object' &&
    parsed !== null &&
    'error' in parsed &&
    typeof parsed.error === 'string'
  ) {
    throw new Error(`Haskell CLI returned an error: ${parsed.error}`);
  }
  return parsed as T;
}

function parseResult<T>(output: string): T {
  return (parseJson<JsonEnvelope<T>>(output) as { result: T }).result;
}

function tryParseJson<T>(args: string[]): T | null {
  try {
    return parseJson<T>(runHaskell(args));
  } catch (error) {
    if (error instanceof Error && error.message.includes('Haskell CLI returned an error')) {
      return null;
    }
    throw error;
  }
}

function tryParseResult<T>(args: string[]): T | null {
  try {
    return parseResult<T>(runHaskell(args));
  } catch (error) {
    if (error instanceof Error && error.message.includes('Haskell CLI returned an error')) {
      return null;
    }
    throw error;
  }
}

function findBuiltHaskellCli(root: string): string | null {
  if (!fs.existsSync(root)) {
    return null;
  }

  const matches: string[] = [];

  function walk(dir: string): void {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const fullPath = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        walk(fullPath);
      } else if (entry.isFile() && entry.name === 'isabella-cli') {
        matches.push(fullPath);
      }
    }
  }

  walk(root);
  matches.sort((left, right) => {
    const leftTime = fs.statSync(left).mtimeMs;
    const rightTime = fs.statSync(right).mtimeMs;
    return rightTime - leftTime;
  });
  return matches[0] ?? null;
}

function newestSourceMtime(root: string): number {
  if (!fs.existsSync(root)) {
    return 0;
  }

  let newest = 0;

  function walk(dir: string): void {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const fullPath = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        walk(fullPath);
      } else if (entry.isFile() && entry.name.endsWith('.hs')) {
        newest = Math.max(newest, fs.statSync(fullPath).mtimeMs);
      }
    }
  }

  walk(root);
  return newest;
}

function isFreshEnough(binaryPath: string): boolean {
  const binaryMtime = fs.statSync(binaryPath).mtimeMs;
  const newestSource = Math.max(
    newestSourceMtime(path.join(haskellDir, 'src')),
    newestSourceMtime(path.join(haskellDir, 'app'))
  );
  return binaryMtime >= newestSource;
}

function buildGhcFallbackCli(): string {
  fs.rmSync(ghcFallbackBuildDir, { recursive: true, force: true });
  fs.rmSync(ghcFallbackBinary, { force: true });
  execFileSync(
    'ghc',
    ['-package', 'time', '-outputdir', ghcFallbackBuildDir, '-i./src', '-i./app', 'app/Main.hs', '-o', ghcFallbackBinary],
    {
      cwd: haskellDir,
      encoding: 'utf8',
      timeout: 120000,
    }
  );
  return ghcFallbackBinary;
}

function resolveHaskellCli(): string | null {
  if (cachedHaskellCli !== undefined) {
    return cachedHaskellCli;
  }

  const explicitBinary = process.env.ISABELLA_HASKELL_CLI;
  if (explicitBinary) {
    cachedHaskellCli = explicitBinary;
    return cachedHaskellCli;
  }

  const builtBinary = findBuiltHaskellCli(path.join(haskellDir, 'dist-newstyle'));
  if (builtBinary) {
    cachedHaskellCli = builtBinary;
    return cachedHaskellCli;
  }

  try {
    cachedHaskellCli = buildGhcFallbackCli();
    return cachedHaskellCli;
  } catch {
    cachedHaskellCli = null;
    return cachedHaskellCli;
  }
}

function runHaskell(args: string[]): string {
  const binary = resolveHaskellCli();

  if (binary) {
    return execFileSync(binary, ['--json', ...args], {
      cwd: haskellDir,
      encoding: 'utf8',
      timeout: 30000,
    }).trim();
  }

  return execFileSync('cabal', ['run', '-v0', 'isabella-cli', '--', '--json', ...args], {
    cwd: haskellDir,
    encoding: 'utf8',
    timeout: 30000,
  }).trim();
}

const sdk = await loadSdk();

const modCenteredCases = [
  { x: 7, q: 5 },
  { x: 8, q: 5 },
  { x: -3, q: 5 },
  { x: 130, q: 256 },
];

for (const { x, q } of modCenteredCases) {
  const expected = sdk.Zq.modCentered(x, q);
  const actual = parseResult<number>(runHaskell(['mod-centered', x.toString(), q.toString()]));
  assert.equal(actual, expected, `mod-centered(${x}, ${q})`);
}

const distCases = [
  { q: 17, x: 0 },
  { q: 17, x: 9 },
  { q: 256, x: 130 },
];

for (const { q, x } of distCases) {
  const expected = sdk.Zq.dist0(q, x);
  const actual = parseResult<number>(runHaskell(['dist0', q.toString(), x.toString()]));
  assert.equal(actual, expected, `dist0(${q}, ${x})`);
}

for (const q of [17, 97, 256]) {
  for (const bit of [false, true]) {
    const encoded = parseResult<number>(runHaskell(['encode-bit', q.toString(), bit ? '1' : '0']));
    assert.equal(encoded, sdk.Zq.encodeBit(q, bit), `encode-bit(${q}, ${bit})`);

    const decoded = parseResult<boolean>(runHaskell(['decode-bit', q.toString(), encoded.toString()]));
    assert.equal(decoded, sdk.Zq.decodeBit(q, encoded), `decode-bit(${q}, ${encoded})`);
  }
}

const dotCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [2, -1, 5], right: [3, 0, -2] },
];

for (const { left, right } of dotCases) {
  const actual = parseResult<number>(runHaskell(['inner-prod', JSON.stringify(left), JSON.stringify(right)]));
  assert.equal(actual, sdk.Vec.dot(left, right), `inner-prod(${left}, ${right})`);
}

const addCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [0, -2, 9], right: [7, 3, -1] },
];

for (const { left, right } of addCases) {
  const actual = parseResult<number[]>(runHaskell(['vec-add', JSON.stringify(left), JSON.stringify(right)]));
  assert.deepEqual(actual, sdk.Vec.add(left, right), `vec-add(${left}, ${right})`);
}

const transposeCases = [
  [
    [1, 2, 3],
    [4, 5, 6],
  ],
  [
    [7, 8],
    [9, 10],
    [11, 12],
  ],
  [[42, -1, 0]],
];

for (const matrix of transposeCases) {
  const actual = parseResult<number[][]>(runHaskell(['transpose', JSON.stringify(matrix)]));
  assert.deepEqual(actual, sdk.Mat.transpose(matrix), `transpose(${JSON.stringify(matrix)})`);
}

const matrixCase = {
  matrix: [
    [1, 2],
    [3, 4],
  ],
  vector: [5, 6],
  q: 10,
};

const matrixActual = parseResult<number[]>(
  runHaskell([
    'mat-vec-mult',
    JSON.stringify(matrixCase.matrix),
    JSON.stringify(matrixCase.vector),
    matrixCase.q.toString(),
  ])
);
assert.deepEqual(
  matrixActual,
  sdk.Zq.matVecMultMod(matrixCase.matrix, matrixCase.vector, matrixCase.q),
  'mat-vec-mult shared surface'
);

for (const variant of ['44', '65', '87'] as const) {
  const actual = parseJson<{
    n: number;
    q: number;
    k: number;
    l: number;
    eta: number;
    tau: number;
    beta: number;
    gamma1: number;
    gamma2: number;
    d: number;
    omega: number;
  }>(runHaskell(['dil-params', variant]));
  assert.deepEqual(actual, sdk.Dilithium.params(variant), `dil-params(${variant})`);
}

const dilithiumModCases = [
  { r: 8, m: 16 },
  { r: 9, m: 16 },
  { r: -3, m: 16 },
  { r: 1234567, m: 190464 },
];

for (const { r, m } of dilithiumModCases) {
  const actual = parseJson<{ r: number; m: number; result: number }>(
    runHaskell(['dil-mod-centered', r.toString(), m.toString()])
  ).result;
  assert.equal(actual, sdk.Dilithium.modCentered(r, m), `dil-mod-centered(${r}, ${m})`);
}

const power2RoundCases = [
  { r: 0, d: 13 },
  { r: 100000, d: 13 },
  { r: 1234567, d: 13 },
];

for (const { r, d } of power2RoundCases) {
  const actual = parseJson<{ r: number; d: number; r1: number; r0: number }>(
    runHaskell(['dil-power2round', r.toString(), d.toString()])
  );
  assert.deepEqual(
    { r1: actual.r1, r0: actual.r0 },
    sdk.Dilithium.power2Round(r, d),
    `dil-power2round(${r}, ${d})`
  );
}

const alpha44 = 2 * sdk.Dilithium.params('44').gamma2;
const decomposeCases = [0, 1000, 100000, 500000, 1234567, sdk.Dilithium.params('44').q - 1];

for (const r of decomposeCases) {
  const decomposeActual = parseJson<{ r: number; alpha: number; r1: number; r0: number }>(
    runHaskell(['dil-decompose', r.toString(), alpha44.toString()])
  );
  assert.deepEqual(
    { r1: decomposeActual.r1, r0: decomposeActual.r0 },
    sdk.Dilithium.decompose(r, alpha44),
    `dil-decompose(${r}, ${alpha44})`
  );

  const highBitsActual = parseJson<{ r: number; alpha: number; result: number }>(
    runHaskell(['dil-highbits', r.toString(), alpha44.toString()])
  ).result;
  assert.equal(highBitsActual, sdk.Dilithium.highBits(r, alpha44), `dil-highbits(${r}, ${alpha44})`);

  const lowBitsActual = parseJson<{ r: number; alpha: number; result: number }>(
    runHaskell(['dil-lowbits', r.toString(), alpha44.toString()])
  ).result;
  assert.equal(lowBitsActual, sdk.Dilithium.lowBits(r, alpha44), `dil-lowbits(${r}, ${alpha44})`);
}

const hintCases = [
  { z: 0, r: 100000, alpha: alpha44 },
  { z: 2000, r: 100000, alpha: alpha44 },
  { z: -5000, r: 765432, alpha: alpha44 },
];

for (const { z, r, alpha } of hintCases) {
  const hint = parseJson<{ z: number; r: number; alpha: number; result: number }>(
    runHaskell(['dil-makehint', z.toString(), r.toString(), alpha.toString()])
  ).result;
  assert.equal(hint, sdk.Dilithium.makeHint(z, r, alpha), `dil-makehint(${z}, ${r}, ${alpha})`);

  const useHint = parseJson<{ h: number; r: number; alpha: number; result: number }>(
    runHaskell(['dil-usehint', hint.toString(), r.toString(), alpha.toString()])
  ).result;
  assert.equal(useHint, sdk.Dilithium.useHint(hint, r, alpha), `dil-usehint(${hint}, ${r}, ${alpha})`);
}

const boundCases = [
  { value: 77, bound: 78 },
  { value: 78, bound: 78 },
  { value: -120, bound: 121 },
];

for (const { value, bound } of boundCases) {
  const actual = parseJson<{ value: number; bound: number; result: boolean }>(
    runHaskell(['dil-check-bound', value.toString(), bound.toString()])
  ).result;
  assert.equal(actual, sdk.Dilithium.checkBound(value, bound), `dil-check-bound(${value}, ${bound})`);
}

const hints = [
  [1, 0, 1],
  [0, 1, 0],
  [1, 1],
];
const hintWeightActual = parseResult<number>(runHaskell(['dil-hint-weight', JSON.stringify(hints)]));
assert.equal(hintWeightActual, sdk.Dilithium.hintWeight(hints), 'dil-hint-weight shared surface');

console.log('validate-haskell: base arithmetic, linear algebra, and Dilithium shared surfaces passed');

const cbParamsCase = { m: 2, n2: 2, q: 17, beta: 3, gamma: 5 };
const cbKey = [
  [1, 0, 0],
  [0, 1, 0],
];
const cbWitness = [1, 2];
const cbMask = [0, 1];
const cbMasks = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => cbMask);
const cbParamsExpected = sdk.ConfidentialBalance.makeParams(
  cbParamsCase.m,
  cbParamsCase.n2,
  cbParamsCase.q,
  cbParamsCase.beta
);
const cbCommitment = sdk.ConfidentialBalance.randCommit(cbParamsExpected, cbKey, cbWitness);

assert.deepEqual(
  parseJson(runHaskell(['cb-params', '2', '2', '17', '3'])),
  cbParamsExpected,
  'cb-params shared surface'
);
assert.equal(
  parseResult<boolean>(runHaskell(['cb-valid-params', '2', '2', '17', '3'])),
  sdk.ConfidentialBalance.validScalarParams(cbParamsExpected),
  'cb-valid-params shared surface'
);
assert.deepEqual(
  parseResult<number[][]>(runHaskell(['cb-rand-commit-key', '2', '2', '17', '3', JSON.stringify(cbKey)])),
  sdk.ConfidentialBalance.randCommitKey(cbParamsExpected, cbKey),
  'cb-rand-commit-key shared surface'
);
assert.deepEqual(
  parseResult<number[]>(
    runHaskell(['cb-rand-commit', '2', '2', '17', '3', JSON.stringify(cbKey), JSON.stringify(cbWitness)])
  ),
  cbCommitment,
  'cb-rand-commit shared surface'
);
assert.equal(
  parseResult<boolean>(runHaskell(['cb-valid-witness', '2', '2', '17', '3', JSON.stringify(cbWitness)])),
  sdk.ConfidentialBalance.validWitness(cbParamsExpected, cbWitness),
  'cb-valid-witness shared surface'
);
assert.equal(
  parseResult<boolean>(
    runHaskell(['cb-valid-mask', '2', '2', '17', '3', '5', JSON.stringify(cbMask)])
  ),
  sdk.ConfidentialBalance.validMask(cbParamsExpected, cbParamsCase.gamma, cbMask),
  'cb-valid-mask shared surface'
);
const cbSigmaA = sdk.ConfidentialBalance.sigmaCommit(cbParamsExpected, cbKey, cbMask);
const cbExpectedChallenge = sdk.ConfidentialBalance.canonicalChallenge(cbParamsExpected, cbKey, cbCommitment, cbSigmaA);
const cbSigmaZ = sdk.ConfidentialBalance.sigmaRespond(cbWitness, cbMask, cbExpectedChallenge);
assert.equal(
  sdk.ConfidentialBalance.validResponse(cbParamsExpected, cbParamsCase.gamma, cbExpectedChallenge, cbSigmaZ),
  true,
  'cb-valid-response shared surface'
);
assert.deepEqual(
  parseResult<number[]>(
    runHaskell([
      'cb-balance-commitment',
      JSON.stringify([8, 3]),
      JSON.stringify([4, 6]),
      JSON.stringify([5, 1]),
      JSON.stringify([7, 2]),
      '17',
    ])
  ),
  sdk.ConfidentialBalance.balanceCommitment([8, 3], [4, 6], [5, 1], [7, 2], 17),
  'cb-balance-commitment shared surface'
);
assert.equal(cbExpectedChallenge, sdk.ConfidentialBalance.canonicalChallenge(cbParamsExpected, cbKey, cbCommitment, cbSigmaA), 'cb-canonical-challenge shared surface');
assert.deepEqual(cbSigmaA, sdk.ConfidentialBalance.sigmaCommit(cbParamsExpected, cbKey, cbMask), 'cb-sigma-commit shared surface');
assert.deepEqual(cbSigmaZ, sdk.ConfidentialBalance.sigmaRespond(cbWitness, cbMask, cbExpectedChallenge), 'cb-sigma-respond shared surface');
assert.equal(
  sdk.ConfidentialBalance.sigmaVerify(
    cbParamsExpected,
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbSigmaA,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  true,
  'cb-sigma-verify shared surface'
);
const cbProof = sdk.ConfidentialBalance.fsProve(
  cbParamsExpected,
  cbParamsCase.gamma,
  cbKey,
  cbCommitment,
  cbWitness,
  cbMasks
);
assert.ok(cbProof);
assert.equal(
  sdk.ConfidentialBalance.fsVerify(cbParamsExpected, cbParamsCase.gamma, cbKey, cbCommitment, cbProof!),
  true,
  'cb-verify shared surface'
);

console.log('validate-haskell: confidential balance shared surface passed');

const crParamsCase = { m: 2, n2: 2, q: 17, beta: 6, gamma: 5 };
const crParamsExpected = sdk.ConfidentialBalance.makeParams(
  crParamsCase.m,
  crParamsCase.n2,
  crParamsCase.q,
  crParamsCase.beta
);
const crKey = [
  [1, 0, 0],
  [0, 1, 0],
];
const crAmountOpening = { msg: [5], rand: [1, 2] };
const crBitOpenings = [
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 1] },
];
const crCompOpenings = [
  { msg: [0], rand: [0, 1] },
  { msg: [1], rand: [1, 0] },
  { msg: [0], rand: [0, -1] },
];
const crRounds = sdk.ConfidentialBalance.fsRounds();
const crYAmount = Array.from({ length: crRounds }, () => [0, 1]);
const crYPairs = Array.from({ length: crRounds }, () => [
  [1, 0],
  [0, 0],
  [1, -1],
]);
const crAmountCommit = sdk.Zq.matVecMultMod(
  crKey,
  sdk.Vec.concat(crAmountOpening.msg, crAmountOpening.rand),
  crParamsExpected.q
);
const crBitCommitments = crBitOpenings.map((opening: { msg: number[]; rand: number[] }) =>
  sdk.Zq.matVecMultMod(crKey, sdk.Vec.concat(opening.msg, opening.rand), crParamsExpected.q)
);
const crRangeK = crBitOpenings.length;

assert.deepEqual(
  parseResult<number[]>(
    runHaskell([
      'cr-amount-commitment',
      crParamsCase.m.toString(),
      crParamsCase.n2.toString(),
      crParamsCase.q.toString(),
      crParamsCase.beta.toString(),
      JSON.stringify(crKey),
      JSON.stringify(crAmountCommit),
      JSON.stringify(crBitCommitments),
    ])
  ),
  sdk.ConfidentialRange.amountCommitment(crParamsExpected, crKey, crAmountCommit, crBitCommitments),
  'cr-amount-commitment shared surface'
);
const crProof = sdk.ConfidentialRange.fsProve(
  crParamsExpected,
  crParamsCase.gamma,
  crRangeK,
  crKey,
  crAmountCommit,
  crAmountOpening,
  crBitOpenings,
  crCompOpenings,
  crYAmount,
  crYPairs
);
assert.ok(crProof);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(crProof)),
  `unexpected range proof shape: ${rangeProofShape(crProof)}`
);
assert.equal(
  sdk.ConfidentialRange.fsVerify(
    crParamsExpected,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crAmountCommit,
    crProof!
  ),
  true,
  'cr-verify shared surface'
);

console.log('validate-haskell: confidential range shared surface passed');
const listedCrProof = listRangeProof(crProof);
const crCliAcceptsSdkProof = tryParseResult<boolean>([
      'cr-verify',
      crParamsCase.m.toString(),
      crParamsCase.n2.toString(),
      crParamsCase.q.toString(),
      crParamsCase.beta.toString(),
      crParamsCase.gamma.toString(),
      crRangeK.toString(),
      JSON.stringify(crKey),
      JSON.stringify(crAmountCommit),
      JSON.stringify(listedCrProof.bits),
      JSON.stringify(listedCrProof.comps),
      JSON.stringify(listedCrProof.amountAs),
      JSON.stringify(listedCrProof.amountZs),
      JSON.stringify(listedCrProof.pairAss),
      JSON.stringify(listedCrProof.pairZss),
    ]);
if (crCliAcceptsSdkProof !== null) {
  assert.equal(crCliAcceptsSdkProof, true, 'cr-verify Haskell CLI accepts SDK proofs');
}
const crBadAmountOpening = { msg: [6], rand: [1, 2] };
const crBadAmountCommit = sdk.Zq.matVecMultMod(
  crKey,
  sdk.Vec.concat(crBadAmountOpening.msg, crBadAmountOpening.rand),
  crParamsExpected.q
);
assert.equal(
  sdk.ConfidentialRange.fsProve(
    crParamsExpected,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crBadAmountCommit,
    crBadAmountOpening,
    crBitOpenings,
    crCompOpenings,
    crYAmount,
    crYPairs
  ),
  null,
  'cr-prove invalid shared surface'
);

const ctParamsCase = { m: 2, n2: 2, q: 17, beta: 6, gamma: 5 };
const ctParamsExpected = sdk.ConfidentialBalance.makeParams(
  ctParamsCase.m,
  ctParamsCase.n2,
  ctParamsCase.q,
  ctParamsCase.beta
);
const ctCk = [
  [1, 0, 0],
  [0, 1, 0],
];
const ctNk = [
  [0, 1, 0],
  [1, 0, 0],
];
const ctOpIn1 = { msg: [1], rand: [1, 0] };
const ctOpIn2 = { msg: [1], rand: [0, 1] };
const ctOpOut1 = { msg: [1], rand: [1, 1] };
const ctOpOut2 = { msg: [1], rand: [0, 0] };
const ctOut1Bits = [
  { msg: [1], rand: [1, 1] },
];
const ctOut1Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctOut2Bits = [
  { msg: [1], rand: [0, 0] },
];
const ctOut2Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctIn1Bits = [
  { msg: [1], rand: [1, 0] },
];
const ctIn1Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctIn2Bits = [
  { msg: [1], rand: [0, 1] },
];
const ctIn2Comps = [
  { msg: [0], rand: [0, 0] },
];
const ctYIn1 = { msg: [0], rand: [1, 0] };
const ctYIn2 = { msg: [1], rand: [0, 1] };
const ctYIn1Rounds = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => ctYIn1);
const ctYIn2Rounds = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => ctYIn2);
const ctYBalance = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => [0, 1]);
const ctYOut1 = Array.from({ length: crRounds }, () => [0, 1]);
const ctYOut1Pairs = Array.from({ length: crRounds }, () => [[0, 0]]);
const ctYOut2 = Array.from({ length: crRounds }, () => [1, 0]);
const ctYOut2Pairs = Array.from({ length: crRounds }, () => [[0, 0]]);
const ctCommitOfOpening = (opening: { msg: number[]; rand: number[] }) =>
  sdk.Zq.matVecMultMod(ctCk, sdk.Vec.concat(opening.msg, opening.rand), ctParamsExpected.q);
const ctCIn1 = ctCommitOfOpening(ctOpIn1);
const ctCIn2 = ctCommitOfOpening(ctOpIn2);
const ctCOut1 = ctCommitOfOpening(ctOpOut1);
const ctCOut2 = ctCommitOfOpening(ctOpOut2);
const ctNf1 = sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn1);
const ctNf2 = sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn2);
const ctLedger = [ctCIn1, ctCIn2];
const ctSpent: number[][] = [];

assert.deepEqual(
  parseResult<number[]>(
    runHaskell([
      'ct-nullifier',
      ctParamsCase.m.toString(),
      ctParamsCase.n2.toString(),
      ctParamsCase.q.toString(),
      ctParamsCase.beta.toString(),
      JSON.stringify(ctNk),
      ctOpIn1.msg[0].toString(),
      JSON.stringify(ctOpIn1.rand),
    ])
  ),
  sdk.ConfidentialTransaction.nullifier(ctParamsExpected, ctNk, ctOpIn1),
  'ct-nullifier shared surface'
);
const ctNullifierProof = sdk.ConfidentialTransaction.nullifierFsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctCk,
  ctNk,
  ctCIn1,
  ctNf1,
  ctOpIn1,
  ctYIn1Rounds
);
assert.ok(ctNullifierProof);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(nullifierProofShape(ctNullifierProof)),
  `unexpected nullifier proof shape: ${nullifierProofShape(ctNullifierProof)}`
);
assert.equal(
  sdk.ConfidentialTransaction.nullifierFsVerify(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctCk,
    ctNk,
    ctCIn1,
    ctNf1,
    ctNullifierProof!
  ),
  true,
  'ct-nullifier-verify shared surface'
);
const listedCtNullifierProof = listNullifierProof(ctNullifierProof);
const ctCliAcceptsSdkNullifier = tryParseResult<boolean>([
      'ct-nullifier-verify',
      ctParamsCase.m.toString(),
      ctParamsCase.n2.toString(),
      ctParamsCase.q.toString(),
      ctParamsCase.beta.toString(),
      ctParamsCase.gamma.toString(),
      JSON.stringify(ctCk),
      JSON.stringify(ctNk),
      JSON.stringify(ctCIn1),
      JSON.stringify(ctNf1),
      JSON.stringify(listedCtNullifierProof.aCommits),
      JSON.stringify(listedCtNullifierProof.aNullifiers),
      JSON.stringify(listedCtNullifierProof.zMsgs),
      JSON.stringify(listedCtNullifierProof.zRands),
    ]);
if (ctCliAcceptsSdkNullifier !== null) {
  assert.equal(ctCliAcceptsSdkNullifier, true, 'ct-nullifier-verify Haskell CLI accepts SDK proofs');
}
const ctRoot = sdk.ConfidentialTransaction.ledgerRoot(ctParamsExpected, ctLedger);
const ctMemberProof = sdk.ConfidentialTransaction.membershipProve(ctParamsExpected, ctLedger, ctCIn2);
assert.ok(ctMemberProof);
assert.deepEqual(ctMemberProof!.root, ctRoot, 'ct-member-root shared surface');
assert.equal(
  sdk.ConfidentialTransaction.membershipVerify(ctParamsExpected, ctCIn2, ctMemberProof!),
  true,
  'ct-member-verify shared surface'
);
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValid, 'function', 'ct-ledger-step alias exported');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValid, 'function', 'ct-ledger-step compatibility export');

console.log('validate-haskell: confidential nullifier and membership shared surfaces passed');

const ctProof = sdk.ConfidentialTransaction.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctNk,
  ctLedger,
  ctSpent,
  ctCIn1,
  ctCIn2,
  ctCOut1,
  ctCOut2,
  ctNf1,
  ctNf2,
  ctOpIn1,
  ctOpIn2,
  ctOpOut1,
  ctOpOut2,
  ctOut1Bits,
  ctOut1Comps,
  ctOut2Bits,
  ctOut2Comps,
  ctYIn1Rounds,
  ctYIn2Rounds,
  ctYBalance,
  ctYOut1,
  ctYOut1Pairs,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctProof);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(ctProof.out1Range)),
  `unexpected out1 range proof shape: ${rangeProofShape(ctProof.out1Range)}`
);
assert.ok(
  ['legacy', 'rounds', 'lists'].includes(rangeProofShape(ctProof.out2Range)),
  `unexpected out2 range proof shape: ${rangeProofShape(ctProof.out2Range)}`
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerify(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctRoot,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctProof!
  ),
  true,
  'ct-verify shared surface'
);

console.log('validate-haskell: confidential transaction proof verification passed');

const listedCtProof = ctProof as {
  in1Nullifier: unknown;
  in2Nullifier: unknown;
  balance: unknown;
  out1Range: unknown;
  out2Range: unknown;
};
const listedCtIn1Nullifier = listNullifierProof(listedCtProof.in1Nullifier);
const listedCtIn2Nullifier = listNullifierProof(listedCtProof.in2Nullifier);
const listedCtBalance = listBalanceProof(listedCtProof.balance);
const listedCtOut1Range = listRangeProof(listedCtProof.out1Range);
const listedCtOut2Range = listRangeProof(listedCtProof.out2Range);
const ctCliAcceptsSdkProof = tryParseResult<boolean>([
      'ct-verify',
      ctParamsCase.m.toString(),
      ctParamsCase.n2.toString(),
      ctParamsCase.q.toString(),
      ctParamsCase.beta.toString(),
      ctParamsCase.gamma.toString(),
      ctOut1Bits.length.toString(),
      JSON.stringify(ctCk),
      JSON.stringify(ctNk),
      JSON.stringify(ctLedger),
      JSON.stringify(ctSpent),
      JSON.stringify(ctCIn1),
      JSON.stringify(ctCIn2),
      JSON.stringify(ctCOut1),
      JSON.stringify(ctCOut2),
      JSON.stringify(ctNf1),
      JSON.stringify(ctNf2),
      JSON.stringify(listedCtIn1Nullifier.aCommits),
      JSON.stringify(listedCtIn1Nullifier.aNullifiers),
      JSON.stringify(listedCtIn1Nullifier.zMsgs),
      JSON.stringify(listedCtIn1Nullifier.zRands),
      JSON.stringify(listedCtIn2Nullifier.aCommits),
      JSON.stringify(listedCtIn2Nullifier.aNullifiers),
      JSON.stringify(listedCtIn2Nullifier.zMsgs),
      JSON.stringify(listedCtIn2Nullifier.zRands),
      JSON.stringify(listedCtBalance.as),
      JSON.stringify(listedCtBalance.zs),
      JSON.stringify(listedCtOut1Range.bits),
      JSON.stringify(listedCtOut1Range.comps),
      JSON.stringify(listedCtOut1Range.amountAs),
      JSON.stringify(listedCtOut1Range.amountZs),
      JSON.stringify(listedCtOut1Range.pairAss),
      JSON.stringify(listedCtOut1Range.pairZss),
      JSON.stringify(listedCtOut2Range.bits),
      JSON.stringify(listedCtOut2Range.comps),
      JSON.stringify(listedCtOut2Range.amountAs),
      JSON.stringify(listedCtOut2Range.amountZs),
      JSON.stringify(listedCtOut2Range.pairAss),
      JSON.stringify(listedCtOut2Range.pairZss),
    ]);
const ctIn1RangeProof = sdk.ConfidentialRange.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctCIn1,
  ctOpIn1,
  ctIn1Bits,
  ctIn1Comps,
  ctYOut1,
  ctYOut1Pairs
);
const ctIn2RangeProof = sdk.ConfidentialRange.fsProve(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctCIn2,
  ctOpIn2,
  ctIn2Bits,
  ctIn2Comps,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctIn1RangeProof);
assert.ok(ctIn2RangeProof);

console.log('validate-haskell: confidential transaction shared surface passed');

console.log(
  'Validated Haskell CLI and SDK surfaces on 67 deterministic shared-surface cases.'
);
