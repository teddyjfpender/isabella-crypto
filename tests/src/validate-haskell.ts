import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  balanceProofShape,
  ctMerkleProofDigestArgs,
  ctVerifyMerkleArgs,
  ctVerifyMerkleEnvelopeArgs,
  listBalanceProof,
  listNullifierProof,
  listRangeProof,
  nullifierProofShape,
  rangeProofShape,
} from './isabella-cli.ts';
import { merkleTransactionProofMutations } from './confidential-proof-mutations.ts';

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
const bignumVectorsPath = path.join(projectRoot, 'tests/fixtures/confidential-bignum-vectors.json');
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

type SampleOpening = { msg: number[]; rand: number[] };
type MembershipProof = {
  index: number;
  root: number[];
  siblings: number[][];
  directions: boolean[];
};

function allBounded(values: number[], bound: number): boolean {
  return values.every(value => Number.isSafeInteger(value) && Math.abs(value) <= bound);
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

function expectHaskellCommandRejected(args: string[], label: string): void {
  assert.equal(tryParseJson<JsonEnvelope<unknown>>(args), null, label);
}

function nonCanonicalIntegerText(value: string): string {
  return value === '0' ? '-0' : `0${value}`;
}

function nonCanonicalFirstInteger(value: string): string {
  return value.replace(/-?\d+/, '-0');
}

const unsafeProtocolInteger = '9007199254740992';

function unsafeFirstInteger(value: string): string {
  return value.replace(/-?\d+/, unsafeProtocolInteger);
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
const bignumVectors = JSON.parse(fs.readFileSync(bignumVectorsPath, 'utf8')) as {
  scalarCases: Array<{ name: string; decimal: string; encodedHex: string; digest: string }>;
  vectorCases: Array<{ name: string; decimals: string[]; encodedHex: string; digest: string }>;
  rejectedDecimals: string[];
};

for (const entry of bignumVectors.scalarCases) {
  assert.equal(
    parseResult<string>(runHaskell(['ct-bignum-encode', entry.decimal])),
    entry.encodedHex,
    `ct-bignum-encode Haskell/fixture parity for ${entry.name}`
  );
  assert.equal(
    sdk.ConfidentialBignum.encodeIntegerHex(entry.decimal),
    entry.encodedHex,
    `ct-bignum-encode TypeScript/fixture parity for ${entry.name}`
  );
}

for (const entry of bignumVectors.vectorCases) {
  assert.equal(
    parseResult<string>(runHaskell(['ct-bignum-vector-encode', ...entry.decimals])),
    entry.encodedHex,
    `ct-bignum-vector-encode Haskell/fixture parity for ${entry.name}`
  );
  assert.equal(
    sdk.ConfidentialBignum.encodeIntegerVectorHex(entry.decimals),
    entry.encodedHex,
    `ct-bignum-vector-encode TypeScript/fixture parity for ${entry.name}`
  );
}

for (const decimal of bignumVectors.rejectedDecimals) {
  expectHaskellCommandRejected(['ct-bignum-encode', decimal], `ct-bignum-encode Haskell rejects ${decimal}`);
}

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

const haskellSampleBalanceMask = parseResult<number[]>(
  runHaskell([
    'cb-sample-mask',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
  ])
);
assert.equal(haskellSampleBalanceMask.length, cbParamsCase.n2, 'cb-sample-mask length');
assert.ok(allBounded(haskellSampleBalanceMask, cbParamsCase.gamma), 'cb-sample-mask bound');
assert.ok(
  sdk.ConfidentialBalance.validMask(cbParamsExpected, cbParamsCase.gamma, haskellSampleBalanceMask),
  'cb-sample-mask valid mask'
);

const haskellSampleBalanceMasks = parseResult<number[][]>(
  runHaskell([
    'cb-sample-masks',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
    '4',
  ])
);
assert.equal(haskellSampleBalanceMasks.length, 4, 'cb-sample-masks count');
assert.ok(
  haskellSampleBalanceMasks.every(mask => mask.length === cbParamsCase.n2 && allBounded(mask, cbParamsCase.gamma)),
  'cb-sample-masks shape and bound'
);

const haskellSampleOpening = parseResult<SampleOpening>(
  runHaskell(['ct-sample-opening', '1', cbParamsCase.n2.toString(), cbParamsCase.gamma.toString()])
);
assert.equal(haskellSampleOpening.msg.length, 1, 'ct-sample-opening msg length');
assert.equal(haskellSampleOpening.rand.length, cbParamsCase.n2, 'ct-sample-opening rand length');
assert.ok(allBounded(haskellSampleOpening.msg, cbParamsCase.gamma), 'ct-sample-opening msg bound');
assert.ok(allBounded(haskellSampleOpening.rand, cbParamsCase.gamma), 'ct-sample-opening rand bound');

const haskellSampleOpenings = parseResult<SampleOpening[]>(
  runHaskell([
    'ct-sample-openings',
    '4',
    '1',
    cbParamsCase.n2.toString(),
    cbParamsCase.gamma.toString(),
  ])
);
assert.equal(haskellSampleOpenings.length, 4, 'ct-sample-openings count');
assert.ok(
  haskellSampleOpenings.every(mask =>
    mask.msg.length === 1 &&
    mask.rand.length === cbParamsCase.n2 &&
    allBounded(mask.msg, cbParamsCase.gamma) &&
    allBounded(mask.rand, cbParamsCase.gamma)
  ),
  'ct-sample-openings shape and bound'
);

const haskellSampleNullifierMask = parseResult<SampleOpening>(
  runHaskell([
    'ct-sample-nullifier-mask',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
  ])
);
assert.equal(haskellSampleNullifierMask.msg.length, 1, 'ct-sample-nullifier-mask msg length');
assert.equal(haskellSampleNullifierMask.rand.length, cbParamsCase.n2, 'ct-sample-nullifier-mask rand length');
assert.ok(allBounded(haskellSampleNullifierMask.msg, cbParamsCase.gamma), 'ct-sample-nullifier-mask msg bound');
assert.ok(allBounded(haskellSampleNullifierMask.rand, cbParamsCase.gamma), 'ct-sample-nullifier-mask rand bound');

const haskellSampleNullifierMasks = parseResult<SampleOpening[]>(
  runHaskell([
    'ct-sample-nullifier-masks',
    cbParamsCase.m.toString(),
    cbParamsCase.n2.toString(),
    cbParamsCase.q.toString(),
    cbParamsCase.beta.toString(),
    cbParamsCase.gamma.toString(),
    '4',
  ])
);
assert.equal(haskellSampleNullifierMasks.length, 4, 'ct-sample-nullifier-masks count');
assert.ok(
  haskellSampleNullifierMasks.every(mask =>
    mask.msg.length === 1 &&
    mask.rand.length === cbParamsCase.n2 &&
    allBounded(mask.msg, cbParamsCase.gamma) &&
    allBounded(mask.rand, cbParamsCase.gamma)
  ),
  'ct-sample-nullifier-masks shape and bound'
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
assert.equal(
  parseResult<number>(
    runHaskell([
      'cb-canonical-challenge',
      '2',
      '2',
      '17',
      '3',
      JSON.stringify(cbKey),
      JSON.stringify(cbCommitment),
      JSON.stringify(cbSigmaA),
    ])
  ),
  cbExpectedChallenge,
  'cb-canonical-challenge shared surface'
);
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
const ctListedNullifierProof = listNullifierProof(ctNullifierProof);
const ctExpectedNullifierChallenge = sdk.ConfidentialTransaction.canonicalNullifierChallenge(
  ctParamsExpected,
  ctCk,
  ctNk,
  ctCIn1,
  ctNf1,
  ctListedNullifierProof.aCommits[0],
  ctListedNullifierProof.aNullifiers[0]
);
assert.equal(
  parseResult<number>(
    runHaskell([
      'ct-nullifier-canonical-challenge',
      '2',
      '2',
      '17',
      '3',
      JSON.stringify(ctCk),
      JSON.stringify(ctNk),
      JSON.stringify(ctCIn1),
      JSON.stringify(ctNf1),
      JSON.stringify(ctListedNullifierProof.aCommits[0]),
      JSON.stringify(ctListedNullifierProof.aNullifiers[0]),
    ])
  ),
  ctExpectedNullifierChallenge,
  'ct-nullifier-canonical-challenge shared surface'
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
const listedCtNullifierProof = ctListedNullifierProof;
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
const ctCliMemberProof = parseJson<MembershipProof>(
  runHaskell([
    'ct-member-prove',
    ctParamsCase.m.toString(),
    ctParamsCase.n2.toString(),
    ctParamsCase.q.toString(),
    ctParamsCase.beta.toString(),
    JSON.stringify(ctLedger),
    JSON.stringify(ctCIn2),
  ])
);
assert.ok(ctMemberProof);
assert.deepEqual(ctCliMemberProof, ctMemberProof, 'ct-member-prove shared surface');
assert.deepEqual(ctMemberProof!.root, ctRoot, 'ct-member-root shared surface');
assert.equal(
  parseResult<boolean>(
    runHaskell([
      'ct-member-verify',
      ctParamsCase.m.toString(),
      ctParamsCase.n2.toString(),
      ctParamsCase.q.toString(),
      ctParamsCase.beta.toString(),
      JSON.stringify(ctLedger),
      JSON.stringify(ctCIn2),
    ])
  ),
  true,
  'ct-member-verify shared surface'
);
const merkleVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-merkle-vectors.json'), 'utf8')
);
const [merkleLeaf0, merkleLeaf1] = merkleVectors.leaves;
const [merkleEmpty0] = merkleVectors.empty;
const [merkleParent01] = merkleVectors.nodes;
const merkleLedger = [merkleLeaf0.commitment, merkleLeaf1.commitment, merkleLeaf0.commitment];
assert.equal(
  parseResult<string>(runHaskell(['ct-merkle-leaf', JSON.stringify(merkleLeaf0.commitment)])),
  sdk.ConfidentialMerkle.leaf(merkleLeaf0.commitment),
  'ct-merkle-leaf Haskell/TypeScript parity'
);
assert.equal(
  parseResult<string>(runHaskell(['ct-merkle-empty', merkleEmpty0.width.toString()])),
  sdk.ConfidentialMerkle.empty(merkleEmpty0.width),
  'ct-merkle-empty Haskell/TypeScript parity'
);
assert.equal(
  parseResult<string>(runHaskell(['ct-merkle-node', merkleParent01.left, merkleParent01.right])),
  sdk.ConfidentialMerkle.node(merkleParent01.left, merkleParent01.right),
  'ct-merkle-node Haskell/TypeScript parity'
);
assert.equal(
  parseResult<string>(runHaskell(['ct-merkle-root', JSON.stringify(merkleLedger)])),
  sdk.ConfidentialMerkle.root(merkleLedger),
  'ct-merkle-root Haskell/TypeScript parity'
);
const haskellMerkleProof = parseJson<{
  index: number;
  root: string;
  siblings: string[];
  directions: boolean[];
} | null>(runHaskell(['ct-merkle-member-prove', JSON.stringify(merkleLedger), JSON.stringify(merkleLeaf1.commitment)]));
assert.deepEqual(
  haskellMerkleProof,
  sdk.ConfidentialMerkle.membershipProve(merkleLedger, merkleLeaf1.commitment),
  'ct-merkle-member-prove Haskell/TypeScript parity'
);
assert.equal(
  parseResult<boolean>(runHaskell(['ct-merkle-member-verify', JSON.stringify(merkleLedger), JSON.stringify(merkleLeaf1.commitment)])),
  true,
  'ct-merkle-member-verify Haskell accepts generated path'
);
const transactionVectors = JSON.parse(
  fs.readFileSync(path.join(projectRoot, 'tests/fixtures/confidential-transaction-vectors.json'), 'utf8')
);
const [transactionContextVector] = transactionVectors.cases;
const [transactionMerkleProofVector] = transactionVectors.merkleProofCases;
const [transactionEnvelopeVector] = transactionVectors.envelopeCases;
const [transactionAcceptedRootWindowVector] = transactionVectors.acceptedRootWindowCases;
const [transactionWalletProofRequestVector] = transactionVectors.walletProofRequestCases;
const transactionContext = transactionContextVector.context;
assert.equal(
  parseResult<string>(
    runHaskell([
      'ct-transaction-context',
      transactionContext.protocolVersion.toString(),
      transactionContext.networkId,
      transactionContext.assetId.toString(),
      transactionContext.ledgerEpoch.toString(),
      transactionContext.root.digest,
      transactionContext.root.depth.toString(),
      transactionContext.publicFee.toString(),
      JSON.stringify(transactionContext.cIn1),
      JSON.stringify(transactionContext.cIn2),
      JSON.stringify(transactionContext.cOut1),
      JSON.stringify(transactionContext.cOut2),
      JSON.stringify(transactionContext.nf1),
      JSON.stringify(transactionContext.nf2),
    ])
  ),
  sdk.ConfidentialTransaction.transactionContextDigest(transactionContext),
  'ct-transaction-context Haskell/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.transactionContextDigest(transactionContext),
  transactionContextVector.digest,
  'ct-transaction-context vector'
);
const transactionContextArgs = [
  'ct-transaction-context',
  transactionContext.protocolVersion.toString(),
  transactionContext.networkId,
  transactionContext.assetId.toString(),
  transactionContext.ledgerEpoch.toString(),
  transactionContext.root.digest,
  transactionContext.root.depth.toString(),
  transactionContext.publicFee.toString(),
  JSON.stringify(transactionContext.cIn1),
  JSON.stringify(transactionContext.cIn2),
  JSON.stringify(transactionContext.cOut1),
  JSON.stringify(transactionContext.cOut2),
  JSON.stringify(transactionContext.nf1),
  JSON.stringify(transactionContext.nf2),
];
for (const { name, args } of [
  {
    name: 'negative-zero public fee',
    args: transactionContextArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'plus-signed asset id',
    args: transactionContextArgs.map((arg, index) => (index === 3 ? `+${arg}` : arg)),
  },
  {
    name: 'unsafe asset id',
    args: transactionContextArgs.map((arg, index) =>
      index === 3 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'leading-zero input vector element',
    args: transactionContextArgs.map((arg, index) =>
      index === 8 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe input vector element',
    args: transactionContextArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-transaction-context Haskell rejects ${name}`);
}
const haskellWalletProofRequest = transactionWalletProofRequestVector.request;
const haskellWalletProofRequestContext = haskellWalletProofRequest.context;
const haskellWalletProofRequestDigest = parseResult<string>(
  runHaskell([
    'ct-wallet-proof-request-digest',
    haskellWalletProofRequestContext.protocolVersion.toString(),
    haskellWalletProofRequestContext.networkId,
    haskellWalletProofRequestContext.assetId.toString(),
    haskellWalletProofRequestContext.ledgerEpoch.toString(),
    haskellWalletProofRequestContext.root.digest,
    haskellWalletProofRequestContext.root.depth.toString(),
    haskellWalletProofRequestContext.publicFee.toString(),
    JSON.stringify(haskellWalletProofRequestContext.cIn1),
    JSON.stringify(haskellWalletProofRequestContext.cIn2),
    JSON.stringify(haskellWalletProofRequestContext.cOut1),
    JSON.stringify(haskellWalletProofRequestContext.cOut2),
    JSON.stringify(haskellWalletProofRequestContext.nf1),
    JSON.stringify(haskellWalletProofRequestContext.nf2),
    JSON.stringify(haskellWalletProofRequest.acceptedRoots.map((root: any) => root.digest)),
    JSON.stringify(haskellWalletProofRequest.acceptedRoots.map((root: any) => root.depth)),
    JSON.stringify(haskellWalletProofRequest.spentNullifiers),
  ])
);
assert.equal(
  haskellWalletProofRequestDigest,
  sdk.ConfidentialTransaction.transactionWalletProofRequestDigest(haskellWalletProofRequest),
  'ct-wallet-proof-request-digest Haskell/TypeScript parity'
);
assert.equal(
  haskellWalletProofRequestDigest,
  transactionWalletProofRequestVector.digest,
  'ct-wallet-proof-request-digest vector'
);
const haskellAcceptedRootWindow = transactionAcceptedRootWindowVector.window;
function ctAcceptedRootWindowDigestArgs(window: any): string[] {
  return [
    'ct-accepted-root-window-digest',
    window.protocolVersion.toString(),
    window.networkId,
    window.assetId.toString(),
    window.ledgerEpoch.toString(),
    JSON.stringify(window.roots.map((entry: any) => entry.root.digest)),
    JSON.stringify(window.roots.map((entry: any) => entry.root.depth)),
    JSON.stringify(window.roots.map((entry: any) => entry.validFromEpoch)),
    JSON.stringify(window.roots.map((entry: any) => entry.expiresAtEpoch)),
  ];
}
const haskellAcceptedRootWindowDigest = parseResult<string>(
  runHaskell(ctAcceptedRootWindowDigestArgs(haskellAcceptedRootWindow))
);
assert.equal(
  haskellAcceptedRootWindowDigest,
  sdk.ConfidentialTransaction.transactionAcceptedRootWindowDigest(haskellAcceptedRootWindow),
  'ct-accepted-root-window-digest Haskell/TypeScript parity'
);
assert.equal(
  haskellAcceptedRootWindowDigest,
  transactionAcceptedRootWindowVector.digest,
  'ct-accepted-root-window-digest vector'
);
function expectHaskellAcceptedRootWindowRejected(window: any, label: string): void {
  expectHaskellCommandRejected(ctAcceptedRootWindowDigestArgs(window), label);
}
const reversedRootWindow = haskellAcceptedRootWindow.roots.slice().reverse();
const acceptedRootWindowRejectionCases = [
  {
    name: 'empty root window',
    window: { ...haskellAcceptedRootWindow, roots: [] },
  },
  {
    name: 'duplicate root window entry',
    window: {
      ...haskellAcceptedRootWindow,
      roots: [haskellAcceptedRootWindow.roots[0], haskellAcceptedRootWindow.roots[0]],
    },
  },
  ...(reversedRootWindow.map((entry: any) => `${entry.root.digest}:${entry.root.depth}`).join('|') ===
    haskellAcceptedRootWindow.roots.map((entry: any) => `${entry.root.digest}:${entry.root.depth}`).join('|')
    ? []
    : [{
        name: 'unsorted root window',
        window: { ...haskellAcceptedRootWindow, roots: reversedRootWindow },
      }]),
  {
    name: 'future root window entry',
    window: {
      ...haskellAcceptedRootWindow,
      roots: haskellAcceptedRootWindow.roots.map((entry: any, index: number) =>
        index === 0 ? { ...entry, validFromEpoch: haskellAcceptedRootWindow.ledgerEpoch + 1 } : entry
      ),
    },
  },
  {
    name: 'expired root window entry',
    window: {
      ...haskellAcceptedRootWindow,
      roots: haskellAcceptedRootWindow.roots.map((entry: any, index: number) =>
        index === 0 ? { ...entry, expiresAtEpoch: haskellAcceptedRootWindow.ledgerEpoch } : entry
      ),
    },
  },
];
for (const { name, window } of acceptedRootWindowRejectionCases) {
  expectHaskellAcceptedRootWindowRejected(window, `ct-accepted-root-window-digest Haskell rejects ${name}`);
}
const acceptedRootWindowArgs = ctAcceptedRootWindowDigestArgs(haskellAcceptedRootWindow);
for (const { name, args } of [
  {
    name: 'negative-zero ledger epoch',
    args: acceptedRootWindowArgs.map((arg, index) => (index === 4 ? '-0' : arg)),
  },
  {
    name: 'leading-zero root depth',
    args: acceptedRootWindowArgs.map((arg, index) =>
      index === 6 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe expiry epoch',
    args: acceptedRootWindowArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-accepted-root-window-digest Haskell rejects ${name}`);
}
function ctWalletProofRequestDigestArgs(request: any): string[] {
  const context = request.context;
  return [
    'ct-wallet-proof-request-digest',
    context.protocolVersion.toString(),
    context.networkId,
    context.assetId.toString(),
    context.ledgerEpoch.toString(),
    context.root.digest,
    context.root.depth.toString(),
    context.publicFee.toString(),
    JSON.stringify(context.cIn1),
    JSON.stringify(context.cIn2),
    JSON.stringify(context.cOut1),
    JSON.stringify(context.cOut2),
    JSON.stringify(context.nf1),
    JSON.stringify(context.nf2),
    JSON.stringify(request.acceptedRoots.map((root: any) => root.digest)),
    JSON.stringify(request.acceptedRoots.map((root: any) => root.depth)),
    JSON.stringify(request.spentNullifiers),
  ];
}
function expectHaskellWalletProofRequestRejected(request: any, label: string): void {
  expectHaskellCommandRejected(ctWalletProofRequestDigestArgs(request), label);
}
const reversedAcceptedRoots = haskellWalletProofRequest.acceptedRoots.slice().reverse();
const reversedSpentNullifiers = haskellWalletProofRequest.spentNullifiers.slice().reverse();
const walletProofRequestRejectionCases = [
  {
    name: 'empty accepted root window',
    request: { ...haskellWalletProofRequest, acceptedRoots: [] },
  },
  {
    name: 'context root missing from accepted window',
    request: {
      ...haskellWalletProofRequest,
      acceptedRoots: haskellWalletProofRequest.acceptedRoots.filter(
        (root: any) =>
          root.digest !== haskellWalletProofRequest.context.root.digest ||
          root.depth !== haskellWalletProofRequest.context.root.depth
      ),
    },
  },
  {
    name: 'context root depth missing from accepted window',
    request: {
      ...haskellWalletProofRequest,
      acceptedRoots: haskellWalletProofRequest.acceptedRoots
        .map((root: any) =>
          root.digest === haskellWalletProofRequest.context.root.digest &&
          root.depth === haskellWalletProofRequest.context.root.depth
            ? { ...root, depth: root.depth + 1 }
            : root
        )
        .sort((left: any, right: any) =>
          `${left.digest}:${left.depth}`.localeCompare(`${right.digest}:${right.depth}`)
        ),
    },
  },
  {
    name: 'duplicate accepted roots',
    request: {
      ...haskellWalletProofRequest,
      acceptedRoots: [
        haskellWalletProofRequest.context.root,
        haskellWalletProofRequest.context.root,
      ],
    },
  },
  ...(reversedAcceptedRoots.map((root: any) => `${root.digest}:${root.depth}`).join('|') ===
    haskellWalletProofRequest.acceptedRoots.map((root: any) => `${root.digest}:${root.depth}`).join('|')
    ? []
    : [{
        name: 'unsorted accepted roots',
        request: { ...haskellWalletProofRequest, acceptedRoots: reversedAcceptedRoots },
      }]),
  ...(reversedSpentNullifiers.length < 2
    ? []
    : [{
        name: 'unsorted spent nullifiers',
        request: { ...haskellWalletProofRequest, spentNullifiers: reversedSpentNullifiers },
      }]),
  {
    name: 'duplicate spent nullifiers',
    request: {
      ...haskellWalletProofRequest,
      spentNullifiers: [
        haskellWalletProofRequest.spentNullifiers[0],
        haskellWalletProofRequest.spentNullifiers[0],
      ],
    },
  },
  {
    name: 'requested nullifier already spent',
    request: {
      ...haskellWalletProofRequest,
      spentNullifiers: [haskellWalletProofRequest.context.nf1],
    },
  },
  {
    name: 'duplicate requested nullifiers',
    request: {
      ...haskellWalletProofRequest,
      context: {
        ...haskellWalletProofRequest.context,
        nf2: haskellWalletProofRequest.context.nf1,
      },
    },
  },
];
for (const { name, request } of walletProofRequestRejectionCases) {
  expectHaskellWalletProofRequestRejected(
    request,
    `ct-wallet-proof-request-digest Haskell rejects ${name}`
  );
}
const walletProofRequestArgs = ctWalletProofRequestDigestArgs(haskellWalletProofRequest);
for (const { name, args } of [
  {
    name: 'negative-zero public fee',
    args: walletProofRequestArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'leading-zero protocol version',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe protocol version',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical spent-nullifier integer',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 16 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe spent-nullifier integer',
    args: walletProofRequestArgs.map((arg, index) =>
      index === 16 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-wallet-proof-request-digest Haskell rejects ${name}`);
}
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValid, 'function', 'Merkle semantic step export');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValidMerkle, 'function', 'Merkle semantic step explicit export');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValid, 'function', 'Merkle ledger-step export');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValidScaffold, 'function', 'explicit scaffold ledger-step export');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValidScaffold, 'function', 'explicit scaffold semantic-step export');

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
  'transaction scaffold shared surface'
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
      'ct-verify-scaffold',
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
      JSON.stringify(listedCtOut1Range.amountsA),
      JSON.stringify(listedCtOut1Range.amountsZ),
      JSON.stringify(listedCtOut1Range.pairAss),
      JSON.stringify(listedCtOut1Range.pairZss),
      JSON.stringify(listedCtOut2Range.bits),
      JSON.stringify(listedCtOut2Range.comps),
      JSON.stringify(listedCtOut2Range.amountsA),
      JSON.stringify(listedCtOut2Range.amountsZ),
      JSON.stringify(listedCtOut2Range.pairAss),
      JSON.stringify(listedCtOut2Range.pairZss),
    ]);
assert.equal(ctCliAcceptsSdkProof, true, 'ct-verify-scaffold Haskell CLI accepts SDK proofs');

const ctMerkleRoot = sdk.ConfidentialTransaction.merkleLedgerRoot(ctLedger);
const ctMerkleProof = sdk.ConfidentialTransaction.fsProveMerkle(
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
assert.ok(ctMerkleProof);
const ctFee = 1;
const ctFeeOpOut2 = { msg: [0], rand: [0, 0] };
const ctFeeOut2Bits = [
  { msg: [0], rand: [0, 0] },
];
const ctFeeOut2Comps = [
  { msg: [1], rand: [0, 0] },
];
const ctFeeCOut2 = ctCommitOfOpening(ctFeeOpOut2);
const ctFeeMerkleProof = sdk.ConfidentialTransaction.fsProveMerkleWithFee(
  ctParamsExpected,
  ctParamsCase.gamma,
  ctOut1Bits.length,
  ctCk,
  ctNk,
  ctLedger,
  ctSpent,
  ctFee,
  ctCIn1,
  ctCIn2,
  ctCOut1,
  ctFeeCOut2,
  ctNf1,
  ctNf2,
  ctOpIn1,
  ctOpIn2,
  ctOpOut1,
  ctFeeOpOut2,
  ctOut1Bits,
  ctOut1Comps,
  ctFeeOut2Bits,
  ctFeeOut2Comps,
  ctYIn1Rounds,
  ctYIn2Rounds,
  ctYBalance,
  ctYOut1,
  ctYOut1Pairs,
  ctYOut2,
  ctYOut2Pairs
);
assert.ok(ctFeeMerkleProof);
const ctOut1BitValues = ctOut1Bits.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut1BitRands = ctOut1Bits.map((opening: { rand: number[] }) => opening.rand);
const ctOut1CompValues = ctOut1Comps.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut1CompRands = ctOut1Comps.map((opening: { rand: number[] }) => opening.rand);
const ctOut2BitValues = ctOut2Bits.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut2BitRands = ctOut2Bits.map((opening: { rand: number[] }) => opening.rand);
const ctOut2CompValues = ctOut2Comps.map((opening: { msg: number[] }) => opening.msg[0]);
const ctOut2CompRands = ctOut2Comps.map((opening: { rand: number[] }) => opening.rand);
const ctYIn1Msgs = ctYIn1Rounds.map((opening: { msg: number[] }) => opening.msg[0]);
const ctYIn1Rands = ctYIn1Rounds.map((opening: { rand: number[] }) => opening.rand);
const ctYIn2Msgs = ctYIn2Rounds.map((opening: { msg: number[] }) => opening.msg[0]);
const ctYIn2Rands = ctYIn2Rounds.map((opening: { rand: number[] }) => opening.rand);
assert.deepEqual(
  parseJson<unknown>(
    runHaskell([
      'ct-prove-merkle',
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
      ctOpIn1.msg[0].toString(),
      JSON.stringify(ctOpIn1.rand),
      ctOpIn2.msg[0].toString(),
      JSON.stringify(ctOpIn2.rand),
      ctOpOut1.msg[0].toString(),
      JSON.stringify(ctOpOut1.rand),
      ctOpOut2.msg[0].toString(),
      JSON.stringify(ctOpOut2.rand),
      JSON.stringify(ctOut1BitValues),
      JSON.stringify(ctOut1BitRands),
      JSON.stringify(ctOut1CompValues),
      JSON.stringify(ctOut1CompRands),
      JSON.stringify(ctOut2BitValues),
      JSON.stringify(ctOut2BitRands),
      JSON.stringify(ctOut2CompValues),
      JSON.stringify(ctOut2CompRands),
      JSON.stringify(ctYIn1Msgs),
      JSON.stringify(ctYIn1Rands),
      JSON.stringify(ctYIn2Msgs),
      JSON.stringify(ctYIn2Rands),
      JSON.stringify(ctYBalance),
      JSON.stringify(ctYOut1),
      JSON.stringify(ctYOut1Pairs),
      JSON.stringify(ctYOut2),
      JSON.stringify(ctYOut2Pairs),
    ])
  ),
  ctMerkleProof,
  'ct-prove-merkle Haskell/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkle(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctMerkleRoot,
    ctSpent,
    ctCIn1,
    ctCIn2,
    ctCOut1,
    ctCOut2,
    ctNf1,
    ctNf2,
    ctMerkleProof!
  ),
  true,
  'ct-verify-merkle SDK accepts generated proof'
);
const haskellMerkleProofDigest = parseResult<string>(
  runHaskell(['ct-merkle-proof-digest', ...ctMerkleProofDigestArgs(ctMerkleProof!)])
);
assert.equal(
  haskellMerkleProofDigest,
  sdk.ConfidentialTransaction.transactionMerkleProofDigest(ctMerkleProof!),
  'ct-merkle-proof-digest Haskell/TypeScript parity'
);
assert.equal(
  haskellMerkleProofDigest,
  transactionMerkleProofVector.digest,
  'ct-merkle-proof-digest vector'
);
const merkleProofDigestArgs = ['ct-merkle-proof-digest', ...ctMerkleProofDigestArgs(ctMerkleProof!)];
for (const { name, args } of [
  {
    name: 'non-canonical membership index',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe membership index',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical directions vector',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 4 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe directions vector',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 4 ? unsafeFirstInteger(arg) : arg
    ),
  },
  {
    name: 'non-canonical proof matrix integer',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 9 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe proof matrix integer',
    args: merkleProofDigestArgs.map((arg, index) =>
      index === 9 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-merkle-proof-digest Haskell rejects ${name}`);
}
const haskellVectorEnvelopeContext = transactionEnvelopeVector.context;
const haskellVectorEnvelopeDigest = parseResult<string>(
  runHaskell([
    'ct-merkle-envelope-digest',
    transactionEnvelopeVector.contextDigest,
    haskellVectorEnvelopeContext.protocolVersion.toString(),
    haskellVectorEnvelopeContext.networkId,
    haskellVectorEnvelopeContext.assetId.toString(),
    haskellVectorEnvelopeContext.ledgerEpoch.toString(),
    haskellVectorEnvelopeContext.root.digest,
    haskellVectorEnvelopeContext.root.depth.toString(),
    haskellVectorEnvelopeContext.publicFee.toString(),
    JSON.stringify(haskellVectorEnvelopeContext.cIn1),
    JSON.stringify(haskellVectorEnvelopeContext.cIn2),
    JSON.stringify(haskellVectorEnvelopeContext.cOut1),
    JSON.stringify(haskellVectorEnvelopeContext.cOut2),
    JSON.stringify(haskellVectorEnvelopeContext.nf1),
    JSON.stringify(haskellVectorEnvelopeContext.nf2),
    ...ctMerkleProofDigestArgs(ctMerkleProof!),
  ])
);
assert.equal(
  haskellVectorEnvelopeDigest,
  sdk.ConfidentialTransaction.transactionEnvelopeDigest({
    context: haskellVectorEnvelopeContext,
    contextDigest: transactionEnvelopeVector.contextDigest,
    proof: ctMerkleProof!,
  }),
  'ct-merkle-envelope-digest Haskell/TypeScript parity'
);
assert.equal(
  haskellVectorEnvelopeDigest,
  transactionEnvelopeVector.digest,
  'ct-merkle-envelope-digest vector'
);
const merkleEnvelopeDigestArgs = [
  'ct-merkle-envelope-digest',
  transactionEnvelopeVector.contextDigest,
  haskellVectorEnvelopeContext.protocolVersion.toString(),
  haskellVectorEnvelopeContext.networkId,
  haskellVectorEnvelopeContext.assetId.toString(),
  haskellVectorEnvelopeContext.ledgerEpoch.toString(),
  haskellVectorEnvelopeContext.root.digest,
  haskellVectorEnvelopeContext.root.depth.toString(),
  haskellVectorEnvelopeContext.publicFee.toString(),
  JSON.stringify(haskellVectorEnvelopeContext.cIn1),
  JSON.stringify(haskellVectorEnvelopeContext.cIn2),
  JSON.stringify(haskellVectorEnvelopeContext.cOut1),
  JSON.stringify(haskellVectorEnvelopeContext.cOut2),
  JSON.stringify(haskellVectorEnvelopeContext.nf1),
  JSON.stringify(haskellVectorEnvelopeContext.nf2),
  ...ctMerkleProofDigestArgs(ctMerkleProof!),
];
for (const { name, args } of [
  {
    name: 'plus-signed protocol version',
    args: merkleEnvelopeDigestArgs.map((arg, index) => (index === 2 ? `+${arg}` : arg)),
  },
  {
    name: 'negative-zero public fee',
    args: merkleEnvelopeDigestArgs.map((arg, index) => (index === 7 ? '-0' : arg)),
  },
  {
    name: 'unsafe public fee',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 7 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 8 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeDigestArgs.map((arg, index) =>
      index === 8 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-merkle-envelope-digest Haskell rejects ${name}`);
}
assert.equal(
  parseResult<boolean>(
    runHaskell([
      'ct-verify-merkle',
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
      ...ctMerkleProofDigestArgs(ctMerkleProof!),
    ])
  ),
  true,
  'ct-verify-merkle Haskell/TypeScript parity'
);
const merkleVerifyArgs = [
  'ct-verify-merkle',
  ...ctVerifyMerkleArgs(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
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
    ctMerkleProof!
  ),
];
for (const { name, args } of [
  {
    name: 'non-canonical parameter',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 1 ? nonCanonicalIntegerText(arg) : arg
    ),
  },
  {
    name: 'unsafe parameter',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 1 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'plus-signed gamma',
    args: merkleVerifyArgs.map((arg, index) => (index === 5 ? `+${arg}` : arg)),
  },
  {
    name: 'non-canonical key matrix integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 7 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe key matrix integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 7 ? unsafeFirstInteger(arg) : arg
    ),
  },
  {
    name: 'non-canonical public vector integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 11 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe public vector integer',
    args: merkleVerifyArgs.map((arg, index) =>
      index === 11 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-verify-merkle Haskell rejects ${name}`);
}
const haskellEnvelopeContext = {
  protocolVersion: 1,
  networkId: 'isabella-haskell-conformance',
  assetId: 7,
  ledgerEpoch: 42,
  root: {
    digest: ctMerkleRoot,
    depth: ctMerkleProof!.in1Member.siblings.length,
  },
  publicFee: 0,
  cIn1: ctCIn1,
  cIn2: ctCIn2,
  cOut1: ctCOut1,
  cOut2: ctCOut2,
  nf1: ctNf1,
  nf2: ctNf2,
};
const haskellEnvelopePolicy = {
  protocolVersion: haskellEnvelopeContext.protocolVersion,
  networkId: haskellEnvelopeContext.networkId,
  assetId: haskellEnvelopeContext.assetId,
  ledgerEpoch: haskellEnvelopeContext.ledgerEpoch,
  root: haskellEnvelopeContext.root,
  publicFee: 0,
};
const haskellEnvelopeContextDigest = parseResult<string>(
  runHaskell([
    'ct-transaction-context',
    haskellEnvelopeContext.protocolVersion.toString(),
    haskellEnvelopeContext.networkId,
    haskellEnvelopeContext.assetId.toString(),
    haskellEnvelopeContext.ledgerEpoch.toString(),
    haskellEnvelopeContext.root.digest,
    haskellEnvelopeContext.root.depth.toString(),
    haskellEnvelopeContext.publicFee.toString(),
    JSON.stringify(haskellEnvelopeContext.cIn1),
    JSON.stringify(haskellEnvelopeContext.cIn2),
    JSON.stringify(haskellEnvelopeContext.cOut1),
    JSON.stringify(haskellEnvelopeContext.cOut2),
    JSON.stringify(haskellEnvelopeContext.nf1),
    JSON.stringify(haskellEnvelopeContext.nf2),
  ])
);
assert.equal(
  haskellEnvelopeContextDigest,
  sdk.ConfidentialTransaction.transactionContextDigest(haskellEnvelopeContext),
  'ct-merkle-envelope context digest Haskell/TypeScript parity'
);
const haskellEnvelope = {
  context: haskellEnvelopeContext,
  contextDigest: haskellEnvelopeContextDigest,
  proof: ctMerkleProof!,
};
const runHaskellEnvelope = (
  policy: typeof haskellEnvelopePolicy,
  contextDigest: string,
  context: typeof haskellEnvelopeContext,
  proof: typeof ctMerkleProof,
  spentOverride = ctSpent
) =>
  parseResult<boolean>(
    runHaskell([
      'ct-verify-merkle-envelope',
      ...ctVerifyMerkleEnvelopeArgs(
        ctParamsCase.m,
        ctParamsCase.n2,
        ctParamsCase.q,
        ctParamsCase.beta,
        ctParamsCase.gamma,
        ctOut1Bits.length,
        ctCk,
        ctNk,
        ctLedger,
        spentOverride,
        policy,
        contextDigest,
        context,
        proof!
      ),
    ])
  );
assert.equal(
  runHaskellEnvelope(
    haskellEnvelopePolicy,
    haskellEnvelopeContextDigest,
    haskellEnvelopeContext,
    ctMerkleProof
  ),
  true,
  'ct-verify-merkle-envelope Haskell accepts native context digest and Merkle proof'
);
const merkleEnvelopeVerifyArgs = [
  'ct-verify-merkle-envelope',
  ...ctVerifyMerkleEnvelopeArgs(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctLedger,
    ctSpent,
    haskellEnvelopePolicy,
    haskellEnvelopeContextDigest,
    haskellEnvelopeContext,
    ctMerkleProof!
  ),
];
for (const { name, args } of [
  {
    name: 'non-canonical expected public fee',
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 17 ? '-0' : arg)),
  },
  {
    name: 'unsafe expected public fee',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 17 ? unsafeProtocolInteger : arg
    ),
  },
  {
    name: 'plus-signed context protocol version',
    args: merkleEnvelopeVerifyArgs.map((arg, index) => (index === 19 ? `+${arg}` : arg)),
  },
  {
    name: 'non-canonical context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 26 ? nonCanonicalFirstInteger(arg) : arg
    ),
  },
  {
    name: 'unsafe context vector integer',
    args: merkleEnvelopeVerifyArgs.map((arg, index) =>
      index === 26 ? unsafeFirstInteger(arg) : arg
    ),
  },
]) {
  expectHaskellCommandRejected(args, `ct-verify-merkle-envelope Haskell rejects ${name}`);
}
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    haskellEnvelope,
    haskellEnvelopePolicy
  ),
  true,
  'ct-merkle-envelope accepts Haskell context digest and Merkle proof'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    { ...haskellEnvelope, contextDigest: haskellEnvelopeContextDigest.replace(/^./, '0') },
    haskellEnvelopePolicy
  ),
  false,
  'ct-merkle-envelope rejects stale Haskell context digest'
);
assert.equal(
  runHaskellEnvelope(
    haskellEnvelopePolicy,
    haskellEnvelopeContextDigest.replace(/^./, '0'),
    haskellEnvelopeContext,
    ctMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects stale context digest'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    haskellEnvelope,
    { ...haskellEnvelopePolicy, assetId: haskellEnvelopePolicy.assetId + 1 }
  ),
  false,
  'ct-merkle-envelope rejects wrong verifier policy'
);
assert.equal(
  runHaskellEnvelope(
    { ...haskellEnvelopePolicy, assetId: haskellEnvelopePolicy.assetId + 1 },
    haskellEnvelopeContextDigest,
    haskellEnvelopeContext,
    ctMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects wrong verifier policy'
);
const haskellFeeEnvelopeContext = {
  ...haskellEnvelopeContext,
  publicFee: ctFee,
  cOut2: ctFeeCOut2,
};
const haskellFeeEnvelopeContextDigest = parseResult<string>(
  runHaskell([
    'ct-transaction-context',
    haskellFeeEnvelopeContext.protocolVersion.toString(),
    haskellFeeEnvelopeContext.networkId,
    haskellFeeEnvelopeContext.assetId.toString(),
    haskellFeeEnvelopeContext.ledgerEpoch.toString(),
    haskellFeeEnvelopeContext.root.digest,
    haskellFeeEnvelopeContext.root.depth.toString(),
    haskellFeeEnvelopeContext.publicFee.toString(),
    JSON.stringify(haskellFeeEnvelopeContext.cIn1),
    JSON.stringify(haskellFeeEnvelopeContext.cIn2),
    JSON.stringify(haskellFeeEnvelopeContext.cOut1),
    JSON.stringify(haskellFeeEnvelopeContext.cOut2),
    JSON.stringify(haskellFeeEnvelopeContext.nf1),
    JSON.stringify(haskellFeeEnvelopeContext.nf2),
  ])
);
assert.equal(
  haskellFeeEnvelopeContextDigest,
  sdk.ConfidentialTransaction.transactionContextDigest(haskellFeeEnvelopeContext),
  'ct-merkle-envelope fee context digest Haskell/TypeScript parity'
);
assert.equal(
  sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
    ctParamsExpected,
    ctParamsCase.gamma,
    ctOut1Bits.length,
    ctCk,
    ctNk,
    ctSpent,
    {
      context: haskellFeeEnvelopeContext,
      contextDigest: haskellFeeEnvelopeContextDigest,
      proof: ctFeeMerkleProof!,
    },
    { ...haskellEnvelopePolicy, publicFee: ctFee }
  ),
  true,
  'ct-merkle-envelope accepts fee-aware public-fee proof'
);
assert.equal(
  runHaskellEnvelope(
    { ...haskellEnvelopePolicy, publicFee: ctFee },
    haskellFeeEnvelopeContextDigest,
    haskellFeeEnvelopeContext,
    ctFeeMerkleProof
  ),
  true,
  'ct-verify-merkle-envelope Haskell accepts fee-aware public-fee proof'
);
assert.equal(
  runHaskellEnvelope(
    haskellEnvelopePolicy,
    haskellFeeEnvelopeContextDigest,
    haskellFeeEnvelopeContext,
    ctFeeMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects mismatched fee policy'
);
assert.equal(
  runHaskellEnvelope(
    {
      ...haskellEnvelopePolicy,
      root: { ...haskellEnvelopePolicy.root, depth: haskellEnvelopePolicy.root.depth + 1 },
    },
    haskellEnvelopeContextDigest,
    haskellEnvelopeContext,
    ctMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects wrong verifier root depth'
);
const haskellWrongDepthContext = {
  ...haskellEnvelopeContext,
  root: { ...haskellEnvelopeContext.root, depth: haskellEnvelopeContext.root.depth + 1 },
};
const haskellWrongDepthDigest = parseResult<string>(
  runHaskell([
    'ct-transaction-context',
    haskellWrongDepthContext.protocolVersion.toString(),
    haskellWrongDepthContext.networkId,
    haskellWrongDepthContext.assetId.toString(),
    haskellWrongDepthContext.ledgerEpoch.toString(),
    haskellWrongDepthContext.root.digest,
    haskellWrongDepthContext.root.depth.toString(),
    haskellWrongDepthContext.publicFee.toString(),
    JSON.stringify(haskellWrongDepthContext.cIn1),
    JSON.stringify(haskellWrongDepthContext.cIn2),
    JSON.stringify(haskellWrongDepthContext.cOut1),
    JSON.stringify(haskellWrongDepthContext.cOut2),
    JSON.stringify(haskellWrongDepthContext.nf1),
    JSON.stringify(haskellWrongDepthContext.nf2),
  ])
);
assert.equal(
  runHaskellEnvelope(
    { ...haskellEnvelopePolicy, root: haskellWrongDepthContext.root },
    haskellWrongDepthDigest,
    haskellWrongDepthContext,
    ctMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects context root depth not matched by the Merkle proof'
);
const haskellWrongRootContext = {
  ...haskellEnvelopeContext,
  root: {
    ...haskellEnvelopeContext.root,
    digest: haskellEnvelopeContext.root.digest.replace(
      /^./,
      haskellEnvelopeContext.root.digest[0] === '0' ? '1' : '0'
    ),
  },
};
const haskellWrongRootDigest = parseResult<string>(
  runHaskell([
    'ct-transaction-context',
    haskellWrongRootContext.protocolVersion.toString(),
    haskellWrongRootContext.networkId,
    haskellWrongRootContext.assetId.toString(),
    haskellWrongRootContext.ledgerEpoch.toString(),
    haskellWrongRootContext.root.digest,
    haskellWrongRootContext.root.depth.toString(),
    haskellWrongRootContext.publicFee.toString(),
    JSON.stringify(haskellWrongRootContext.cIn1),
    JSON.stringify(haskellWrongRootContext.cIn2),
    JSON.stringify(haskellWrongRootContext.cOut1),
    JSON.stringify(haskellWrongRootContext.cOut2),
    JSON.stringify(haskellWrongRootContext.nf1),
    JSON.stringify(haskellWrongRootContext.nf2),
  ])
);
assert.equal(
  runHaskellEnvelope(
    { ...haskellEnvelopePolicy, root: haskellWrongRootContext.root },
    haskellWrongRootDigest,
    haskellWrongRootContext,
    ctMerkleProof
  ),
  false,
  'ct-verify-merkle-envelope Haskell rejects context roots not matched by the Merkle proof'
);
for (const mutation of merkleTransactionProofMutations(
  ctMerkleProof!,
  ctSpent,
  haskellEnvelopeContext.root.digest,
  ctNf1
)) {
  const mutatedContext =
    mutation.root === haskellEnvelopeContext.root.digest
      ? haskellEnvelopeContext
      : {
          ...haskellEnvelopeContext,
          root: { ...haskellEnvelopeContext.root, digest: mutation.root },
        };
  const mutatedPolicy =
    mutation.root === haskellEnvelopePolicy.root.digest
      ? haskellEnvelopePolicy
      : {
          ...haskellEnvelopePolicy,
          root: { ...haskellEnvelopePolicy.root, digest: mutation.root },
        };
  const mutatedContextDigest =
    mutatedContext === haskellEnvelopeContext
      ? haskellEnvelopeContextDigest
      : parseResult<string>(
          runHaskell([
            'ct-transaction-context',
            mutatedContext.protocolVersion.toString(),
            mutatedContext.networkId,
            mutatedContext.assetId.toString(),
            mutatedContext.ledgerEpoch.toString(),
            mutatedContext.root.digest,
            mutatedContext.root.depth.toString(),
            mutatedContext.publicFee.toString(),
            JSON.stringify(mutatedContext.cIn1),
            JSON.stringify(mutatedContext.cIn2),
            JSON.stringify(mutatedContext.cOut1),
            JSON.stringify(mutatedContext.cOut2),
            JSON.stringify(mutatedContext.nf1),
            JSON.stringify(mutatedContext.nf2),
          ])
        );
  assert.equal(
    sdk.ConfidentialTransaction.fsVerifyMerkleEnvelope(
      ctParamsExpected,
      ctParamsCase.gamma,
      ctOut1Bits.length,
      ctCk,
      ctNk,
      mutation.spent,
      {
        context: mutatedContext,
        contextDigest: mutatedContextDigest,
        proof: mutation.proof,
      },
      mutatedPolicy
    ),
    false,
    `ct-merkle-envelope rejects mutated proof case ${mutation.name}`
  );
  assert.equal(
    runHaskellEnvelope(
      mutatedPolicy,
      mutatedContextDigest,
      mutatedContext,
      mutation.proof,
      mutation.spent
    ),
    false,
    `ct-verify-merkle-envelope Haskell rejects mutated proof case ${mutation.name}`
  );
}

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
  'Validated Haskell CLI and SDK surfaces on deterministic shared-surface cases plus native accepted-root-window and wallet-request digest/rejection parity, native non-canonical/out-of-range transaction encoding rejection, expanded Merkle envelope mutation rejection including membership index/path and root-depth mismatches, and randomized sampler bound checks.'
);
