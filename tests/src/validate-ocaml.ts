import assert from 'node:assert/strict';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

import {
  balanceProofShape,
  cbBalanceCommitment,
  cbCanonicalChallenge,
  cbParams,
  cbProve,
  cbRandCommit,
  cbRandCommitKey,
  cbSigmaCommit,
  cbSigmaRespond,
  cbSigmaVerify,
  cbValidMask,
  cbValidParams,
  cbValidResponse,
  cbValidWitness,
  cbVerify,
  ctMemberProve,
  ctMemberVerify,
  ctNullifier,
  ctNullifierProve,
  ctNullifierVerify,
  ctProve,
  ctVerify,
  crAmountCommitment,
  crProve,
  rangeProofShape,
  crVerify,
  nullifierProofShape,
  dilCheckBound,
  dilDecompose,
  dilHighbits,
  dilHintWeight,
  dilLowbits,
  dilMakeHint,
  dilModCentered,
  dilParams,
  dilPower2Round,
  dilUseHint,
  parseCliResult,
  runCli,
} from './isabella-cli.ts';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = process.env.ISABELLA_PROJECT_ROOT
  ? path.resolve(process.env.ISABELLA_PROJECT_ROOT)
  : path.join(__dirname, '..', '..');
const typeScriptEntry = process.env.ISABELLA_TS_ENTRY
  ? path.resolve(process.env.ISABELLA_TS_ENTRY)
  : path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');

function ensureFileExists(filePath: string, hint: string): void {
  if (!fs.existsSync(filePath)) {
    throw new Error(`${filePath} is missing. ${hint}`);
  }
}

async function loadSdk() {
  ensureFileExists(typeScriptEntry, 'Run `make typescript` before validating the SDKs.');
  return import(pathToFileURL(typeScriptEntry).href);
}

const sdk = await loadSdk();
const trace = process.env.ISABELLA_VALIDATE_TRACE === '1';

function logProgress(message: string): void {
  if (trace) {
    console.log(message);
  }
}

const modCenteredCases = [
  { x: 7, q: 5 },
  { x: 8, q: 5 },
  { x: -3, q: 5 },
  { x: 130, q: 256 },
];

for (const { x, q } of modCenteredCases) {
  const actual = parseCliResult<{ result: number }>(runCli(['mod-centered', x.toString(), q.toString()])).result;
  assert.equal(actual, sdk.Zq.modCentered(x, q), `mod-centered(${x}, ${q})`);
}

const distCases = [
  { q: 17, x: 0 },
  { q: 17, x: 9 },
  { q: 256, x: 130 },
];

for (const { q, x } of distCases) {
  const actual = parseCliResult<{ result: number }>(runCli(['dist0', q.toString(), x.toString()])).result;
  assert.equal(actual, sdk.Zq.dist0(q, x), `dist0(${q}, ${x})`);
}

for (const q of [17, 97, 256]) {
  for (const bit of [false, true]) {
    const encoded = parseCliResult<{ result: number }>(runCli(['encode-bit', q.toString(), bit ? '1' : '0'])).result;
    assert.equal(encoded, sdk.Zq.encodeBit(q, bit), `encode-bit(${q}, ${bit})`);

    const decoded = parseCliResult<{ result: boolean }>(runCli(['decode-bit', q.toString(), encoded.toString()])).result;
    assert.equal(decoded, sdk.Zq.decodeBit(q, encoded), `decode-bit(${q}, ${encoded})`);
  }
}

const dotCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [2, -1, 5], right: [3, 0, -2] },
];

for (const { left, right } of dotCases) {
  const actual = parseCliResult<{ result: number }>(
    runCli(['inner-prod', JSON.stringify(left), JSON.stringify(right)])
  ).result;
  assert.equal(actual, sdk.Vec.dot(left, right), `inner-prod(${left}, ${right})`);
}

const addCases = [
  { left: [1, 2, 3], right: [4, 5, 6] },
  { left: [0, -2, 9], right: [7, 3, -1] },
];

for (const { left, right } of addCases) {
  const actual = parseCliResult<{ result: number[] }>(
    runCli(['vec-add', JSON.stringify(left), JSON.stringify(right)])
  ).result;
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
  const actual = parseCliResult<{ result: number[][] }>(
    runCli(['transpose', JSON.stringify(matrix)])
  ).result;
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

const matrixActual = parseCliResult<{ result: number[] }>(
  runCli([
    'mat-vec-mult',
    JSON.stringify(matrixCase.matrix),
    JSON.stringify(matrixCase.vector),
    matrixCase.q.toString(),
  ])
).result;
assert.deepEqual(
  matrixActual,
  sdk.Zq.matVecMultMod(matrixCase.matrix, matrixCase.vector, matrixCase.q),
  'mat-vec-mult shared surface'
);

for (const variant of ['44', '65', '87'] as const) {
  assert.deepEqual(dilParams(variant), sdk.Dilithium.params(variant), `dil-params(${variant})`);
}

const dilithiumModCases = [
  { r: 8, m: 16 },
  { r: 9, m: 16 },
  { r: -3, m: 16 },
  { r: 1234567, m: 190464 },
];

for (const { r, m } of dilithiumModCases) {
  assert.equal(dilModCentered(r, m), sdk.Dilithium.modCentered(r, m), `dil-mod-centered(${r}, ${m})`);
}

const power2RoundCases = [
  { r: 0, d: 13 },
  { r: 100000, d: 13 },
  { r: 1234567, d: 13 },
];

for (const { r, d } of power2RoundCases) {
  const expected = dilPower2Round(r, d);
  assert.deepEqual(
    sdk.Dilithium.power2Round(r, d),
    { r1: expected.r1, r0: expected.r0 },
    `dil-power2round(${r}, ${d})`
  );
}

const alpha44 = 2 * sdk.Dilithium.params('44').gamma2;
const decomposeCases = [0, 1000, 100000, 500000, 1234567, sdk.Dilithium.params('44').q - 1];

for (const r of decomposeCases) {
  const expected = dilDecompose(r, alpha44);
  const actual = sdk.Dilithium.decompose(r, alpha44);
  assert.deepEqual(actual, { r1: expected.r1, r0: expected.r0 }, `dil-decompose(${r}, ${alpha44})`);
  assert.equal(sdk.Dilithium.highBits(r, alpha44), dilHighbits(r, alpha44), `dil-highbits(${r}, ${alpha44})`);
  assert.equal(sdk.Dilithium.lowBits(r, alpha44), dilLowbits(r, alpha44), `dil-lowbits(${r}, ${alpha44})`);
}

const hintCases = [
  { z: 0, r: 100000, alpha: alpha44 },
  { z: 2000, r: 100000, alpha: alpha44 },
  { z: -5000, r: 765432, alpha: alpha44 },
];

for (const { z, r, alpha } of hintCases) {
  const expectedHint = dilMakeHint(z, r, alpha);
  assert.equal(sdk.Dilithium.makeHint(z, r, alpha), expectedHint, `dil-makehint(${z}, ${r}, ${alpha})`);
  assert.equal(
    sdk.Dilithium.useHint(expectedHint, r, alpha),
    dilUseHint(expectedHint, r, alpha),
    `dil-usehint(${expectedHint}, ${r}, ${alpha})`
  );
}

const boundCases = [
  { value: 77, bound: 78 },
  { value: 78, bound: 78 },
  { value: -120, bound: 121 },
];

for (const { value, bound } of boundCases) {
  assert.equal(
    sdk.Dilithium.checkBound(value, bound),
    dilCheckBound(value, bound),
    `dil-check-bound(${value}, ${bound})`
  );
}

const hints = [
  [1, 0, 1],
  [0, 1, 0],
  [1, 1],
];
assert.equal(sdk.Dilithium.hintWeight(hints), dilHintWeight(hints), 'dil-hint-weight shared surface');

console.log('validate-ocaml: base arithmetic, linear algebra, and Dilithium shared surfaces passed');

const cbParamsCase = { m: 2, n2: 2, q: 17, beta: 3, gamma: 5 };
const cbKey = [
  [1, 0, 0],
  [0, 1, 0],
];
const cbWitness = [1, 2];
const cbMask = [0, 1];
const cbMasks = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => cbMask);
const cbCommitment = sdk.ConfidentialBalance.randCommit(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbKey,
  cbWitness
);

assert.deepEqual(
  cbParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  'cb-params shared surface'
);
assert.equal(
  cbValidParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  sdk.ConfidentialBalance.validScalarParams(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta)
  ),
  'cb-valid-params shared surface'
);
assert.deepEqual(
  cbRandCommitKey(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey),
  sdk.ConfidentialBalance.randCommitKey(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey
  ),
  'cb-rand-commit-key shared surface'
);
assert.deepEqual(
  cbRandCommit(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey, cbWitness),
  cbCommitment,
  'cb-rand-commit shared surface'
);
assert.equal(
  cbValidWitness(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbWitness),
  sdk.ConfidentialBalance.validWitness(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbWitness
  ),
  'cb-valid-witness shared surface'
);
assert.equal(
  cbValidMask(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbParamsCase.gamma, cbMask),
  sdk.ConfidentialBalance.validMask(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbMask
  ),
  'cb-valid-mask shared surface'
);
const cbExpectedChallenge = sdk.ConfidentialBalance.canonicalChallenge(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbKey,
  cbCommitment,
  sdk.ConfidentialBalance.sigmaCommit(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey,
    cbMask
  )
);
const cbSigmaA = cbSigmaCommit(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta, cbKey, cbMask);
const cbSigmaZ = cbSigmaRespond(cbWitness, cbMask, cbExpectedChallenge);
assert.equal(
  cbValidResponse(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  sdk.ConfidentialBalance.validResponse(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  'cb-valid-response shared surface'
);
assert.deepEqual(
  cbBalanceCommitment([8, 3], [4, 6], [5, 1], [7, 2], cbParamsCase.q),
  sdk.ConfidentialBalance.balanceCommitment([8, 3], [4, 6], [5, 1], [7, 2], cbParamsCase.q),
  'cb-balance-commitment shared surface'
);
assert.equal(
  cbCanonicalChallenge(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbKey,
    cbCommitment,
    cbSigmaA
  ),
  cbExpectedChallenge,
  'cb-canonical-challenge shared surface'
);
assert.deepEqual(
  cbSigmaA,
  sdk.ConfidentialBalance.sigmaCommit(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbKey,
    cbMask
  ),
  'cb-sigma-commit shared surface'
);
assert.deepEqual(
  cbSigmaZ,
  sdk.ConfidentialBalance.sigmaRespond(cbWitness, cbMask, cbExpectedChallenge),
  'cb-sigma-respond shared surface'
);
assert.equal(
  cbSigmaVerify(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbSigmaA,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  sdk.ConfidentialBalance.sigmaVerify(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbSigmaA,
    cbExpectedChallenge,
    cbSigmaZ
  ),
  'cb-sigma-verify shared surface'
);
const cbProof = cbProve(
  cbParamsCase.m,
  cbParamsCase.n2,
  cbParamsCase.q,
  cbParamsCase.beta,
  cbParamsCase.gamma,
  cbKey,
  cbCommitment,
  cbWitness,
  cbMasks
);
const cbSdkProof = sdk.ConfidentialBalance.fsProve(
  sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
  cbParamsCase.gamma,
  cbKey,
  cbCommitment,
  cbWitness,
  cbMasks
);
assert.deepEqual(
  cbProof,
  cbSdkProof,
  'cb-prove shared surface'
);
assert.equal(balanceProofShape(cbProof!), balanceProofShape(cbSdkProof!), 'cb-proof-shape shared surface');
assert.equal(
  cbVerify(
    cbParamsCase.m,
    cbParamsCase.n2,
    cbParamsCase.q,
    cbParamsCase.beta,
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbProof!
  ),
  sdk.ConfidentialBalance.fsVerify(
    sdk.ConfidentialBalance.makeParams(cbParamsCase.m, cbParamsCase.n2, cbParamsCase.q, cbParamsCase.beta),
    cbParamsCase.gamma,
    cbKey,
    cbCommitment,
    cbProof!
  ),
  'cb-verify shared surface'
);

console.log('validate-ocaml: confidential balance shared surface passed');

const runFullConfidentialEquivalence =
  process.env.ISABELLA_SDK_EQUIV_FULL === '1' || sdk.ConfidentialBalance.fsRounds() <= 32;
if (!runFullConfidentialEquivalence) {
  console.log(
    `validate-ocaml: skipping range/transaction equivalence for ${sdk.ConfidentialBalance.fsRounds()} FS rounds; set ISABELLA_SDK_EQUIV_FULL=1 to run it`
  );
  process.exit(0);
}

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
  crAmountCommitment(
    crParamsCase.m,
    crParamsCase.n2,
    crParamsCase.q,
    crParamsCase.beta,
    crKey,
    crAmountCommit,
    crBitCommitments
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
assert.equal(
  crVerify(
    crParamsCase.m,
    crParamsCase.n2,
    crParamsCase.q,
    crParamsCase.beta,
    crParamsCase.gamma,
    crRangeK,
    crKey,
    crAmountCommit,
    crProof!
  ),
  true,
  'cr-verify CLI accepts SDK range proofs'
);
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

console.log('validate-ocaml: confidential range shared surface passed');

const ctParamsCase = { m: 2, n2: 2, q: 17, beta: 6, gamma: 5 };
logProgress('validate-ocaml: entering confidential transaction shared surface');
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
  ctNullifier(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctNk,
    ctOpIn1.msg[0],
    ctOpIn1.rand
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
logProgress('validate-ocaml: nullifier proof checks passed');
assert.equal(
  ctNullifierVerify(
    ctParamsCase.m,
    ctParamsCase.n2,
    ctParamsCase.q,
    ctParamsCase.beta,
    ctParamsCase.gamma,
    ctCk,
    ctNk,
    ctCIn1,
    ctNf1,
    ctNullifierProof!
  ),
  true,
  'ct-nullifier-verify CLI accepts SDK proofs'
);
const ctRoot = sdk.ConfidentialTransaction.ledgerRoot(ctParamsExpected, ctLedger);
const ctMemberProof = ctMemberProve(ctParamsExpected, ctLedger, ctCIn2);
assert.deepEqual(
  ctMemberProof,
  sdk.ConfidentialTransaction.membershipProve(ctParamsExpected, ctLedger, ctCIn2),
  'ct-member-prove shared surface'
);
assert.equal(
  ctMemberVerify(ctParamsExpected, ctCIn2, ctMemberProof!),
  sdk.ConfidentialTransaction.membershipVerify(ctParamsExpected, ctCIn2, ctMemberProof!),
  'ct-member-verify shared surface'
);
logProgress('validate-ocaml: membership checks passed');
assert.equal(typeof sdk.ConfidentialTransaction.semanticStepValid, 'function', 'ct-ledger-step alias exported');
assert.equal(typeof sdk.ConfidentialTransaction.ledgerStepValid, 'function', 'ct-ledger-step compatibility export');

console.log('validate-ocaml: confidential nullifier and membership shared surfaces passed');

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
logProgress('validate-ocaml: transaction proof constructed');
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
logProgress('validate-ocaml: transaction verification passed');

console.log('validate-ocaml: confidential transaction proof verification passed');

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
logProgress('validate-ocaml: verified input notes constructed');

console.log('validate-ocaml: confidential transaction shared surface passed');

console.log('Validated the TypeScript SDK against the OCaml surface on 67 deterministic shared-surface cases.');
