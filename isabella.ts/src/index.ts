/**
 * Isabella - Formally Verified Lattice Cryptography
 *
 * This library provides lattice-based cryptographic primitives that have been
 * formally verified in Isabelle/HOL. All functions are extracted from proven-correct
 * specifications and compiled to JavaScript via js_of_ocaml.
 *
 * @packageDocumentation
 *
 * Provenance: Wrapper over js_of_ocaml output generated from
 * Isabelle-exported OCaml Canon modules only.
 */

import { createHash, randomInt } from 'node:crypto';

// Load the js_of_ocaml runtime (sets globalThis.Isabella)
// This import is handled by the runtime loader
import './runtime.cjs';

/** Integer vector type */
export type IntVec = number[];

/** Integer matrix type (list of rows) */
export type IntMatrix = number[][];

/** Supported ML-DSA parameter sets */
export type DilithiumVariant = '44' | '65' | '87';

/** FIPS 204 ML-DSA parameter record */
export interface DilithiumParams {
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
}

/** Result of Power2Round or Decompose on a single coefficient */
export interface DilithiumSplit {
  r1: number;
  r0: number;
}

/** Scalar commitment parameters for the confidential-balance proof slice */
export interface ScalarCommitParams {
  n1: number;
  n2: number;
  m: number;
  q: number;
  beta: number;
}

/** Opening for a scalar commitment */
export interface CommitOpening {
  msg: IntVec;
  rand: IntVec;
}

/** Deterministic Fiat-Shamir proof object for confidential balance */
export interface BalanceProof {
  as: IntMatrix;
  zs: IntMatrix;
}

/** Arbitrary-precision integer vector for widened confidential parameters */
export type BigIntVec = bigint[];

/** Arbitrary-precision integer matrix for widened confidential parameters */
export type BigIntMatrix = bigint[][];

/** Input vector accepted by widened BigInt reference helpers */
export type BigIntVecInput = readonly ConfidentialBigIntInput[];

/** Input matrix accepted by widened BigInt reference helpers */
export type BigIntMatrixInput = readonly BigIntVecInput[];

/** BigInt scalar commitment parameters for widened confidential-balance checks */
export interface BigIntScalarCommitParams {
  n1: number;
  n2: number;
  m: number;
  q: bigint;
  beta: bigint;
}

/** BigInt Fiat-Shamir proof object for confidential balance */
export interface BigIntBalanceProof {
  as: BigIntMatrix;
  zs: BigIntMatrix;
}

/** Input form accepted by bignum transaction digest helpers for balance proofs */
export interface BigIntBalanceProofInput {
  as: BigIntMatrixInput;
  zs: BigIntMatrixInput;
}

/** BigInt SIS commitment opening for widened reference helpers */
export interface BigIntCommitOpening {
  msg: BigIntVec;
  rand: BigIntVec;
}

/** BigInt Fiat-Shamir proof object for confidential range */
export interface BigIntRangeProof {
  bits: BigIntMatrix;
  comps: BigIntMatrix;
  amountAs: BigIntMatrix;
  amountZs: BigIntMatrix;
  pairAss: BigIntMatrix[];
  pairZss: BigIntMatrix[];
}

/** Input form accepted by bignum transaction digest helpers for range proofs */
export interface BigIntRangeProofInput {
  bits: BigIntMatrixInput;
  comps: BigIntMatrixInput;
  amountAs: BigIntMatrixInput;
  amountZs: BigIntMatrixInput;
  pairAss: readonly BigIntMatrixInput[];
  pairZss: readonly BigIntMatrixInput[];
}

/** BigInt Fiat-Shamir proof object for confidential nullifiers */
export interface BigIntNullifierProof {
  aCommits: BigIntMatrix;
  aNullifiers: BigIntMatrix;
  zMsgs: BigIntMatrix;
  zRands: BigIntMatrix;
}

/** Input form accepted by bignum transaction digest helpers for nullifier proofs */
export interface BigIntNullifierProofInput {
  aCommits: BigIntMatrixInput;
  aNullifiers: BigIntMatrixInput;
  zMsgs: BigIntMatrixInput;
  zRands: BigIntMatrixInput;
}

/** Deterministic Fiat-Shamir proof object for confidential range */
export interface RangeProof {
  bits: IntMatrix;
  comps: IntMatrix;
  amountA: IntVec;
  amountZ: IntVec;
  pairAs: IntMatrix;
  pairZs: IntMatrix;
}

/** One repeated-round transcript for the confidential-range proof slice */
export interface RangeRound {
  amountA: IntVec;
  amountZ: IntVec;
  pairAs: IntMatrix;
  pairZs: IntMatrix;
  challenge?: boolean | number;
}

/** JSON-friendly repeated-round confidential-range proof */
export interface RepeatedRangeProof {
  bits: IntMatrix;
  comps: IntMatrix;
  rounds: RangeRound[];
}

/** JSON-friendly list form of the repeated confidential-range proof */
export interface ListedRangeProof {
  bits: IntMatrix;
  comps: IntMatrix;
  amountAs: IntMatrix;
  amountZs: IntMatrix;
  pairAss: IntMatrix[];
  pairZss: IntMatrix[];
  challenges?: Array<boolean | number>;
}

/** Confidential-range proof, legacy or repeated */
export type RangeProofLike = RangeProof | RepeatedRangeProof | ListedRangeProof;

/** Deterministic Fiat-Shamir proof object for note nullification */
export interface NullifierProof {
  aCommit: IntVec;
  aNullifier: IntVec;
  zMsg: IntVec;
  zRand: IntVec;
}

/** One repeated-round transcript for the nullifier proof slice */
export interface NullifierRound {
  aCommit: IntVec;
  aNullifier: IntVec;
  zMsg: IntVec;
  zRand: IntVec;
  challenge?: boolean | number;
}

/** JSON-friendly repeated-round nullifier proof */
export interface RepeatedNullifierProof {
  rounds: NullifierRound[];
}

/** JSON-friendly list form of the repeated nullifier proof */
export interface ListedNullifierProof {
  aCommits: IntMatrix;
  aNullifiers: IntMatrix;
  zMsgs: IntMatrix;
  zRands: IntMatrix;
  challenges?: Array<boolean | number>;
}

/** Nullifier proof, legacy or repeated */
export type NullifierProofLike =
  | NullifierProof
  | RepeatedNullifierProof
  | ListedNullifierProof;

/** Deterministic proof that a commitment appears at a ledger position */
export interface MembershipProof {
  index: number;
  root: IntVec;
  siblings: IntMatrix;
  directions: boolean[];
}

/** Hex-encoded SHA3-256 Merkle digest */
export type MerkleDigest = string;

/** Accepted Merkle root bound to its tree depth */
export interface MerkleAcceptedRoot {
  digest: MerkleDigest;
  depth: number;
}

/** Consensus/indexer accepted-root entry with an exclusive expiry epoch */
export interface ConfidentialAcceptedRootWindowEntry {
  root: MerkleAcceptedRoot;
  validFromEpoch: number;
  expiresAtEpoch: number;
}

/** Depth-tagged root window that is live for one ledger epoch */
export interface ConfidentialAcceptedRootWindow {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  roots: ConfidentialAcceptedRootWindowEntry[];
}

/** Cryptographic Merkle membership proof over note commitment leaves */
export interface MerkleMembershipProof {
  index: number;
  root: MerkleDigest;
  siblings: MerkleDigest[];
  directions: boolean[];
}

/** Range-verified note tracked by the confidential ledger model */
export interface VerifiedNote {
  commitment: IntVec;
  rangeProof: RangeProofLike;
}

/** Deterministic Fiat-Shamir proof object for a 2-in/2-out confidential transfer */
export interface TransactionProof {
  in1Member: MembershipProof;
  in2Member: MembershipProof;
  in1Nullifier: NullifierProofLike;
  in2Nullifier: NullifierProofLike;
  balance: BalanceProof;
  out1Range: RangeProofLike;
  out2Range: RangeProofLike;
}

/** Deterministic Fiat-Shamir transfer proof with cryptographic Merkle membership */
export interface MerkleTransactionProof {
  in1Member: MerkleMembershipProof;
  in2Member: MerkleMembershipProof;
  in1Nullifier: NullifierProofLike;
  in2Nullifier: NullifierProofLike;
  balance: BalanceProof;
  out1Range: RangeProofLike;
  out2Range: RangeProofLike;
}

/** Public, replay-sensitive context for the SIS-note 2-in/2-out MVP statement */
export interface ConfidentialTransactionContext {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  root: MerkleAcceptedRoot;
  publicFee: number;
  cIn1: IntVec;
  cIn2: IntVec;
  cOut1: IntVec;
  cOut2: IntVec;
  nf1: IntVec;
  nf2: IntVec;
}

/** Public bignum transaction context for widened SIS-note parameters */
export interface BigIntConfidentialTransactionContext {
  protocolVersion: number;
  networkId: string;
  assetId: number;
  ledgerEpoch: number;
  root: MerkleAcceptedRoot;
  publicFee: ConfidentialBigIntInput;
  cIn1: BigIntVecInput;
  cIn2: BigIntVecInput;
  cOut1: BigIntVecInput;
  cOut2: BigIntVecInput;
  nf1: BigIntVecInput;
  nf2: BigIntVecInput;
}

/** Verifier-facing transaction envelope that binds a proof to public context bytes */
export interface ConfidentialTransactionEnvelope {
  context: ConfidentialTransactionContext;
  contextDigest: MerkleDigest;
  proof: MerkleTransactionProof;
}

/** Bignum transaction proof with cryptographic Merkle membership */
export interface BigIntMerkleTransactionProof {
  in1Member: MerkleMembershipProof;
  in2Member: MerkleMembershipProof;
  in1Nullifier: BigIntNullifierProofInput;
  in2Nullifier: BigIntNullifierProofInput;
  balance: BigIntBalanceProofInput;
  out1Range: BigIntRangeProofInput;
  out2Range: BigIntRangeProofInput;
}

/** Bignum transaction envelope that binds a proof to public context bytes */
export interface BigIntConfidentialTransactionEnvelope {
  context: BigIntConfidentialTransactionContext;
  contextDigest: MerkleDigest;
  proof: BigIntMerkleTransactionProof;
}

/** Public wallet proof request snapshot bound before local proof generation */
export interface ConfidentialWalletProofRequest {
  context: ConfidentialTransactionContext;
  acceptedRoots: MerkleAcceptedRoot[];
  spentNullifiers: IntMatrix;
}

/** Bignum wallet proof request snapshot bound before local proof generation */
export interface BigIntConfidentialWalletProofRequest {
  context: BigIntConfidentialTransactionContext;
  acceptedRoots: MerkleAcceptedRoot[];
  spentNullifiers: readonly BigIntVecInput[];
}

/** Local policy expected by a verifier before accepting a transaction envelope */
export interface ConfidentialTransactionContextPolicy {
  protocolVersion?: number;
  networkId: string;
  assetId: number;
  ledgerEpoch?: number;
  root?: MerkleAcceptedRoot;
  publicFee?: number;
}

/** Local policy expected by a verifier before accepting a bignum transaction envelope */
export interface BigIntConfidentialTransactionContextPolicy {
  protocolVersion?: number;
  networkId: string;
  assetId: number;
  ledgerEpoch?: number;
  root?: MerkleAcceptedRoot;
  publicFee?: ConfidentialBigIntInput;
}

/**
 * Raw Isabella module interface (from js_of_ocaml)
 * @internal
 */
interface IsabellaRuntime {
  modCentered(x: number, q: number): number;
  vecMod(v: number[], q: number): number[];
  vecModCentered(v: number[], q: number): number[];
  dist0(q: number, x: number): number;
  encodeBit(q: number, b: boolean): number;
  decodeBit(q: number, x: number): boolean;
  vecAdd(v1: number[], v2: number[]): number[];
  vecSub(v1: number[], v2: number[]): number[];
  scalarMult(c: number, v: number[]): number[];
  vecNeg(v: number[]): number[];
  innerProd(v1: number[], v2: number[]): number;
  matVecMult(mat: number[][], vec: number[]): number[];
  matVecMultMod(mat: number[][], vec: number[], q: number): number[];
  transpose(mat: number[][]): number[][];
  validVec(n: number, v: number[]): boolean;
  validMatrix(m: number, n: number, mat: number[][]): boolean;
  vecConcat(v1: number[], v2: number[]): number[];
  splitVec(n: number, v: number[]): [number[], number[]];
  dilParams(variant: string): DilithiumParams;
  dilModCentered(r: number, m: number): number;
  dilPower2Round(r: number, d: number): DilithiumSplit;
  dilDecompose(r: number, alpha: number): DilithiumSplit;
  dilHighBits(r: number, alpha: number): number;
  dilLowBits(r: number, alpha: number): number;
  dilMakeHint(z: number, r: number, alpha: number): number;
  dilUseHint(h: number, r: number, alpha: number): number;
  dilCheckBound(value: number, bound: number): boolean;
  dilHintWeight(hints: number[][]): number;
  cbMakeParams(m: number, n2: number, q: number, beta: number): ScalarCommitParams;
  cbValidScalarParams(params: ScalarCommitParams): boolean;
  cbRandCommitKey(params: ScalarCommitParams, ck: number[][]): number[][];
  cbRandCommit(params: ScalarCommitParams, ck: number[][], r: number[]): number[];
  cbAmountOfOpening(opening: CommitOpening): number;
  cbAggregateRandomness(
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening
  ): number[];
  cbBalanceCommitment(
    cIn1: number[],
    cIn2: number[],
    cOut1: number[],
    cOut2: number[],
    q: number
  ): number[];
  cbValidWitness(params: ScalarCommitParams, r: number[]): boolean;
  cbValidMask(params: ScalarCommitParams, gamma: number, y: number[]): boolean;
  cbValidResponse(
    params: ScalarCommitParams,
    gamma: number,
    challenge: number,
    z: number[]
  ): boolean;
  cbRelation(params: ScalarCommitParams, ck: number[][], c: number[], r: number[]): boolean;
  cbSigmaCommit(params: ScalarCommitParams, ck: number[][], y: number[]): number[];
  cbSigmaRespond(r: number[], y: number[], challenge: number): number[];
  cbCanonicalChallenge(params: ScalarCommitParams, ck: number[][], c: number[], a: number[]): number;
  cbFsRounds(): number;
  cbFsChallenges(
    params: ScalarCommitParams,
    ck: number[][],
    c: number[],
    as: number[][]
  ): number[];
  cbSigmaVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: number[][],
    c: number[],
    a: number[],
    challenge: number,
    z: number[]
  ): boolean;
  cbFsProve(
    params: ScalarCommitParams,
    gamma: number,
    ck: number[][],
    c: number[],
    r: number[],
    ys: number[][]
  ): BalanceProof | null;
  cbFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: number[][],
    c: number[],
    proof: BalanceProof
  ): boolean;
  crOneOpening(params: ScalarCommitParams): CommitOpening;
  crValidBitOpening(params: ScalarCommitParams, opening: CommitOpening): boolean;
  crBitPairRelation(params: ScalarCommitParams, bitOpening: CommitOpening, compOpening: CommitOpening): boolean;
  crWeightedCommitment(params: ScalarCommitParams, ck: number[][], bits: number[][]): number[];
  crAmountCommitment(
    params: ScalarCommitParams,
    ck: number[][],
    cAmount: number[],
    cBits: number[][]
  ): number[];
  crPairCommitment(
    params: ScalarCommitParams,
    ck: number[][],
    cBit: number[],
    cComp: number[]
  ): number[];
  crAmountWitnessBound(params: ScalarCommitParams, k: number): number;
  crPairWitnessBound(params: ScalarCommitParams): number;
  crValidAmountWitness(params: ScalarCommitParams, k: number, r: number[]): boolean;
  crValidPairWitness(params: ScalarCommitParams, r: number[]): boolean;
  crValidMask(params: ScalarCommitParams, gamma: number, y: number[]): boolean;
  crValidAmountResponse(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    challenge: number,
    z: number[]
  ): boolean;
  crValidPairResponse(
    params: ScalarCommitParams,
    gamma: number,
    challenge: number,
    z: number[]
  ): boolean;
  crCanonicalChallenge(
    params: ScalarCommitParams,
    ck: number[][],
    cAmount: number[],
    cBits: number[][],
    cComps: number[][],
    aAmounts: number[][],
    aPairss: number[][][]
  ): number;
  crFsProve(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    cAmount: number[],
    amountOpening: CommitOpening,
    bitMsgs: number[][],
    bitRands: number[][],
    compMsgs: number[][],
    compRands: number[][],
    yAmounts: number[][],
    yPairss: number[][][]
  ): RangeProofLike | null;
  crFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    cAmount: number[],
    proof: RangeProofLike
  ): boolean;
  ctNullifier(params: ScalarCommitParams, nk: number[][], opening: CommitOpening): number[];
  ctNullifierCanonicalChallenge(
    params: ScalarCommitParams,
    ck: number[][],
    nk: number[][],
    c: number[],
    nf: number[],
    aCommit: number[],
    aNullifier: number[]
  ): number;
  ctNullifierFsProve(
    params: ScalarCommitParams,
    gamma: number,
    ck: number[][],
    nk: number[][],
    c: number[],
    nf: number[],
    opening: CommitOpening,
    ys: CommitOpening[]
  ): NullifierProofLike | null;
  ctNullifierFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: number[][],
    nk: number[][],
    c: number[],
    nf: number[],
    proof: NullifierProofLike
  ): boolean;
  ctLedgerRoot(params: ScalarCommitParams, ledger: number[][]): number[];
  ctMembershipProve(
    params: ScalarCommitParams,
    ledger: number[][],
    c: number[]
  ): MembershipProof | null;
  ctMembershipVerify(
    params: ScalarCommitParams,
    c: number[],
    proof: MembershipProof
  ): boolean;
  ctCommitmentLedger(notes: VerifiedNote[]): number[][];
  ctLedgerValid(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    root: number[],
    notes: VerifiedNote[],
    spent: number[][]
  ): boolean;
  ctLedgerStepValidScaffold(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    nk: number[][],
    notes: VerifiedNote[],
    spent: number[][],
    cIn1: number[],
    cIn2: number[],
    cOut1: number[],
    cOut2: number[],
    nf1: number[],
    nf2: number[],
    proof: TransactionProof
  ): boolean;
  ctFsProve(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    nk: number[][],
    ledger: number[][],
    spent: number[][],
    cIn1: number[],
    cIn2: number[],
    cOut1: number[],
    cOut2: number[],
    nf1: number[],
    nf2: number[],
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening,
    out1Bits: CommitOpening[],
    out1Comps: CommitOpening[],
    out2Bits: CommitOpening[],
    out2Comps: CommitOpening[],
    yIn1: CommitOpening[],
    yIn2: CommitOpening[],
    yBalance: number[][],
    yOut1: number[][],
    yOut1Pairs: number[][][],
    yOut2: number[][],
    yOut2Pairs: number[][][]
  ): TransactionProof | null;
  ctFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: number[][],
    nk: number[][],
    root: number[],
    spent: number[][],
    cIn1: number[],
    cIn2: number[],
    cOut1: number[],
    cOut2: number[],
    nf1: number[],
    nf2: number[],
    proof: TransactionProof
  ): boolean;
  ctLedgerApplyNotes(
    notes: VerifiedNote[],
    proof: TransactionProof,
    cOut1: number[],
    cOut2: number[]
  ): VerifiedNote[];
  ctLedgerApplySpent(spent: number[][], nf1: number[], nf2: number[]): number[][];
}

// Access the global Isabella object that was set by js_of_ocaml
const Isabella: IsabellaRuntime = (globalThis as any).Isabella;

function normalizeInt(x: number): number {
  return Object.is(x, -0) ? 0 : x;
}

function normalizeVec(v: IntVec): IntVec {
  let normalized: IntVec | null = null;
  for (let index = 0; index < v.length; index += 1) {
    const value = v[index];
    const next = normalizeInt(value);
    if (normalized !== null) {
      normalized[index] = next;
    } else if (next !== value) {
      normalized = v.slice();
      normalized[index] = next;
    }
  }
  return normalized ?? v;
}

function normalizeMat(m: IntMatrix): IntMatrix {
  let normalized: IntMatrix | null = null;
  for (let index = 0; index < m.length; index += 1) {
    const row = m[index];
    const next = normalizeVec(row);
    if (normalized !== null) {
      normalized[index] = next;
    } else if (next !== row) {
      normalized = m.slice();
      normalized[index] = next;
    }
  }
  return normalized ?? m;
}

function sameVec(left: IntVec, right: IntVec): boolean {
  return JSON.stringify(left) === JSON.stringify(right);
}

function containsVec(values: IntMatrix, value: IntVec): boolean {
  return values.some((entry) => sameVec(entry, value));
}

function distinctMat(values: IntMatrix): boolean {
  const seen = new Set<string>();
  for (const value of values) {
    const key = JSON.stringify(value);
    if (seen.has(key)) {
      return false;
    }
    seen.add(key);
  }
  return true;
}

function validCommitKeyShape(params: ScalarCommitParams, key: IntMatrix): boolean {
  return (
    key.length === params.m &&
    key.every((row) => row.length === params.n1 + params.n2)
  );
}

function normalizeSplit(split: DilithiumSplit): DilithiumSplit {
  return { r1: normalizeInt(split.r1), r0: normalizeInt(split.r0) };
}

function normalizeChallengeValue(challenge: boolean | number): boolean | number {
  return typeof challenge === 'number' ? normalizeInt(challenge) : challenge;
}

function normalizeChallenges(
  challenges?: Array<boolean | number>
): Array<boolean | number> | undefined {
  if (challenges === undefined) {
    return undefined;
  }
  let normalized: Array<boolean | number> | null = null;
  for (let index = 0; index < challenges.length; index += 1) {
    const value = challenges[index];
    const next = normalizeChallengeValue(value);
    if (normalized !== null) {
      normalized[index] = next;
    } else if (next !== value) {
      normalized = challenges.slice();
      normalized[index] = next;
    }
  }
  return normalized ?? challenges;
}

function normalizeMatArray(mats: IntMatrix[]): IntMatrix[] {
  let normalized: IntMatrix[] | null = null;
  for (let index = 0; index < mats.length; index += 1) {
    const mat = mats[index];
    const next = normalizeMat(mat);
    if (normalized !== null) {
      normalized[index] = next;
    } else if (next !== mat) {
      normalized = mats.slice();
      normalized[index] = next;
    }
  }
  return normalized ?? mats;
}

function normalizeArray<T>(values: T[], normalize: (value: T) => T): T[] {
  let normalized: T[] | null = null;
  for (let index = 0; index < values.length; index += 1) {
    const value = values[index];
    const next = normalize(value);
    if (normalized !== null) {
      normalized[index] = next;
    } else if (next !== value) {
      normalized = values.slice();
      normalized[index] = next;
    }
  }
  return normalized ?? values;
}

function normalizeProof(proof: BalanceProof | null): BalanceProof | null {
  if (proof === null) {
    return null;
  }
  assertExactObjectKeys(proof, ['as', 'zs'], 'balanceProof');
  const as = normalizeMat(proof.as);
  const zs = normalizeMat(proof.zs);
  if (as === proof.as && zs === proof.zs) {
    return proof;
  }
  return {
    as,
    zs,
  };
}

function normalizeRangeRound(round: RangeRound): RangeRound {
  assertExactObjectKeysWithOptional(
    round,
    ['amountA', 'amountZ', 'pairAs', 'pairZs'],
    ['challenge'],
    'rangeRound'
  );
  const amountA = normalizeVec(round.amountA);
  const amountZ = normalizeVec(round.amountZ);
  const pairAs = normalizeMat(round.pairAs);
  const pairZs = normalizeMat(round.pairZs);
  const challenge =
    round.challenge === undefined ? undefined : normalizeChallengeValue(round.challenge);
  if (
    amountA === round.amountA &&
    amountZ === round.amountZ &&
    pairAs === round.pairAs &&
    pairZs === round.pairZs &&
    challenge === round.challenge
  ) {
    return round;
  }
  return {
    amountA,
    amountZ,
    pairAs,
    pairZs,
    challenge,
  };
}

function normalizeRangeProof(proof: RangeProofLike | null): RangeProofLike | null {
  if (proof === null) {
    return null;
  }
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    assertExactObjectKeys(proof, ['bits', 'comps', 'rounds'], 'rangeProof');
    const bits = normalizeMat(proof.bits);
    const comps = normalizeMat(proof.comps);
    const rounds = normalizeArray(proof.rounds, normalizeRangeRound);
    if (bits === proof.bits && comps === proof.comps && rounds === proof.rounds) {
      return proof;
    }
    return {
      bits,
      comps,
      rounds,
    };
  }
  if ('amountAs' in proof && 'amountZs' in proof && 'pairAss' in proof && 'pairZss' in proof) {
    assertExactObjectKeysWithOptional(
      proof,
      ['bits', 'comps', 'amountAs', 'amountZs', 'pairAss', 'pairZss'],
      ['challenges'],
      'rangeProof'
    );
    const bits = normalizeMat(proof.bits);
    const comps = normalizeMat(proof.comps);
    const amountAs = normalizeMat(proof.amountAs);
    const amountZs = normalizeMat(proof.amountZs);
    const pairAss = normalizeMatArray(proof.pairAss);
    const pairZss = normalizeMatArray(proof.pairZss);
    const challenges = normalizeChallenges(proof.challenges);
    if (
      bits === proof.bits &&
      comps === proof.comps &&
      amountAs === proof.amountAs &&
      amountZs === proof.amountZs &&
      pairAss === proof.pairAss &&
      pairZss === proof.pairZss &&
      challenges === proof.challenges
    ) {
      return proof;
    }
    return {
      bits,
      comps,
      amountAs,
      amountZs,
      pairAss,
      pairZss,
      challenges,
    };
  }
  const legacy = proof as RangeProof;
  assertExactObjectKeys(
    legacy,
    ['bits', 'comps', 'amountA', 'amountZ', 'pairAs', 'pairZs'],
    'rangeProof'
  );
  const bits = normalizeMat(legacy.bits);
  const comps = normalizeMat(legacy.comps);
  const amountA = normalizeVec(legacy.amountA);
  const amountZ = normalizeVec(legacy.amountZ);
  const pairAs = normalizeMat(legacy.pairAs);
  const pairZs = normalizeMat(legacy.pairZs);
  if (
    bits === legacy.bits &&
    comps === legacy.comps &&
    amountA === legacy.amountA &&
    amountZ === legacy.amountZ &&
    pairAs === legacy.pairAs &&
    pairZs === legacy.pairZs
  ) {
    return proof;
  }
  return {
    bits,
    comps,
    amountA,
    amountZ,
    pairAs,
    pairZs,
  };
}

function normalizeNullifierRound(round: NullifierRound): NullifierRound {
  assertExactObjectKeysWithOptional(
    round,
    ['aCommit', 'aNullifier', 'zMsg', 'zRand'],
    ['challenge'],
    'nullifierRound'
  );
  const aCommit = normalizeVec(round.aCommit);
  const aNullifier = normalizeVec(round.aNullifier);
  const zMsg = normalizeVec(round.zMsg);
  const zRand = normalizeVec(round.zRand);
  const challenge =
    round.challenge === undefined ? undefined : normalizeChallengeValue(round.challenge);
  if (
    aCommit === round.aCommit &&
    aNullifier === round.aNullifier &&
    zMsg === round.zMsg &&
    zRand === round.zRand &&
    challenge === round.challenge
  ) {
    return round;
  }
  return {
    aCommit,
    aNullifier,
    zMsg,
    zRand,
    challenge,
  };
}

function normalizeNullifierProof(
  proof: NullifierProofLike | null
): NullifierProofLike | null {
  if (proof === null) {
    return null;
  }
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    assertExactObjectKeys(proof, ['rounds'], 'nullifierProof');
    const rounds = normalizeArray(proof.rounds, normalizeNullifierRound);
    if (rounds === proof.rounds) {
      return proof;
    }
    return {
      rounds,
    };
  }
  if (
    'aCommits' in proof &&
    'aNullifiers' in proof &&
    'zMsgs' in proof &&
    'zRands' in proof
  ) {
    assertExactObjectKeysWithOptional(
      proof,
      ['aCommits', 'aNullifiers', 'zMsgs', 'zRands'],
      ['challenges'],
      'nullifierProof'
    );
    const aCommits = normalizeMat(proof.aCommits);
    const aNullifiers = normalizeMat(proof.aNullifiers);
    const zMsgs = normalizeMat(proof.zMsgs);
    const zRands = normalizeMat(proof.zRands);
    const challenges = normalizeChallenges(proof.challenges);
    if (
      aCommits === proof.aCommits &&
      aNullifiers === proof.aNullifiers &&
      zMsgs === proof.zMsgs &&
      zRands === proof.zRands &&
      challenges === proof.challenges
    ) {
      return proof;
    }
    return {
      aCommits,
      aNullifiers,
      zMsgs,
      zRands,
      challenges,
    };
  }
  const legacy = proof as NullifierProof;
  assertExactObjectKeys(legacy, ['aCommit', 'aNullifier', 'zMsg', 'zRand'], 'nullifierProof');
  const aCommit = normalizeVec(legacy.aCommit);
  const aNullifier = normalizeVec(legacy.aNullifier);
  const zMsg = normalizeVec(legacy.zMsg);
  const zRand = normalizeVec(legacy.zRand);
  if (
    aCommit === legacy.aCommit &&
    aNullifier === legacy.aNullifier &&
    zMsg === legacy.zMsg &&
    zRand === legacy.zRand
  ) {
    return proof;
  }
  return {
    aCommit,
    aNullifier,
    zMsg,
    zRand,
  };
}

function normalizeMembershipProof(proof: MembershipProof | null): MembershipProof | null {
  if (proof === null) {
    return null;
  }
  assertExactObjectKeys(proof, ['index', 'root', 'siblings', 'directions'], 'membershipProof');
  const index = normalizeInt(proof.index);
  const root = normalizeVec(proof.root);
  const siblings = normalizeMat(proof.siblings);
  if (index === proof.index && root === proof.root && siblings === proof.siblings) {
    return proof;
  }
  return {
    index,
    root,
    siblings,
    directions: proof.directions,
  };
}

function normalizeMerkleMembershipProof(proof: MerkleMembershipProof): MerkleMembershipProof {
  assertExactObjectKeys(proof, ['index', 'root', 'siblings', 'directions'], 'merkleMembershipProof');
  const index = normalizeInt(proof.index);
  if (index === proof.index) {
    return proof;
  }
  return {
    index,
    root: proof.root,
    siblings: proof.siblings,
    directions: proof.directions,
  };
}

function normalizeVerifiedNote(note: VerifiedNote): VerifiedNote {
  assertExactObjectKeys(note, ['commitment', 'rangeProof'], 'verifiedNote');
  const commitment = normalizeVec(note.commitment);
  const rangeProof = normalizeRangeProof(note.rangeProof)!;
  if (commitment === note.commitment && rangeProof === note.rangeProof) {
    return note;
  }
  return {
    commitment,
    rangeProof,
  };
}

function normalizeVerifiedNotes(notes: VerifiedNote[]): VerifiedNote[] {
  return normalizeArray(notes, normalizeVerifiedNote);
}

function normalizeTransactionProof(proof: TransactionProof | null): TransactionProof | null {
  if (proof === null) {
    return null;
  }
  assertExactObjectKeys(
    proof,
    ['in1Member', 'in2Member', 'in1Nullifier', 'in2Nullifier', 'balance', 'out1Range', 'out2Range'],
    'transactionProof'
  );
  const in1Member = normalizeMembershipProof(proof.in1Member)!;
  const in2Member = normalizeMembershipProof(proof.in2Member)!;
  const in1Nullifier = normalizeNullifierProof(proof.in1Nullifier)!;
  const in2Nullifier = normalizeNullifierProof(proof.in2Nullifier)!;
  const balance = normalizeProof(proof.balance)!;
  const out1Range = normalizeRangeProof(proof.out1Range)!;
  const out2Range = normalizeRangeProof(proof.out2Range)!;
  if (
    in1Member === proof.in1Member &&
    in2Member === proof.in2Member &&
    in1Nullifier === proof.in1Nullifier &&
    in2Nullifier === proof.in2Nullifier &&
    balance === proof.balance &&
    out1Range === proof.out1Range &&
    out2Range === proof.out2Range
  ) {
    return proof;
  }
  return {
    in1Member,
    in2Member,
    in1Nullifier,
    in2Nullifier,
    balance,
    out1Range,
    out2Range,
  };
}

function normalizeMerkleTransactionProof(
  proof: MerkleTransactionProof | null
): MerkleTransactionProof | null {
  if (proof === null) {
    return null;
  }
  assertExactObjectKeys(
    proof,
    ['in1Member', 'in2Member', 'in1Nullifier', 'in2Nullifier', 'balance', 'out1Range', 'out2Range'],
    'merkleTransactionProof'
  );
  const in1Member = normalizeMerkleMembershipProof(proof.in1Member);
  const in2Member = normalizeMerkleMembershipProof(proof.in2Member);
  const in1Nullifier = normalizeNullifierProof(proof.in1Nullifier)!;
  const in2Nullifier = normalizeNullifierProof(proof.in2Nullifier)!;
  const balance = normalizeProof(proof.balance)!;
  const out1Range = normalizeRangeProof(proof.out1Range)!;
  const out2Range = normalizeRangeProof(proof.out2Range)!;
  if (
    in1Member === proof.in1Member &&
    in2Member === proof.in2Member &&
    in1Nullifier === proof.in1Nullifier &&
    in2Nullifier === proof.in2Nullifier &&
    balance === proof.balance &&
    out1Range === proof.out1Range &&
    out2Range === proof.out2Range
  ) {
    return proof;
  }
  return {
    in1Member,
    in2Member,
    in1Nullifier,
    in2Nullifier,
    balance,
    out1Range,
    out2Range,
  };
}

const CT_MERKLE_DST = 'ISABELLA-CT-MERKLE-v1';
const CT_MERKLE_BIGNUM_DST = 'ISABELLA-CT-MERKLE-BIGNUM-v1';
const CT_MERKLE_TAGS = {
  leaf: 0,
  node: 1,
  empty: 2,
} as const;
const CT_TRANSACTION_DST = 'ISABELLA-CT-TX-v1';
const CT_TRANSACTION_BIGNUM_DST = 'ISABELLA-CT-TX-BIGNUM-v1';
const CT_TRANSACTION_PROTOCOL_ID = 'ISABELLA-CT-SIS-NOTE';
const CT_TRANSACTION_TAGS = {
  context: 0,
  merkleProof: 1,
  envelope: 2,
  walletProofRequest: 3,
  acceptedRootWindow: 4,
} as const;
const CT_FS_DST = 'ISABELLA-CT-FS-v1';
const CT_FS_BALANCE_DOMAIN = 1001;
const CT_FS_RANGE_DOMAIN = 2001;
const CT_FS_NULLIFIER_DOMAIN = 3001;
const CT_FS_ROUNDS = 128;
const CT_BIGNUM_DST = 'ISABELLA-CT-BIGNUM-v1';
const CT_BIGNUM_ENCODING = 'sign_u8 || len_i64_le || magnitude_le_minimal';

export type ConfidentialBigIntInput = bigint | number | string;

function assertSafeI64(value: number, label: string): void {
  if (!Number.isSafeInteger(value)) {
    throw new RangeError(`${label} must be a safe signed integer`);
  }
  if (Object.is(value, -0)) {
    throw new RangeError(`${label} must not be negative zero`);
  }
}

function assertNonNegativeSafeI64(value: number, label: string): void {
  assertSafeI64(value, label);
  if (value < 0) {
    throw new RangeError(`${label} must be non-negative`);
  }
}

function assertSafeArrayLength(value: number, label: string): void {
  assertNonNegativeSafeI64(value, label);
  if (value > 1_000_000) {
    throw new RangeError(`${label} is too large to allocate safely`);
  }
}

function sampleCenteredInt(bound: number, label: string): number {
  assertNonNegativeSafeI64(bound, label);
  const width = 2 * bound + 1;
  if (!Number.isSafeInteger(width) || width > 2 ** 48) {
    throw new RangeError(`${label} is too large for unbiased Node.js randomInt sampling`);
  }
  return randomInt(width) - bound;
}

function sampleCenteredVector(length: number, bound: number, label: string): IntVec {
  assertSafeArrayLength(length, `${label}.length`);
  return Array.from({ length }, (_, index) => sampleCenteredInt(bound, `${label}[${index}]`));
}

function encodeI64LE(value: number, label: string): Buffer {
  assertSafeI64(value, label);
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function normalizeConfidentialBigInt(value: ConfidentialBigIntInput, label: string): bigint {
  if (typeof value === 'bigint') {
    return value;
  }
  if (typeof value === 'number') {
    assertSafeI64(value, label);
    return BigInt(value);
  }
  if (typeof value === 'string') {
    if (!/^(0|-?[1-9][0-9]*)$/.test(value)) {
      throw new Error(`${label} must be a canonical decimal integer`);
    }
    return BigInt(value);
  }
  throw new Error(`${label} must be bigint, number, or canonical decimal string`);
}

function encodeConfidentialBigInt(value: ConfidentialBigIntInput, label: string): Buffer {
  const normalized = normalizeConfidentialBigInt(value, label);
  const negative = normalized < 0n;
  let magnitude = negative ? -normalized : normalized;
  const bytes: number[] = [];
  while (magnitude > 0n) {
    bytes.push(Number(magnitude & 0xffn));
    magnitude >>= 8n;
  }
  assertNonNegativeSafeI64(bytes.length, `${label}.magnitude_length`);
  return Buffer.concat([
    Buffer.from([negative ? 1 : 0]),
    encodeI64LE(bytes.length, `${label}.magnitude_length`),
    Buffer.from(bytes),
  ]);
}

function encodeConfidentialBigIntVector(
  values: readonly ConfidentialBigIntInput[],
  label: string
): Buffer {
  assertNonNegativeSafeI64(values.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(values.length, `${label}.length`),
    ...values.map((value, index) => encodeConfidentialBigInt(value, `${label}[${index}]`)),
  ]);
}

function normalizeBigIntVec(values: readonly ConfidentialBigIntInput[], label: string): BigIntVec {
  if (!Array.isArray(values)) {
    throw new Error(`${label} must be an array`);
  }
  assertSafeArrayLength(values.length, `${label}.length`);
  return values.map((value, index) => normalizeConfidentialBigInt(value, `${label}[${index}]`));
}

function normalizeBigIntMatrix(
  rows: readonly (readonly ConfidentialBigIntInput[])[],
  label: string
): BigIntMatrix {
  if (!Array.isArray(rows)) {
    throw new Error(`${label} must be an array`);
  }
  assertSafeArrayLength(rows.length, `${label}.length`);
  return rows.map((row, index) => normalizeBigIntVec(row, `${label}[${index}]`));
}

function bigintAbs(value: bigint): bigint {
  return value < 0n ? -value : value;
}

function bigintMod(value: bigint, modulus: bigint): bigint {
  if (modulus <= 1n) {
    throw new RangeError('modulus must be greater than 1');
  }
  const reduced = value % modulus;
  return reduced < 0n ? reduced + modulus : reduced;
}

function bigintVecMod(values: readonly bigint[], modulus: bigint): BigIntVec {
  return values.map((value) => bigintMod(value, modulus));
}

function bigintVecAdd(left: readonly bigint[], right: readonly bigint[]): BigIntVec {
  if (left.length !== right.length) {
    throw new Error('vector lengths must agree');
  }
  return left.map((value, index) => value + right[index]);
}

function bigintScalarMult(scalar: bigint, values: readonly bigint[]): BigIntVec {
  return values.map((value) => scalar * value);
}

function bigintMatVecMult(matrix: readonly (readonly bigint[])[], vector: readonly bigint[]): BigIntVec {
  return matrix.map((row) => {
    if (row.length !== vector.length) {
      throw new Error('matrix row length must match vector length');
    }
    return row.reduce((acc, value, index) => acc + value * vector[index], 0n);
  });
}

function bigintMatVecMultMod(
  matrix: readonly (readonly bigint[])[],
  vector: readonly bigint[],
  modulus: bigint
): BigIntVec {
  return bigintVecMod(bigintMatVecMult(matrix, vector), modulus);
}

function bigintAllBounded(values: readonly bigint[], bound: bigint): boolean {
  return bound >= 0n && values.every((value) => bigintAbs(value) <= bound);
}

function bigintSum(values: readonly bigint[]): bigint {
  return values.reduce((acc, value) => acc + value, 0n);
}

function bigintMatrixSum(rows: readonly (readonly bigint[])[]): bigint {
  return rows.reduce((acc, row) => acc + bigintSum(row), 0n);
}

function encodeFsTranscript(domain: number, round: number, fields: readonly bigint[]): Buffer {
  return Buffer.concat([
    Buffer.from(CT_FS_DST, 'ascii'),
    encodeI64LE(domain, 'fs.domain'),
    encodeI64LE(round, 'fs.round'),
    encodeI64LE(fields.length, 'fs.field_count'),
    ...fields.map((field, index) => encodeConfidentialBigInt(field, `fs.fields[${index}]`)),
  ]);
}

function binaryFsChallenge(domain: number, fields: readonly bigint[], round: number): number {
  const digest = createHash('sha3-256').update(encodeFsTranscript(domain, round, fields)).digest();
  return digest[0] & 1;
}

function encodeIntVector(values: IntVec, label: string): Buffer {
  assertNonNegativeSafeI64(values.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(values.length, `${label}.length`),
    ...values.map((value, index) => encodeI64LE(value, `${label}[${index}]`)),
  ]);
}

function encodeBoolVector(values: boolean[], label: string): Buffer {
  assertNonNegativeSafeI64(values.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(values.length, `${label}.length`),
    ...values.map((value, index) => {
      if (typeof value !== 'boolean') {
        throw new Error(`${label}[${index}] must be boolean`);
      }
      return encodeI64LE(value ? 1 : 0, `${label}[${index}]`);
    }),
  ]);
}

function encodeIntMatrix(rows: IntMatrix, label: string): Buffer {
  assertNonNegativeSafeI64(rows.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(rows.length, `${label}.length`),
    ...rows.map((row, index) => encodeIntVector(row, `${label}[${index}]`)),
  ]);
}

function encodeIntMatrixArray(mats: IntMatrix[], label: string): Buffer {
  assertNonNegativeSafeI64(mats.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(mats.length, `${label}.length`),
    ...mats.map((mat, index) => encodeIntMatrix(mat, `${label}[${index}]`)),
  ]);
}

function encodeBigIntMatrix(rows: BigIntMatrixInput, label: string): Buffer {
  const normalized = normalizeBigIntMatrix(rows, label);
  return Buffer.concat([
    encodeI64LE(normalized.length, `${label}.length`),
    ...normalized.map((row, index) => encodeConfidentialBigIntVector(row, `${label}[${index}]`)),
  ]);
}

function encodeBigIntMatrixArray(mats: readonly BigIntMatrixInput[], label: string): Buffer {
  assertNonNegativeSafeI64(mats.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(mats.length, `${label}.length`),
    ...mats.map((mat, index) => encodeBigIntMatrix(mat, `${label}[${index}]`)),
  ]);
}

function encodeAsciiString(value: string, label: string): Buffer {
  const bytes = [...value].map((char, index) => {
    const code = char.charCodeAt(0);
    if (code > 0x7e || code < 0x20) {
      throw new Error(`${label}[${index}] must be printable ASCII`);
    }
    return code;
  });
  assertNonNegativeSafeI64(bytes.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(bytes.length, `${label}.length`),
    Buffer.from(bytes),
  ]);
}

function encodeDigest(digest: MerkleDigest, label: string): Buffer {
  assertDigestHex(digest, label);
  const bytes = Buffer.from(digest, 'hex');
  return Buffer.concat([
    encodeI64LE(bytes.length, `${label}.length`),
    bytes,
  ]);
}

function encodeDigestVector(digests: MerkleDigest[], label: string): Buffer {
  assertNonNegativeSafeI64(digests.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(digests.length, `${label}.length`),
    ...digests.map((digest, index) => encodeDigest(digest, `${label}[${index}]`)),
  ]);
}

function assertExactObjectKeys(value: unknown, keys: string[], label: string): void {
  assertExactObjectKeysWithOptional(value, keys, [], label);
}

function assertExactObjectKeysWithOptional(
  value: unknown,
  requiredKeys: string[],
  optionalKeys: string[],
  label: string
): void {
  if (typeof value !== 'object' || value === null || Array.isArray(value)) {
    throw new Error(`${label} must be an object`);
  }
  const allowed = new Set([...requiredKeys, ...optionalKeys]);
  const present = Object.keys(value);
  const missing = requiredKeys.filter((key) => !Object.prototype.hasOwnProperty.call(value, key));
  if (missing.length > 0) {
    throw new Error(`${label} is missing required fields: ${missing.join(', ')}`);
  }
  const unsupported = present.filter((key) => !allowed.has(key));
  if (unsupported.length > 0) {
    throw new Error(`${label} contains unsupported fields: ${unsupported.join(', ')}`);
  }
}

function encodeAcceptedRoot(root: MerkleAcceptedRoot, label: string): Buffer {
  assertExactObjectKeys(root, ['digest', 'depth'], label);
  assertNonNegativeSafeI64(root.depth, `${label}.depth`);
  return Buffer.concat([
    encodeDigest(root.digest, `${label}.digest`),
    encodeI64LE(root.depth, `${label}.depth`),
  ]);
}

function encodeAcceptedRootVector(roots: MerkleAcceptedRoot[], label: string): Buffer {
  assertNonNegativeSafeI64(roots.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(roots.length, `${label}.length`),
    ...roots.map((root, index) => encodeAcceptedRoot(root, `${label}[${index}]`)),
  ]);
}

function encodeAcceptedRootWindowEntry(
  entry: ConfidentialAcceptedRootWindowEntry,
  label: string
): Buffer {
  assertExactObjectKeys(entry, ['root', 'validFromEpoch', 'expiresAtEpoch'], label);
  assertNonNegativeSafeI64(entry.validFromEpoch, `${label}.validFromEpoch`);
  assertNonNegativeSafeI64(entry.expiresAtEpoch, `${label}.expiresAtEpoch`);
  if (entry.expiresAtEpoch <= entry.validFromEpoch) {
    throw new Error(`${label}.expiresAtEpoch must be greater than validFromEpoch`);
  }
  return Buffer.concat([
    encodeAcceptedRoot(entry.root, `${label}.root`),
    encodeI64LE(entry.validFromEpoch, `${label}.validFromEpoch`),
    encodeI64LE(entry.expiresAtEpoch, `${label}.expiresAtEpoch`),
  ]);
}

function encodeAcceptedRootWindowEntryVector(
  entries: ConfidentialAcceptedRootWindowEntry[],
  label: string
): Buffer {
  assertNonNegativeSafeI64(entries.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(entries.length, `${label}.length`),
    ...entries.map((entry, index) => encodeAcceptedRootWindowEntry(entry, `${label}[${index}]`)),
  ]);
}

function compareIntVectors(left: IntVec, right: IntVec): number {
  const width = Math.min(left.length, right.length);
  for (let index = 0; index < width; index += 1) {
    if (left[index] < right[index]) {
      return -1;
    }
    if (left[index] > right[index]) {
      return 1;
    }
  }
  return Math.sign(left.length - right.length);
}

function compareBigIntVectors(left: readonly bigint[], right: readonly bigint[]): number {
  const width = Math.min(left.length, right.length);
  for (let index = 0; index < width; index += 1) {
    if (left[index] < right[index]) {
      return -1;
    }
    if (left[index] > right[index]) {
      return 1;
    }
  }
  return Math.sign(left.length - right.length);
}

function compareAcceptedRoots(left: MerkleAcceptedRoot, right: MerkleAcceptedRoot): number {
  if (left.digest < right.digest) {
    return -1;
  }
  if (left.digest > right.digest) {
    return 1;
  }
  return Math.sign(left.depth - right.depth);
}

function sameAcceptedRoot(left: MerkleAcceptedRoot, right: MerkleAcceptedRoot): boolean {
  return left.digest === right.digest && left.depth === right.depth;
}

function compareAcceptedRootWindowEntries(
  left: ConfidentialAcceptedRootWindowEntry,
  right: ConfidentialAcceptedRootWindowEntry
): number {
  return compareAcceptedRoots(left.root, right.root);
}

function assertCanonicalDigestSet(digests: MerkleDigest[], label: string): void {
  if (digests.length === 0) {
    throw new Error(`${label} must not be empty`);
  }
  let previous: MerkleDigest | null = null;
  for (let index = 0; index < digests.length; index += 1) {
    const digest = digests[index];
    assertDigestHex(digest, `${label}[${index}]`);
    if (previous !== null && previous >= digest) {
      throw new Error(`${label} must be sorted lexicographically with no duplicates`);
    }
    previous = digest;
  }
}

function assertCanonicalAcceptedRootSet(roots: MerkleAcceptedRoot[], label: string): void {
  if (roots.length === 0) {
    throw new Error(`${label} must not be empty`);
  }
  let previous: MerkleAcceptedRoot | null = null;
  for (let index = 0; index < roots.length; index += 1) {
    const root = roots[index];
    encodeAcceptedRoot(root, `${label}[${index}]`);
    if (previous !== null && compareAcceptedRoots(previous, root) >= 0) {
      throw new Error(`${label} must be sorted by digest/depth with no duplicates`);
    }
    previous = root;
  }
}

function assertCanonicalAcceptedRootWindow(window: ConfidentialAcceptedRootWindow): void {
  assertExactObjectKeys(
    window,
    ['protocolVersion', 'networkId', 'assetId', 'ledgerEpoch', 'roots'],
    'acceptedRootWindow'
  );
  assertNonNegativeSafeI64(window.protocolVersion, 'acceptedRootWindow.protocolVersion');
  assertNonNegativeSafeI64(window.assetId, 'acceptedRootWindow.assetId');
  assertNonNegativeSafeI64(window.ledgerEpoch, 'acceptedRootWindow.ledgerEpoch');
  if (window.roots.length === 0) {
    throw new Error('acceptedRootWindow.roots must not be empty');
  }
  let previous: ConfidentialAcceptedRootWindowEntry | null = null;
  for (let index = 0; index < window.roots.length; index += 1) {
    const entry = window.roots[index];
    encodeAcceptedRootWindowEntry(entry, `acceptedRootWindow.roots[${index}]`);
    if (entry.validFromEpoch > window.ledgerEpoch || window.ledgerEpoch >= entry.expiresAtEpoch) {
      throw new Error(`acceptedRootWindow.roots[${index}] is not live at ledgerEpoch`);
    }
    if (previous !== null && compareAcceptedRootWindowEntries(previous, entry) >= 0) {
      throw new Error('acceptedRootWindow.roots must be sorted by digest/depth with no duplicates');
    }
    previous = entry;
  }
}

function assertCanonicalIntMatrixSet(rows: IntMatrix, label: string): void {
  assertNonNegativeSafeI64(rows.length, `${label}.length`);
  let previous: IntVec | null = null;
  for (let rowIndex = 0; rowIndex < rows.length; rowIndex += 1) {
    const row = rows[rowIndex];
    assertNonNegativeSafeI64(row.length, `${label}[${rowIndex}].length`);
    for (let colIndex = 0; colIndex < row.length; colIndex += 1) {
      assertSafeI64(row[colIndex], `${label}[${rowIndex}][${colIndex}]`);
    }
    if (previous !== null && compareIntVectors(previous, row) >= 0) {
      throw new Error(`${label} must be sorted lexicographically with no duplicates`);
    }
    previous = row;
  }
}

function assertCanonicalBigIntMatrixSet(rows: readonly BigIntVecInput[], label: string): BigIntMatrix {
  if (!Array.isArray(rows)) {
    throw new Error(`${label} must be an array`);
  }
  assertNonNegativeSafeI64(rows.length, `${label}.length`);
  const normalized = normalizeBigIntMatrix(rows, label);
  let previous: BigIntVec | null = null;
  for (let rowIndex = 0; rowIndex < normalized.length; rowIndex += 1) {
    const row = normalized[rowIndex];
    if (previous !== null && compareBigIntVectors(previous, row) >= 0) {
      throw new Error(`${label} must be sorted lexicographically with no duplicates`);
    }
    previous = row;
  }
  return normalized;
}

function merklePreimage(tag: number, body: Buffer): Buffer {
  return Buffer.concat([
    Buffer.from(CT_MERKLE_DST, 'ascii'),
    encodeI64LE(tag, 'merkle tag'),
    body,
  ]);
}

function merkleBignumPreimage(tag: number, body: Buffer): Buffer {
  return Buffer.concat([
    Buffer.from(CT_MERKLE_BIGNUM_DST, 'ascii'),
    encodeI64LE(tag, 'merkle tag'),
    body,
  ]);
}

function sha3Hex(preimage: Buffer): MerkleDigest {
  return createHash('sha3-256').update(preimage).digest('hex');
}

function assertDigestHex(digest: MerkleDigest, label: string): void {
  if (!/^[0-9a-f]{64}$/.test(digest)) {
    throw new Error(`${label} must be a canonical lowercase SHA3-256 digest`);
  }
}

function digestToByteVector(digest: MerkleDigest, label: string): IntVec {
  assertDigestHex(digest, label);
  return [...Buffer.from(digest, 'hex')];
}

function merkleLeafPreimage(commitment: IntVec): Buffer {
  return merklePreimage(CT_MERKLE_TAGS.leaf, encodeIntVector(commitment, 'commitment'));
}

function merkleBignumLeafPreimage(commitment: BigIntVecInput): Buffer {
  return merkleBignumPreimage(
    CT_MERKLE_TAGS.leaf,
    encodeConfidentialBigIntVector(commitment, 'commitment')
  );
}

function merkleEmptyPreimage(width: number): Buffer {
  assertNonNegativeSafeI64(width, 'width');
  return merklePreimage(CT_MERKLE_TAGS.empty, encodeI64LE(width, 'width'));
}

function merkleBignumEmptyPreimage(width: number): Buffer {
  assertNonNegativeSafeI64(width, 'width');
  return merkleBignumPreimage(CT_MERKLE_TAGS.empty, encodeI64LE(width, 'width'));
}

function merkleNodePreimage(left: MerkleDigest, right: MerkleDigest): Buffer {
  return merklePreimage(
    CT_MERKLE_TAGS.node,
    Buffer.concat([
      encodeIntVector(digestToByteVector(left, 'left'), 'left'),
      encodeIntVector(digestToByteVector(right, 'right'), 'right'),
    ])
  );
}

function merkleBignumNodePreimage(left: MerkleDigest, right: MerkleDigest): Buffer {
  return merkleBignumPreimage(
    CT_MERKLE_TAGS.node,
    Buffer.concat([
      encodeDigest(left, 'left'),
      encodeDigest(right, 'right'),
    ])
  );
}

function merkleHashLeaf(commitment: IntVec): MerkleDigest {
  return sha3Hex(merkleLeafPreimage(commitment));
}

function merkleBignumHashLeaf(commitment: BigIntVecInput): MerkleDigest {
  return sha3Hex(merkleBignumLeafPreimage(commitment));
}

function merkleHashEmpty(width: number): MerkleDigest {
  return sha3Hex(merkleEmptyPreimage(width));
}

function merkleBignumHashEmpty(width: number): MerkleDigest {
  return sha3Hex(merkleBignumEmptyPreimage(width));
}

function merkleHashNode(left: MerkleDigest, right: MerkleDigest): MerkleDigest {
  return sha3Hex(merkleNodePreimage(left, right));
}

function merkleBignumHashNode(left: MerkleDigest, right: MerkleDigest): MerkleDigest {
  return sha3Hex(merkleBignumNodePreimage(left, right));
}

function transactionContextPreimage(context: ConfidentialTransactionContext): Buffer {
  assertExactObjectKeys(
    context,
    [
      'protocolVersion',
      'networkId',
      'assetId',
      'ledgerEpoch',
      'root',
      'publicFee',
      'cIn1',
      'cIn2',
      'cOut1',
      'cOut2',
      'nf1',
      'nf2',
    ],
    'context'
  );
  assertNonNegativeSafeI64(context.protocolVersion, 'protocolVersion');
  assertNonNegativeSafeI64(context.assetId, 'assetId');
  assertNonNegativeSafeI64(context.ledgerEpoch, 'ledgerEpoch');
  assertNonNegativeSafeI64(context.publicFee, 'publicFee');
  return Buffer.concat([
    Buffer.from(CT_TRANSACTION_DST, 'ascii'),
    encodeI64LE(CT_TRANSACTION_TAGS.context, 'transaction tag'),
    encodeAsciiString(CT_TRANSACTION_PROTOCOL_ID, 'protocolId'),
    encodeI64LE(context.protocolVersion, 'protocolVersion'),
    encodeAsciiString(context.networkId, 'networkId'),
    encodeI64LE(context.assetId, 'assetId'),
    encodeI64LE(context.ledgerEpoch, 'ledgerEpoch'),
    encodeAcceptedRoot(context.root, 'root'),
    encodeI64LE(context.publicFee, 'publicFee'),
    encodeIntVector(context.cIn1, 'cIn1'),
    encodeIntVector(context.cIn2, 'cIn2'),
    encodeIntVector(context.cOut1, 'cOut1'),
    encodeIntVector(context.cOut2, 'cOut2'),
    encodeIntVector(context.nf1, 'nf1'),
    encodeIntVector(context.nf2, 'nf2'),
  ]);
}

function transactionTaggedPreimage(tag: number, body: Buffer): Buffer {
  return Buffer.concat([
    Buffer.from(CT_TRANSACTION_DST, 'ascii'),
    encodeI64LE(tag, 'transaction tag'),
    encodeAsciiString(CT_TRANSACTION_PROTOCOL_ID, 'protocolId'),
    body,
  ]);
}

function transactionAcceptedRootWindowPreimage(
  window: ConfidentialAcceptedRootWindow
): Buffer {
  assertCanonicalAcceptedRootWindow(window);
  return transactionTaggedPreimage(
    CT_TRANSACTION_TAGS.acceptedRootWindow,
    Buffer.concat([
      encodeI64LE(window.protocolVersion, 'acceptedRootWindow.protocolVersion'),
      encodeAsciiString(window.networkId, 'acceptedRootWindow.networkId'),
      encodeI64LE(window.assetId, 'acceptedRootWindow.assetId'),
      encodeI64LE(window.ledgerEpoch, 'acceptedRootWindow.ledgerEpoch'),
      encodeAcceptedRootWindowEntryVector(window.roots, 'acceptedRootWindow.roots'),
    ])
  );
}

function transactionBignumTaggedPreimage(tag: number, body: Buffer): Buffer {
  return Buffer.concat([
    Buffer.from(CT_TRANSACTION_BIGNUM_DST, 'ascii'),
    encodeI64LE(tag, 'transaction tag'),
    encodeAsciiString(CT_TRANSACTION_PROTOCOL_ID, 'protocolId'),
    body,
  ]);
}

function transactionBignumContextPreimage(context: BigIntConfidentialTransactionContext): Buffer {
  assertExactObjectKeys(
    context,
    [
      'protocolVersion',
      'networkId',
      'assetId',
      'ledgerEpoch',
      'root',
      'publicFee',
      'cIn1',
      'cIn2',
      'cOut1',
      'cOut2',
      'nf1',
      'nf2',
    ],
    'context'
  );
  assertNonNegativeSafeI64(context.protocolVersion, 'protocolVersion');
  assertNonNegativeSafeI64(context.assetId, 'assetId');
  assertNonNegativeSafeI64(context.ledgerEpoch, 'ledgerEpoch');
  return Buffer.concat([
    Buffer.from(CT_TRANSACTION_BIGNUM_DST, 'ascii'),
    encodeI64LE(CT_TRANSACTION_TAGS.context, 'transaction tag'),
    encodeAsciiString(CT_TRANSACTION_PROTOCOL_ID, 'protocolId'),
    encodeI64LE(context.protocolVersion, 'protocolVersion'),
    encodeAsciiString(context.networkId, 'networkId'),
    encodeI64LE(context.assetId, 'assetId'),
    encodeI64LE(context.ledgerEpoch, 'ledgerEpoch'),
    encodeAcceptedRoot(context.root, 'root'),
    encodeConfidentialBigInt(context.publicFee, 'publicFee'),
    encodeConfidentialBigIntVector(context.cIn1, 'cIn1'),
    encodeConfidentialBigIntVector(context.cIn2, 'cIn2'),
    encodeConfidentialBigIntVector(context.cOut1, 'cOut1'),
    encodeConfidentialBigIntVector(context.cOut2, 'cOut2'),
    encodeConfidentialBigIntVector(context.nf1, 'nf1'),
    encodeConfidentialBigIntVector(context.nf2, 'nf2'),
  ]);
}

function transactionBignumAcceptedRootWindowPreimage(
  window: ConfidentialAcceptedRootWindow
): Buffer {
  assertCanonicalAcceptedRootWindow(window);
  return transactionBignumTaggedPreimage(
    CT_TRANSACTION_TAGS.acceptedRootWindow,
    Buffer.concat([
      encodeI64LE(window.protocolVersion, 'acceptedRootWindow.protocolVersion'),
      encodeAsciiString(window.networkId, 'acceptedRootWindow.networkId'),
      encodeI64LE(window.assetId, 'acceptedRootWindow.assetId'),
      encodeI64LE(window.ledgerEpoch, 'acceptedRootWindow.ledgerEpoch'),
      encodeAcceptedRootWindowEntryVector(window.roots, 'acceptedRootWindow.roots'),
    ])
  );
}

function normalizeBigIntBalanceProofInput(
  proof: BigIntBalanceProofInput,
  label: string
): BigIntBalanceProof {
  assertExactObjectKeys(proof, ['as', 'zs'], label);
  return {
    as: normalizeBigIntMatrix(proof.as, `${label}.as`),
    zs: normalizeBigIntMatrix(proof.zs, `${label}.zs`),
  };
}

function normalizeBigIntNullifierProofInput(
  proof: BigIntNullifierProofInput,
  label: string
): BigIntNullifierProof {
  assertExactObjectKeys(proof, ['aCommits', 'aNullifiers', 'zMsgs', 'zRands'], label);
  return {
    aCommits: normalizeBigIntMatrix(proof.aCommits, `${label}.aCommits`),
    aNullifiers: normalizeBigIntMatrix(proof.aNullifiers, `${label}.aNullifiers`),
    zMsgs: normalizeBigIntMatrix(proof.zMsgs, `${label}.zMsgs`),
    zRands: normalizeBigIntMatrix(proof.zRands, `${label}.zRands`),
  };
}

function normalizeBigIntRangeProofInput(
  proof: BigIntRangeProofInput,
  label: string
): BigIntRangeProof {
  assertExactObjectKeys(proof, ['bits', 'comps', 'amountAs', 'amountZs', 'pairAss', 'pairZss'], label);
  assertNonNegativeSafeI64(proof.pairAss.length, `${label}.pairAss.length`);
  assertNonNegativeSafeI64(proof.pairZss.length, `${label}.pairZss.length`);
  return {
    bits: normalizeBigIntMatrix(proof.bits, `${label}.bits`),
    comps: normalizeBigIntMatrix(proof.comps, `${label}.comps`),
    amountAs: normalizeBigIntMatrix(proof.amountAs, `${label}.amountAs`),
    amountZs: normalizeBigIntMatrix(proof.amountZs, `${label}.amountZs`),
    pairAss: proof.pairAss.map((mat, index) => normalizeBigIntMatrix(mat, `${label}.pairAss[${index}]`)),
    pairZss: proof.pairZss.map((mat, index) => normalizeBigIntMatrix(mat, `${label}.pairZss[${index}]`)),
  };
}

function transactionBignumMembershipPreimage(
  proof: MerkleMembershipProof,
  label: string
): Buffer {
  proof = normalizeMerkleMembershipProof(proof);
  if (proof.siblings.length !== proof.directions.length) {
    throw new Error(`${label}.siblings and ${label}.directions must have the same length`);
  }
  assertNonNegativeSafeI64(proof.index, `${label}.index`);
  return Buffer.concat([
    encodeI64LE(proof.index, `${label}.index`),
    encodeDigest(proof.root, `${label}.root`),
    encodeDigestVector(proof.siblings, `${label}.siblings`),
    encodeBoolVector(proof.directions, `${label}.directions`),
  ]);
}

function transactionBignumNullifierProofPreimage(
  proof: BigIntNullifierProofInput,
  label: string
): Buffer {
  const normalized = normalizeBigIntNullifierProofInput(proof, label);
  return Buffer.concat([
    encodeBigIntMatrix(normalized.aCommits, `${label}.aCommits`),
    encodeBigIntMatrix(normalized.aNullifiers, `${label}.aNullifiers`),
    encodeBigIntMatrix(normalized.zMsgs, `${label}.zMsgs`),
    encodeBigIntMatrix(normalized.zRands, `${label}.zRands`),
  ]);
}

function transactionBignumBalanceProofPreimage(
  proof: BigIntBalanceProofInput,
  label: string
): Buffer {
  const normalized = normalizeBigIntBalanceProofInput(proof, label);
  return Buffer.concat([
    encodeBigIntMatrix(normalized.as, `${label}.as`),
    encodeBigIntMatrix(normalized.zs, `${label}.zs`),
  ]);
}

function transactionBignumRangeProofPreimage(
  proof: BigIntRangeProofInput,
  label: string
): Buffer {
  const normalized = normalizeBigIntRangeProofInput(proof, label);
  return Buffer.concat([
    encodeBigIntMatrix(normalized.bits, `${label}.bits`),
    encodeBigIntMatrix(normalized.comps, `${label}.comps`),
    encodeBigIntMatrix(normalized.amountAs, `${label}.amountAs`),
    encodeBigIntMatrix(normalized.amountZs, `${label}.amountZs`),
    encodeBigIntMatrixArray(normalized.pairAss, `${label}.pairAss`),
    encodeBigIntMatrixArray(normalized.pairZss, `${label}.pairZss`),
  ]);
}

function transactionBignumMerkleProofPreimage(proof: BigIntMerkleTransactionProof): Buffer {
  assertExactObjectKeys(
    proof,
    ['in1Member', 'in2Member', 'in1Nullifier', 'in2Nullifier', 'balance', 'out1Range', 'out2Range'],
    'proof'
  );
  return transactionBignumTaggedPreimage(
    CT_TRANSACTION_TAGS.merkleProof,
    Buffer.concat([
      transactionBignumMembershipPreimage(proof.in1Member, 'in1Member'),
      transactionBignumMembershipPreimage(proof.in2Member, 'in2Member'),
      transactionBignumNullifierProofPreimage(proof.in1Nullifier, 'in1Nullifier'),
      transactionBignumNullifierProofPreimage(proof.in2Nullifier, 'in2Nullifier'),
      transactionBignumBalanceProofPreimage(proof.balance, 'balance'),
      transactionBignumRangeProofPreimage(proof.out1Range, 'out1Range'),
      transactionBignumRangeProofPreimage(proof.out2Range, 'out2Range'),
    ])
  );
}

function transactionBignumEnvelopePreimage(
  envelope: BigIntConfidentialTransactionEnvelope
): Buffer {
  assertExactObjectKeys(envelope, ['context', 'contextDigest', 'proof'], 'envelope');
  const contextDigest = sha3Hex(transactionBignumContextPreimage(envelope.context));
  if (envelope.contextDigest !== contextDigest) {
    throw new Error('contextDigest does not match canonical bignum transaction context');
  }
  return transactionBignumTaggedPreimage(
    CT_TRANSACTION_TAGS.envelope,
    Buffer.concat([
      encodeDigest(contextDigest, 'contextDigest'),
      encodeDigest(sha3Hex(transactionBignumMerkleProofPreimage(envelope.proof)), 'proofDigest'),
    ])
  );
}

function sameBigIntVec(left: readonly bigint[], right: readonly bigint[]): boolean {
  return left.length === right.length && left.every((value, index) => value === right[index]);
}

function containsBigIntVec(rows: readonly (readonly bigint[])[], target: readonly bigint[]): boolean {
  return rows.some((row) => sameBigIntVec(row, target));
}

function transactionBignumWalletProofRequestPreimage(
  request: BigIntConfidentialWalletProofRequest
): Buffer {
  assertExactObjectKeys(request, ['context', 'acceptedRoots', 'spentNullifiers'], 'walletProofRequest');
  assertCanonicalAcceptedRootSet(request.acceptedRoots, 'acceptedRoots');
  const spentNullifiers = assertCanonicalBigIntMatrixSet(request.spentNullifiers, 'spentNullifiers');
  const contextDigest = sha3Hex(transactionBignumContextPreimage(request.context));
  const nf1 = normalizeBigIntVec(request.context.nf1, 'context.nf1');
  const nf2 = normalizeBigIntVec(request.context.nf2, 'context.nf2');
  if (!request.acceptedRoots.some((root) => sameAcceptedRoot(root, request.context.root))) {
    throw new Error('context.root must be inside acceptedRoots');
  }
  if (sameBigIntVec(nf1, nf2)) {
    throw new Error('context nullifiers must be distinct');
  }
  if (containsBigIntVec(spentNullifiers, nf1) || containsBigIntVec(spentNullifiers, nf2)) {
    throw new Error('context nullifiers must be absent from spentNullifiers');
  }
  return transactionBignumTaggedPreimage(
    CT_TRANSACTION_TAGS.walletProofRequest,
    Buffer.concat([
      encodeDigest(contextDigest, 'contextDigest'),
      encodeAcceptedRootVector(request.acceptedRoots, 'acceptedRoots'),
      encodeBigIntMatrix(spentNullifiers, 'spentNullifiers'),
    ])
  );
}

function listedNullifierProof(proof: NullifierProofLike): ListedNullifierProof {
  const checkedProof = normalizeNullifierProof(proof)!;
  proof = checkedProof;
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return {
      aCommits: proof.rounds.map((round) => round.aCommit),
      aNullifiers: proof.rounds.map((round) => round.aNullifier),
      zMsgs: proof.rounds.map((round) => round.zMsg),
      zRands: proof.rounds.map((round) => round.zRand),
    };
  }
  if (
    'aCommits' in proof &&
    'aNullifiers' in proof &&
    'zMsgs' in proof &&
    'zRands' in proof
  ) {
    return proof;
  }
  const legacy = proof as NullifierProof;
  return {
    aCommits: [legacy.aCommit],
    aNullifiers: [legacy.aNullifier],
    zMsgs: [legacy.zMsg],
    zRands: [legacy.zRand],
  };
}

function listedRangeProof(proof: RangeProofLike): ListedRangeProof {
  const checkedProof = normalizeRangeProof(proof)!;
  proof = checkedProof;
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return {
      bits: proof.bits,
      comps: proof.comps,
      amountAs: proof.rounds.map((round) => round.amountA),
      amountZs: proof.rounds.map((round) => round.amountZ),
      pairAss: proof.rounds.map((round) => round.pairAs),
      pairZss: proof.rounds.map((round) => round.pairZs),
    };
  }
  if ('amountAs' in proof && 'amountZs' in proof && 'pairAss' in proof && 'pairZss' in proof) {
    return proof;
  }
  const legacy = proof as RangeProof;
  return {
    bits: legacy.bits,
    comps: legacy.comps,
    amountAs: [legacy.amountA],
    amountZs: [legacy.amountZ],
    pairAss: [legacy.pairAs],
    pairZss: [legacy.pairZs],
  };
}

function transactionMerkleMembershipPreimage(
  proof: MerkleMembershipProof,
  label: string
): Buffer {
  proof = normalizeMerkleMembershipProof(proof);
  if (proof.siblings.length !== proof.directions.length) {
    throw new Error(`${label}.siblings and ${label}.directions must have the same length`);
  }
  assertNonNegativeSafeI64(proof.index, `${label}.index`);
  return Buffer.concat([
    encodeI64LE(proof.index, `${label}.index`),
    encodeDigest(proof.root, `${label}.root`),
    encodeDigestVector(proof.siblings, `${label}.siblings`),
    encodeBoolVector(proof.directions, `${label}.directions`),
  ]);
}

function transactionNullifierProofPreimage(
  proof: NullifierProofLike,
  label: string
): Buffer {
  const listed = listedNullifierProof(proof);
  return Buffer.concat([
    encodeIntMatrix(listed.aCommits, `${label}.aCommits`),
    encodeIntMatrix(listed.aNullifiers, `${label}.aNullifiers`),
    encodeIntMatrix(listed.zMsgs, `${label}.zMsgs`),
    encodeIntMatrix(listed.zRands, `${label}.zRands`),
  ]);
}

function transactionBalanceProofPreimage(proof: BalanceProof, label: string): Buffer {
  proof = normalizeProof(proof)!;
  return Buffer.concat([
    encodeIntMatrix(proof.as, `${label}.as`),
    encodeIntMatrix(proof.zs, `${label}.zs`),
  ]);
}

function transactionRangeProofPreimage(proof: RangeProofLike, label: string): Buffer {
  const listed = listedRangeProof(proof);
  return Buffer.concat([
    encodeIntMatrix(listed.bits, `${label}.bits`),
    encodeIntMatrix(listed.comps, `${label}.comps`),
    encodeIntMatrix(listed.amountAs, `${label}.amountAs`),
    encodeIntMatrix(listed.amountZs, `${label}.amountZs`),
    encodeIntMatrixArray(listed.pairAss, `${label}.pairAss`),
    encodeIntMatrixArray(listed.pairZss, `${label}.pairZss`),
  ]);
}

function transactionMerkleProofPreimage(proof: MerkleTransactionProof): Buffer {
  proof = normalizeMerkleTransactionProof(proof)!;
  return transactionTaggedPreimage(
    CT_TRANSACTION_TAGS.merkleProof,
    Buffer.concat([
      transactionMerkleMembershipPreimage(proof.in1Member, 'in1Member'),
      transactionMerkleMembershipPreimage(proof.in2Member, 'in2Member'),
      transactionNullifierProofPreimage(proof.in1Nullifier, 'in1Nullifier'),
      transactionNullifierProofPreimage(proof.in2Nullifier, 'in2Nullifier'),
      transactionBalanceProofPreimage(proof.balance, 'balance'),
      transactionRangeProofPreimage(proof.out1Range, 'out1Range'),
      transactionRangeProofPreimage(proof.out2Range, 'out2Range'),
    ])
  );
}

function transactionEnvelopePreimage(envelope: ConfidentialTransactionEnvelope): Buffer {
  assertExactObjectKeys(envelope, ['context', 'contextDigest', 'proof'], 'envelope');
  const contextDigest = sha3Hex(transactionContextPreimage(envelope.context));
  if (envelope.contextDigest !== contextDigest) {
    throw new Error('contextDigest does not match canonical transaction context');
  }
  return transactionTaggedPreimage(
    CT_TRANSACTION_TAGS.envelope,
    Buffer.concat([
      encodeDigest(contextDigest, 'contextDigest'),
      encodeDigest(sha3Hex(transactionMerkleProofPreimage(envelope.proof)), 'proofDigest'),
    ])
  );
}

function transactionWalletProofRequestPreimage(
  request: ConfidentialWalletProofRequest
): Buffer {
  assertExactObjectKeys(request, ['context', 'acceptedRoots', 'spentNullifiers'], 'walletProofRequest');
  assertCanonicalAcceptedRootSet(request.acceptedRoots, 'acceptedRoots');
  assertCanonicalIntMatrixSet(request.spentNullifiers, 'spentNullifiers');
  const contextDigest = sha3Hex(transactionContextPreimage(request.context));
  if (!request.acceptedRoots.some((root) => sameAcceptedRoot(root, request.context.root))) {
    throw new Error('context.root must be inside acceptedRoots');
  }
  if (sameVec(request.context.nf1, request.context.nf2)) {
    throw new Error('context nullifiers must be distinct');
  }
  if (
    containsVec(request.spentNullifiers, request.context.nf1) ||
    containsVec(request.spentNullifiers, request.context.nf2)
  ) {
    throw new Error('context nullifiers must be absent from spentNullifiers');
  }
  return transactionTaggedPreimage(
    CT_TRANSACTION_TAGS.walletProofRequest,
    Buffer.concat([
      encodeDigest(contextDigest, 'contextDigest'),
      encodeAcceptedRootVector(request.acceptedRoots, 'acceptedRoots'),
      encodeIntMatrix(request.spentNullifiers, 'spentNullifiers'),
    ])
  );
}

function merkleCompressLevel(width: number, level: MerkleDigest[]): MerkleDigest[] {
  if (level.length === 0) {
    return [];
  }
  if (level.length === 1) {
    return level.slice();
  }
  const out: MerkleDigest[] = [];
  const empty = merkleHashEmpty(width);
  for (let index = 0; index < level.length; index += 2) {
    const left = level[index];
    const right = index + 1 < level.length ? level[index + 1] : empty;
    out.push(merkleHashNode(left, right));
  }
  return out;
}

function merkleBignumCompressLevel(width: number, level: MerkleDigest[]): MerkleDigest[] {
  if (level.length === 0) {
    return [];
  }
  if (level.length === 1) {
    return level.slice();
  }
  const out: MerkleDigest[] = [];
  const empty = merkleBignumHashEmpty(width);
  for (let index = 0; index < level.length; index += 2) {
    const left = level[index];
    const right = index + 1 < level.length ? level[index + 1] : empty;
    out.push(merkleBignumHashNode(left, right));
  }
  return out;
}

function merkleIndexDirections(depth: number, index: number): boolean[] {
  assertNonNegativeSafeI64(depth, 'depth');
  assertNonNegativeSafeI64(index, 'index');
  const directions: boolean[] = [];
  let current = index;
  for (let round = 0; round < depth; round += 1) {
    directions.push(current % 2 === 1);
    current = Math.floor(current / 2);
  }
  return directions;
}

function assertMerkleCommitmentWidths(commitments: IntMatrix, width: number): void {
  for (let index = 0; index < commitments.length; index += 1) {
    if (commitments[index].length !== width) {
      throw new Error('Merkle commitments must all have the selected width');
    }
  }
}

function assertBigIntMerkleCommitmentWidths(commitments: readonly BigIntVecInput[], width: number): BigIntMatrix {
  const normalized = normalizeBigIntMatrix(commitments, 'commitments');
  for (let index = 0; index < normalized.length; index += 1) {
    if (normalized[index].length !== width) {
      throw new Error('Merkle commitments must all have the selected width');
    }
  }
  return normalized;
}

/**
 * Modular arithmetic operations over Z_q
 *
 * These functions provide operations for working with integers modulo q,
 * with a focus on centered representation used in lattice cryptography.
 */
export namespace Zq {
  /**
   * Centered modular reduction: maps x to (-q/2, q/2]
   *
   * @param x - Value to reduce
   * @param q - Modulus (must be positive)
   * @returns Centered representative
   *
   * @example
   * ```ts
   * Zq.modCentered(7, 5)  // => 2
   * Zq.modCentered(8, 5)  // => -2
   * ```
   */
  export function modCentered(x: number, q: number): number {
    return Isabella.modCentered(x, q);
  }

  /**
   * Apply modular reduction to each element of a vector
   *
   * @param v - Input vector
   * @param q - Modulus
   * @returns Vector with each element reduced mod q
   */
  export function vecMod(v: IntVec, q: number): IntVec {
    return normalizeVec(Isabella.vecMod(v, q));
  }

  /**
   * Apply centered modular reduction to each element
   *
   * @param v - Input vector
   * @param q - Modulus
   * @returns Vector with centered representatives
   */
  export function vecModCentered(v: IntVec, q: number): IntVec {
    return normalizeVec(Isabella.vecModCentered(v, q));
  }

  /**
   * Distance from zero in Z_q
   *
   * Computes |mod_centered(x, q)|, useful for decryption correctness.
   *
   * @param q - Modulus
   * @param x - Value
   * @returns Non-negative distance
   */
  export function dist0(q: number, x: number): number {
    return Isabella.dist0(q, x);
  }

  /**
   * Encode a bit for LWE encryption
   *
   * - false encodes to 0
   * - true encodes to q/2
   *
   * @param q - Modulus
   * @param bit - Bit to encode
   * @returns Encoded value
   */
  export function encodeBit(q: number, bit: boolean): number {
    return Isabella.encodeBit(q, bit);
  }

  /**
   * Decode a bit from LWE ciphertext
   *
   * Returns true if distance from zero exceeds q/4.
   *
   * @param q - Modulus
   * @param x - Value to decode
   * @returns Decoded bit
   */
  export function decodeBit(q: number, x: number): boolean {
    return Isabella.decodeBit(q, x);
  }

  /**
   * Matrix-vector multiplication modulo q
   *
   * @param mat - Matrix (m × n)
   * @param vec - Vector (length n)
   * @param q - Modulus
   * @returns Result vector (length m) with entries mod q
   */
  export function matVecMultMod(mat: IntMatrix, vec: IntVec, q: number): IntVec {
    return normalizeVec(Isabella.matVecMultMod(mat, vec, q));
  }
}

/**
 * Vector and matrix operations
 *
 * Basic linear algebra over integers, matching the Isabelle formalization.
 */
export namespace Vec {
  /**
   * Element-wise vector addition
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Sum vector
   */
  export function add(v1: IntVec, v2: IntVec): IntVec {
    return normalizeVec(Isabella.vecAdd(v1, v2));
  }

  /**
   * Element-wise vector subtraction
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Difference vector
   */
  export function sub(v1: IntVec, v2: IntVec): IntVec {
    return normalizeVec(Isabella.vecSub(v1, v2));
  }

  /**
   * Scalar multiplication
   *
   * @param c - Scalar
   * @param v - Vector
   * @returns Scaled vector
   */
  export function scale(c: number, v: IntVec): IntVec {
    return normalizeVec(Isabella.scalarMult(c, v));
  }

  /**
   * Vector negation
   *
   * @param v - Input vector
   * @returns Negated vector
   */
  export function neg(v: IntVec): IntVec {
    return normalizeVec(Isabella.vecNeg(v));
  }

  /**
   * Inner product (dot product)
   *
   * @param v1 - First vector
   * @param v2 - Second vector (same length)
   * @returns Sum of element-wise products
   */
  export function dot(v1: IntVec, v2: IntVec): number {
    return Isabella.innerProd(v1, v2);
  }

  /**
   * Concatenate two vectors
   *
   * @param v1 - First vector
   * @param v2 - Second vector
   * @returns Concatenated vector
   */
  export function concat(v1: IntVec, v2: IntVec): IntVec {
    return normalizeVec(Isabella.vecConcat(v1, v2));
  }

  /**
   * Split vector at position n
   *
   * @param n - Split position
   * @param v - Vector to split
   * @returns Tuple of [first n elements, remaining elements]
   */
  export function split(n: number, v: IntVec): [IntVec, IntVec] {
    const [left, right] = Isabella.splitVec(n, v);
    return [normalizeVec(left), normalizeVec(right)];
  }

  /**
   * Check if vector has given dimension
   *
   * @param n - Expected dimension
   * @param v - Vector to check
   * @returns true if length equals n
   */
  export function isValid(n: number, v: IntVec): boolean {
    return Isabella.validVec(n, v);
  }
}

/**
 * Matrix operations
 */
export namespace Mat {
  /**
   * Matrix-vector multiplication
   *
   * @param mat - Matrix (m × n)
   * @param vec - Vector (length n)
   * @returns Result vector (length m)
   */
  export function vecMult(mat: IntMatrix, vec: IntVec): IntVec {
    return normalizeVec(Isabella.matVecMult(mat, vec));
  }

  /**
   * Matrix transpose
   *
   * @param mat - Input matrix
   * @returns Transposed matrix
   */
  export function transpose(mat: IntMatrix): IntMatrix {
    return normalizeMat(Isabella.transpose(mat));
  }

  /**
   * Check if matrix has dimensions m × n
   *
   * @param m - Expected rows
   * @param n - Expected columns
   * @param mat - Matrix to check
   * @returns true if dimensions match
   */
  export function isValid(m: number, n: number, mat: IntMatrix): boolean {
    return Isabella.validMatrix(m, n, mat);
  }
}

/**
 * Dilithium / ML-DSA helper functions
 *
 * These operations are the coefficient-level compression and hint primitives
 * used by FIPS 204 ML-DSA, exposed through the shared SDK surface.
 */
export namespace Dilithium {
  /**
   * Select one of the standardized ML-DSA parameter sets.
   *
   * @param variant - One of the FIPS 204 parameter families
   * @returns Parameter record for the chosen variant
   */
  export function params(variant: DilithiumVariant): DilithiumParams {
    return Isabella.dilParams(variant);
  }

  /**
   * Centered modular reduction used by the Dilithium compression helpers.
   *
   * @param r - Value to reduce
   * @param m - Positive modulus
   * @returns Centered representative in (-m/2, m/2]
   */
  export function modCentered(r: number, m: number): number {
    return Isabella.dilModCentered(r, m);
  }

  /**
   * Split a coefficient into high and low parts using 2^d.
   *
   * @param r - Input coefficient
   * @param d - Power-of-two bit width
   * @returns Pair (r1, r0) such that r = r1 * 2^d + r0
   */
  export function power2Round(r: number, d: number): DilithiumSplit {
    return normalizeSplit(Isabella.dilPower2Round(r, d));
  }

  /**
   * Split a coefficient into high and low parts using alpha = 2 * gamma2.
   *
   * @param r - Input coefficient
   * @param alpha - Decomposition modulus
   * @returns Pair (r1, r0) used by HighBits and LowBits
   */
  export function decompose(r: number, alpha: number): DilithiumSplit {
    return normalizeSplit(Isabella.dilDecompose(r, alpha));
  }

  /**
   * Extract the high-order decomposition component.
   *
   * @param r - Input coefficient
   * @param alpha - Decomposition modulus
   * @returns HighBits(r, alpha)
   */
  export function highBits(r: number, alpha: number): number {
    return Isabella.dilHighBits(r, alpha);
  }

  /**
   * Extract the low-order decomposition component.
   *
   * @param r - Input coefficient
   * @param alpha - Decomposition modulus
   * @returns LowBits(r, alpha)
   */
  export function lowBits(r: number, alpha: number): number {
    return Isabella.dilLowBits(r, alpha);
  }

  /**
   * Compute whether adding z changes the extracted high bits.
   *
   * @param z - Adjustment coefficient
   * @param r - Reference coefficient
   * @param alpha - Decomposition modulus
   * @returns 1 if a hint is needed, otherwise 0
   */
  export function makeHint(z: number, r: number, alpha: number): number {
    return Isabella.dilMakeHint(z, r, alpha);
  }

  /**
   * Recover adjusted high bits from a hint bit.
   *
   * @param h - Hint bit
   * @param r - Reference coefficient
   * @param alpha - Decomposition modulus
   * @returns Adjusted high bits
   */
  export function useHint(h: number, r: number, alpha: number): number {
    return Isabella.dilUseHint(h, r, alpha);
  }

  /**
   * Check the strict coefficient bound |value| < bound.
   *
   * @param value - Coefficient to check
   * @param bound - Strict upper bound
   * @returns true when the coefficient satisfies the bound
   */
  export function checkBound(value: number, bound: number): boolean {
    return Isabella.dilCheckBound(value, bound);
  }

  /**
   * Count the total number of hint bits set to 1.
   *
   * @param hints - Hint matrix encoded as 0/1 rows
   * @returns Total Hamming weight across all rows
   */
  export function hintWeight(hints: IntMatrix): number {
    return Isabella.dilHintWeight(hints);
  }
}

/**
 * CSPRNG-backed sampling helpers for confidential-transfer masks.
 *
 * These helpers use Node.js `crypto.randomInt` for unbiased centered integer
 * sampling. They are runtime conveniences for mask generation; callers still
 * pass the sampled masks into the checked proof APIs.
 */
export namespace ConfidentialBignum {
  export const dst = CT_BIGNUM_DST;
  export const integerEncoding = CT_BIGNUM_ENCODING;
  export const vectorEncoding = 'len_i64_le || bignum...';

  export function encodeInteger(value: ConfidentialBigIntInput): Uint8Array {
    return Uint8Array.from(encodeConfidentialBigInt(value, 'value'));
  }

  export function encodeIntegerHex(value: ConfidentialBigIntInput): string {
    return encodeConfidentialBigInt(value, 'value').toString('hex');
  }

  export function encodeIntegerVector(values: readonly ConfidentialBigIntInput[]): Uint8Array {
    return Uint8Array.from(encodeConfidentialBigIntVector(values, 'values'));
  }

  export function encodeIntegerVectorHex(values: readonly ConfidentialBigIntInput[]): string {
    return encodeConfidentialBigIntVector(values, 'values').toString('hex');
  }

  export function digestInteger(value: ConfidentialBigIntInput): MerkleDigest {
    return sha3Hex(Buffer.concat([
      Buffer.from(CT_BIGNUM_DST, 'ascii'),
      encodeConfidentialBigInt(value, 'value'),
    ]));
  }

  export function digestIntegerVector(values: readonly ConfidentialBigIntInput[]): MerkleDigest {
    return sha3Hex(Buffer.concat([
      Buffer.from(CT_BIGNUM_DST, 'ascii'),
      encodeConfidentialBigIntVector(values, 'values'),
    ]));
  }
}

export namespace ConfidentialSampling {
  /**
   * Sample uniformly from the centered interval [-bound, bound].
   */
  export function boundedInt(bound: number): number {
    return sampleCenteredInt(bound, 'bound');
  }

  /**
   * Sample an integer vector with every coordinate in [-bound, bound].
   */
  export function intVector(length: number, bound: number): IntVec {
    return sampleCenteredVector(length, bound, 'vector');
  }

  /**
   * Sample a commitment-opening-shaped mask.
   */
  export function opening(msgLength: number, randLength: number, bound: number): CommitOpening {
    return {
      msg: sampleCenteredVector(msgLength, bound, 'opening.msg'),
      rand: sampleCenteredVector(randLength, bound, 'opening.rand'),
    };
  }

  /**
   * Sample repeated commitment-opening-shaped masks.
   */
  export function openings(
    count: number,
    msgLength: number,
    randLength: number,
    bound: number
  ): CommitOpening[] {
    assertSafeArrayLength(count, 'openings.length');
    return Array.from({ length: count }, () => opening(msgLength, randLength, bound));
  }
}

/**
 * Confidential-balance proof helpers over SIS commitments.
 *
 * This is the first privacy slice toward confidential token transfers:
 * it proves that an aggregate input/output commitment opens to zero amount,
 * without yet solving range proofs or double-spend prevention.
 */
export namespace ConfidentialBalance {
  /**
   * Build scalar commitment parameters with the message dimension fixed to 1.
   *
   * @param m - Commitment output dimension
   * @param n2 - Randomness dimension
   * @param q - Modulus
   * @param beta - Opening bound
   * @returns Parameter record with n1 fixed to 1
   */
  export function makeParams(m: number, n2: number, q: number, beta: number): ScalarCommitParams {
    return Isabella.cbMakeParams(m, n2, q, beta);
  }

  /**
   * Check that parameters are valid for the scalar confidential-balance slice.
   *
   * @param params - Candidate parameter record
   * @returns true when params are valid and n1 = 1
   */
  export function validScalarParams(params: ScalarCommitParams): boolean {
    return Isabella.cbValidScalarParams(params);
  }

  /**
   * Drop the message column(s) from a commitment key.
   *
   * @param params - Commitment parameters
   * @param ck - Full commitment key matrix
   * @returns Randomness-only commitment key
   */
  export function randCommitKey(params: ScalarCommitParams, ck: IntMatrix): IntMatrix {
    return normalizeMat(Isabella.cbRandCommitKey(params, ck));
  }

  /**
   * Commit to the aggregate randomness using the randomness-only key.
   *
   * @param params - Commitment parameters
   * @param ck - Full commitment key matrix
   * @param r - Aggregate randomness witness
   * @returns Commitment vector
   */
  export function randCommit(params: ScalarCommitParams, ck: IntMatrix, r: IntVec): IntVec {
    return normalizeVec(Isabella.cbRandCommit(params, ck, r));
  }

  /**
   * Extract the scalar amount from a commitment opening.
   *
   * @param opening - Opening with message and randomness parts
   * @returns First message coordinate, or 0 for an empty message list
   */
  export function amountOfOpening(opening: CommitOpening): number {
    return Isabella.cbAmountOfOpening(opening);
  }

  /**
   * Aggregate randomness from two inputs and two outputs.
   *
   * @param opIn1 - First input opening
   * @param opIn2 - Second input opening
   * @param opOut1 - First output opening
   * @param opOut2 - Second output opening
   * @returns Aggregate randomness witness
   */
  export function aggregateRandomness(
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening
  ): IntVec {
    return normalizeVec(Isabella.cbAggregateRandomness(opIn1, opIn2, opOut1, opOut2));
  }

  /**
   * Aggregate input and output commitments into a zero-balance target.
   *
   * @param cIn1 - First input commitment
   * @param cIn2 - Second input commitment
   * @param cOut1 - First output commitment
   * @param cOut2 - Second output commitment
   * @param q - Commitment modulus
   * @returns Aggregate commitment difference modulo q
   */
  export function balanceCommitment(
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    q: number
  ): IntVec {
    return normalizeVec(Isabella.cbBalanceCommitment(cIn1, cIn2, cOut1, cOut2, q));
  }

  /**
   * Commit to a public fee amount with zero randomness.
   */
  export function publicAmountCommitment(
    params: ScalarCommitParams,
    ck: IntMatrix,
    fee: number
  ): IntVec {
    assertNonNegativeSafeI64(fee, 'fee');
    return Zq.matVecMultMod(
      ck,
      Vec.concat([fee], Array.from({ length: params.n2 }, () => 0)),
      params.q
    );
  }

  /**
   * Subtract a public fee commitment from the aggregate balance commitment.
   */
  export function feeBalanceCommitment(
    params: ScalarCommitParams,
    ck: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    fee: number
  ): IntVec {
    return Zq.vecMod(
      Vec.sub(
        balanceCommitment(cIn1, cIn2, cOut1, cOut2, params.q),
        publicAmountCommitment(params, ck, fee)
      ),
      params.q
    );
  }

  /**
   * Check witness bounds.
   *
   * @param params - Commitment parameters
   * @param r - Aggregate randomness witness
   * @returns true when r has the right length and bound
   */
  export function validWitness(params: ScalarCommitParams, r: IntVec): boolean {
    return Isabella.cbValidWitness(params, r);
  }

  /**
   * Check mask bounds.
   *
   * @param params - Commitment parameters
   * @param gamma - Mask bound
   * @param y - Mask vector
   * @returns true when y has the right length and bound
   */
  export function validMask(params: ScalarCommitParams, gamma: number, y: IntVec): boolean {
    return Isabella.cbValidMask(params, gamma, y);
  }

  /**
   * Check response bounds.
   *
   * @param params - Commitment parameters
   * @param gamma - Mask bound
   * @param z - Response vector
   * @returns true when z has the right length and bound
   */
  export function validResponse(
    params: ScalarCommitParams,
    gamma: number,
    challenge: number,
    z: IntVec
  ): boolean {
    return Isabella.cbValidResponse(params, gamma, challenge, z);
  }

  /**
   * Check the confidential-balance relation against an aggregate commitment.
   *
   * @param params - Commitment parameters
   * @param ck - Full commitment key matrix
   * @param c - Aggregate commitment difference
   * @param r - Aggregate randomness witness
   * @returns true when c is the commitment to r under the randomness-only key
   */
  export function relation(params: ScalarCommitParams, ck: IntMatrix, c: IntVec, r: IntVec): boolean {
    return Isabella.cbRelation(params, ck, c, r);
  }

  /**
   * Compute the sigma-protocol announcement.
   *
   * @param params - Commitment parameters
   * @param ck - Full commitment key matrix
   * @param y - Mask vector
   * @returns Announcement vector
   */
  export function sigmaCommit(params: ScalarCommitParams, ck: IntMatrix, y: IntVec): IntVec {
    return normalizeVec(Isabella.cbSigmaCommit(params, ck, y));
  }

  /**
   * Compute the sigma-protocol response.
   *
   * @param r - Aggregate randomness witness
   * @param y - Mask vector
   * @param challenge - Fiat-Shamir challenge reduced modulo q
   * @returns Response vector
   */
  export function sigmaRespond(r: IntVec, y: IntVec, challenge: number): IntVec {
    return normalizeVec(Isabella.cbSigmaRespond(r, y, challenge));
  }

  /**
   * Derive the deterministic Fiat-Shamir challenge.
   *
   * @param params - Commitment parameters
   * @param ck - Full commitment key matrix
   * @param c - Aggregate commitment difference
   * @param a - Sigma announcement
   * @returns Deterministic challenge reduced modulo q
   */
  export function canonicalChallenge(
    params: ScalarCommitParams,
    ck: IntMatrix,
    c: IntVec,
    a: IntVec
  ): number {
    return Isabella.cbCanonicalChallenge(params, ck, c, a);
  }

  export function fsRounds(): number {
    return Isabella.cbFsRounds();
  }

  /**
   * Sample a CSPRNG-backed balance proof mask.
   */
  export function sampleMask(params: ScalarCommitParams, gamma: number): IntVec {
    return ConfidentialSampling.intVector(params.n2, gamma);
  }

  /**
   * Sample one CSPRNG-backed balance proof mask per Fiat-Shamir round.
   */
  export function sampleMasks(
    params: ScalarCommitParams,
    gamma: number,
    rounds: number = fsRounds()
  ): IntMatrix {
    assertSafeArrayLength(rounds, 'rounds');
    return Array.from({ length: rounds }, () => sampleMask(params, gamma));
  }

  export function fsChallenges(
    params: ScalarCommitParams,
    ck: IntMatrix,
    c: IntVec,
    as: IntMatrix
  ): number[] {
    return normalizeVec(Isabella.cbFsChallenges(params, ck, c, as));
  }

  /**
   * Verify the sigma-protocol step directly.
   *
   * @param params - Commitment parameters
   * @param gamma - Mask bound
   * @param ck - Full commitment key matrix
   * @param c - Aggregate commitment difference
   * @param a - Sigma announcement
   * @param challenge - Deterministic challenge reduced modulo q
   * @param z - Response vector
   * @returns true when the sigma step verifies
   */
  export function sigmaVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    c: IntVec,
    a: IntVec,
    challenge: number,
    z: IntVec
  ): boolean {
    return Isabella.cbSigmaVerify(params, gamma, ck, c, a, challenge, z);
  }

  /**
   * Build a deterministic Fiat-Shamir proof.
   *
   * @param params - Commitment parameters
   * @param gamma - Mask bound
   * @param ck - Full commitment key matrix
   * @param c - Aggregate commitment difference
   * @param r - Aggregate randomness witness
   * @param ys - Mask vectors, one per Fiat-Shamir round
   * @returns Proof object, or null if the inputs violate the relation or bounds
   */
  export function fsProve(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    c: IntVec,
    r: IntVec,
    ys: IntMatrix
  ): BalanceProof | null {
    return normalizeProof(Isabella.cbFsProve(params, gamma, ck, c, r, ys));
  }

  /**
   * Verify a deterministic Fiat-Shamir proof.
   *
   * @param params - Commitment parameters
   * @param gamma - Mask bound
   * @param ck - Full commitment key matrix
   * @param c - Aggregate commitment difference
   * @param proof - Proof object with per-round announcements and responses
   * @returns true when the proof verifies
   */
  export function fsVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    c: IntVec,
    proof: BalanceProof
  ): boolean {
    try {
      const checkedProof = normalizeProof(proof);
      return checkedProof !== null && Isabella.cbFsVerify(params, gamma, ck, c, checkedProof);
    } catch {
      return false;
    }
  }
}

/**
 * BigInt reference implementation for the confidential-balance proof slice.
 *
 * This is a TypeScript reference path for widened parameter candidates whose
 * modulus and proof bounds exceed the current js_of_ocaml number surface. It
 * uses the same canonical Fiat-Shamir bignum transcript-field encoding as the
 * native transcript backends. OCaml/Haskell multiprecision parity remains a
 * separate launch-readiness blocker.
 */
export namespace ConfidentialBalanceBigInt {
  export const transcriptDst = CT_FS_DST;
  export const fsDomain = CT_FS_BALANCE_DOMAIN;
  export const fieldEncoding = CT_BIGNUM_ENCODING;

  export function makeParams(
    m: number,
    n2: number,
    q: ConfidentialBigIntInput,
    beta: ConfidentialBigIntInput
  ): BigIntScalarCommitParams {
    assertSafeArrayLength(m, 'm');
    assertSafeArrayLength(n2, 'n2');
    return {
      n1: 1,
      n2,
      m,
      q: normalizeConfidentialBigInt(q, 'q'),
      beta: normalizeConfidentialBigInt(beta, 'beta'),
    };
  }

  export function validScalarParams(params: BigIntScalarCommitParams): boolean {
    return (
      params.n1 === 1 &&
      Number.isSafeInteger(params.n2) &&
      params.n2 > 0 &&
      Number.isSafeInteger(params.m) &&
      params.m > 0 &&
      params.q > 1n &&
      params.beta > 0n
    );
  }

  export function validCommitKey(params: BigIntScalarCommitParams, ck: BigIntMatrixInput): boolean {
    if (!validScalarParams(params)) {
      return false;
    }
    try {
      const key = normalizeBigIntMatrix(ck, 'ck');
      return key.length === params.m && key.every((row) => row.length === params.n1 + params.n2);
    } catch {
      return false;
    }
  }

  export function randCommitKey(params: BigIntScalarCommitParams, ck: BigIntMatrixInput): BigIntMatrix {
    if (!validCommitKey(params, ck)) {
      throw new Error('invalid commitment key');
    }
    return normalizeBigIntMatrix(ck, 'ck').map((row) => row.slice(params.n1));
  }

  export function randCommit(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    r: BigIntVecInput
  ): BigIntVec {
    const randomness = normalizeBigIntVec(r, 'r');
    if (!validScalarParams(params) || randomness.length !== params.n2) {
      throw new Error('invalid balance commitment input');
    }
    return bigintMatVecMultMod(randCommitKey(params, ck), randomness, params.q);
  }

  export function validWitness(params: BigIntScalarCommitParams, r: BigIntVecInput): boolean {
    try {
      const witness = normalizeBigIntVec(r, 'r');
      return (
        validScalarParams(params) &&
        witness.length === params.n2 &&
        bigintAllBounded(witness, 4n * params.beta)
      );
    } catch {
      return false;
    }
  }

  export function validMask(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    y: BigIntVecInput
  ): boolean {
    try {
      const bound = normalizeConfidentialBigInt(gamma, 'gamma');
      const mask = normalizeBigIntVec(y, 'y');
      return validScalarParams(params) && mask.length === params.n2 && bigintAllBounded(mask, bound);
    } catch {
      return false;
    }
  }

  export function validResponse(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    challenge: number,
    z: BigIntVecInput
  ): boolean {
    try {
      if (challenge !== 0 && challenge !== 1) {
        return false;
      }
      const bound = normalizeConfidentialBigInt(gamma, 'gamma') + BigInt(challenge) * 4n * params.beta;
      const response = normalizeBigIntVec(z, 'z');
      return (
        validScalarParams(params) &&
        response.length === params.n2 &&
        bigintAllBounded(response, bound)
      );
    } catch {
      return false;
    }
  }

  export function relation(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    r: BigIntVecInput
  ): boolean {
    try {
      const commitment = normalizeBigIntVec(c, 'c');
      return (
        commitment.length === params.m &&
        validCommitKey(params, ck) &&
        validWitness(params, r) &&
        randCommit(params, ck, r).every((value, index) => value === commitment[index])
      );
    } catch {
      return false;
    }
  }

  export function sigmaCommit(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    y: BigIntVecInput
  ): BigIntVec {
    return randCommit(params, ck, y);
  }

  export function sigmaRespond(r: BigIntVecInput, y: BigIntVecInput, challenge: number): BigIntVec {
    if (challenge !== 0 && challenge !== 1) {
      throw new Error('challenge must be binary');
    }
    const witness = normalizeBigIntVec(r, 'r');
    const mask = normalizeBigIntVec(y, 'y');
    return bigintVecAdd(mask, bigintScalarMult(BigInt(challenge), witness));
  }

  export function fsRounds(): number {
    return CT_FS_ROUNDS;
  }

  export function fsFields(
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    as: BigIntMatrixInput
  ): BigIntVec {
    const key = normalizeBigIntMatrix(ck, 'ck');
    const commitment = normalizeBigIntVec(c, 'c');
    const announcements = normalizeBigIntMatrix(as, 'as');
    return [bigintMatrixSum(key), bigintSum(commitment), bigintMatrixSum(announcements)];
  }

  export function canonicalChallenge(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    a: BigIntVecInput
  ): number {
    if (!validScalarParams(params)) {
      throw new Error('invalid scalar commitment parameters');
    }
    return binaryFsChallenge(CT_FS_BALANCE_DOMAIN, fsFields(ck, c, [a]), 0);
  }

  export function fsChallenges(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    as: BigIntMatrixInput,
    rounds: number = CT_FS_ROUNDS
  ): number[] {
    assertSafeArrayLength(rounds, 'rounds');
    if (!validScalarParams(params)) {
      throw new Error('invalid scalar commitment parameters');
    }
    const fields = fsFields(ck, c, as);
    return Array.from({ length: rounds }, (_, round) =>
      binaryFsChallenge(CT_FS_BALANCE_DOMAIN, fields, round)
    );
  }

  export function sigmaVerify(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    a: BigIntVecInput,
    challenge: number,
    z: BigIntVecInput
  ): boolean {
    try {
      const commitment = normalizeBigIntVec(c, 'c');
      const announcement = normalizeBigIntVec(a, 'a');
      const responseCommitment = randCommit(params, ck, z);
      const expected = bigintVecMod(
        bigintVecAdd(announcement, bigintScalarMult(BigInt(challenge), commitment)),
        params.q
      );
      return (
        commitment.length === params.m &&
        announcement.length === params.m &&
        validResponse(params, gamma, challenge, z) &&
        responseCommitment.every((value, index) => value === expected[index])
      );
    } catch {
      return false;
    }
  }

  export function fsProve(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    r: BigIntVecInput,
    ys: BigIntMatrixInput
  ): BigIntBalanceProof | null {
    try {
      const masks = normalizeBigIntMatrix(ys, 'ys');
      if (
        masks.length !== CT_FS_ROUNDS ||
        !relation(params, ck, c, r) ||
        !masks.every((mask) => validMask(params, gamma, mask))
      ) {
        return null;
      }
      const as = masks.map((mask) => sigmaCommit(params, ck, mask));
      const challenges = fsChallenges(params, ck, c, as);
      const zs = masks.map((mask, index) => sigmaRespond(r, mask, challenges[index]));
      if (!zs.every((response, index) => validResponse(params, gamma, challenges[index], response))) {
        return null;
      }
      return { as, zs };
    } catch {
      return null;
    }
  }

  export function fsVerify(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    proof: BigIntBalanceProof
  ): boolean {
    try {
      const as = normalizeBigIntMatrix(proof.as, 'proof.as');
      const zs = normalizeBigIntMatrix(proof.zs, 'proof.zs');
      if (
        as.length !== CT_FS_ROUNDS ||
        zs.length !== CT_FS_ROUNDS ||
        !validCommitKey(params, ck)
      ) {
        return false;
      }
      const challenges = fsChallenges(params, ck, c, as);
      return as.every((announcement, index) =>
        sigmaVerify(params, gamma, ck, c, announcement, challenges[index], zs[index])
      );
    } catch {
      return false;
    }
  }
}

/**
 * BigInt reference implementation for the confidential-range proof slice.
 *
 * This exists to exercise widened q83-style arithmetic and transcript encoding
 * before the production OCaml/Haskell/TypeScript proof APIs are fully migrated
 * to canonical bignum values.
 */
export namespace ConfidentialRangeBigInt {
  export const transcriptDst = CT_FS_DST;
  export const fsDomain = CT_FS_RANGE_DOMAIN;
  export const fieldEncoding = CT_BIGNUM_ENCODING;

  type OpeningInput = {
    msg: BigIntVecInput;
    rand: BigIntVecInput;
  };

  function normalizeOpening(opening: OpeningInput, label: string): BigIntCommitOpening {
    return {
      msg: normalizeBigIntVec(opening.msg, `${label}.msg`),
      rand: normalizeBigIntVec(opening.rand, `${label}.rand`),
    };
  }

  function validOpening(params: BigIntScalarCommitParams, opening: OpeningInput): boolean {
    try {
      const normalized = normalizeOpening(opening, 'opening');
      return (
        ConfidentialBalanceBigInt.validScalarParams(params) &&
        normalized.msg.length === params.n1 &&
        normalized.rand.length === params.n2 &&
        bigintAllBounded(normalized.msg, params.beta) &&
        bigintAllBounded(normalized.rand, params.beta)
      );
    } catch {
      return false;
    }
  }

  function commit(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    opening: OpeningInput
  ): BigIntVec {
    const normalized = normalizeOpening(opening, 'opening');
    if (!validOpening(params, normalized) || !ConfidentialBalanceBigInt.validCommitKey(params, ck)) {
      throw new Error('invalid commitment input');
    }
    return bigintMatVecMultMod(
      normalizeBigIntMatrix(ck, 'ck'),
      [...normalized.msg, ...normalized.rand],
      params.q
    );
  }

  function zeroOpening(params: BigIntScalarCommitParams): BigIntCommitOpening {
    return {
      msg: Array.from({ length: params.n1 }, () => 0n),
      rand: Array.from({ length: params.n2 }, () => 0n),
    };
  }

  export function oneOpening(params: BigIntScalarCommitParams): BigIntCommitOpening {
    return {
      msg: [1n],
      rand: Array.from({ length: params.n2 }, () => 0n),
    };
  }

  function openingAdd(left: BigIntCommitOpening, right: BigIntCommitOpening): BigIntCommitOpening {
    return {
      msg: bigintVecAdd(left.msg, right.msg),
      rand: bigintVecAdd(left.rand, right.rand),
    };
  }

  function openingSub(left: BigIntCommitOpening, right: BigIntCommitOpening): BigIntCommitOpening {
    return {
      msg: bigintVecAdd(left.msg, bigintScalarMult(-1n, right.msg)),
      rand: bigintVecAdd(left.rand, bigintScalarMult(-1n, right.rand)),
    };
  }

  function openingScale(scalar: bigint, opening: BigIntCommitOpening): BigIntCommitOpening {
    return {
      msg: bigintScalarMult(scalar, opening.msg),
      rand: bigintScalarMult(scalar, opening.rand),
    };
  }

  function weightedOpening(
    params: BigIntScalarCommitParams,
    base: bigint,
    openings: readonly OpeningInput[]
  ): BigIntCommitOpening {
    let acc = zeroOpening(params);
    for (let index = openings.length - 1; index >= 0; index -= 1) {
      acc = openingAdd(normalizeOpening(openings[index], `openings[${index}]`), openingScale(base, acc));
    }
    return acc;
  }

  function weightedCommitment(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    base: bigint,
    commitments: BigIntMatrixInput
  ): BigIntVec {
    const rows = normalizeBigIntMatrix(commitments, 'commitments');
    let acc = ConfidentialBalanceBigInt.randCommit(params, ck, Array.from({ length: params.n2 }, () => 0n));
    for (let index = rows.length - 1; index >= 0; index -= 1) {
      acc = bigintVecMod(bigintVecAdd(rows[index], bigintScalarMult(base, acc)), params.q);
    }
    return acc;
  }

  function amountOfOpening(opening: OpeningInput): bigint {
    const normalized = normalizeOpening(opening, 'opening');
    if (normalized.msg.length !== 1) {
      throw new Error('amount opening must have one message coordinate');
    }
    return normalized.msg[0];
  }

  function validBitOpening(params: BigIntScalarCommitParams, opening: OpeningInput): boolean {
    try {
      const normalized = normalizeOpening(opening, 'opening');
      return validOpening(params, normalized) && bigintAllBounded(normalized.msg, 1n);
    } catch {
      return false;
    }
  }

  function bitPairRelation(
    params: BigIntScalarCommitParams,
    bitOpening: OpeningInput,
    compOpening: OpeningInput
  ): boolean {
    try {
      return (
        validBitOpening(params, bitOpening) &&
        validBitOpening(params, compOpening) &&
        amountOfOpening(bitOpening) + amountOfOpening(compOpening) === 1n
      );
    } catch {
      return false;
    }
  }

  function recomposeBits(bitOpenings: readonly OpeningInput[]): bigint {
    return bitOpenings.reduce(
      (acc, opening, index) => acc + amountOfOpening(opening) * (1n << BigInt(index)),
      0n
    );
  }

  export function amountCommitment(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    cBits: BigIntMatrixInput
  ): BigIntVec {
    const amount = normalizeBigIntVec(cAmount, 'cAmount');
    return bigintVecMod(
      bigintVecAdd(amount, bigintScalarMult(-1n, weightedCommitment(params, ck, 2n, cBits))),
      params.q
    );
  }

  export function pairCommitment(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cBit: BigIntVecInput,
    cComp: BigIntVecInput
  ): BigIntVec {
    return bigintVecMod(
      bigintVecAdd(
        bigintVecAdd(normalizeBigIntVec(cBit, 'cBit'), normalizeBigIntVec(cComp, 'cComp')),
        bigintScalarMult(-1n, commit(params, ck, oneOpening(params)))
      ),
      params.q
    );
  }

  function pairCommitments(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cBits: BigIntMatrixInput,
    cComps: BigIntMatrixInput
  ): BigIntMatrix {
    const bits = normalizeBigIntMatrix(cBits, 'cBits');
    const comps = normalizeBigIntMatrix(cComps, 'cComps');
    if (bits.length !== comps.length) {
      throw new Error('bit and complement commitments must have the same length');
    }
    return bits.map((bit, index) => pairCommitment(params, ck, bit, comps[index]));
  }

  function rangeAmountOpening(
    params: BigIntScalarCommitParams,
    amountOpening: OpeningInput,
    bitOpenings: readonly OpeningInput[]
  ): BigIntCommitOpening {
    return openingSub(
      normalizeOpening(amountOpening, 'amountOpening'),
      weightedOpening(params, 2n, bitOpenings)
    );
  }

  function rangePairOpening(
    params: BigIntScalarCommitParams,
    bitOpening: OpeningInput,
    compOpening: OpeningInput
  ): BigIntCommitOpening {
    return openingSub(
      openingAdd(
        normalizeOpening(bitOpening, 'bitOpening'),
        normalizeOpening(compOpening, 'compOpening')
      ),
      oneOpening(params)
    );
  }

  function rangePairOpenings(
    params: BigIntScalarCommitParams,
    bitOpenings: readonly OpeningInput[],
    compOpenings: readonly OpeningInput[]
  ): BigIntCommitOpening[] {
    if (bitOpenings.length !== compOpenings.length) {
      throw new Error('bit and complement openings must have the same length');
    }
    return bitOpenings.map((bitOpening, index) =>
      rangePairOpening(params, bitOpening, compOpenings[index])
    );
  }

  export function amountWitnessBound(params: BigIntScalarCommitParams, k: number): bigint {
    assertSafeArrayLength(k, 'k');
    return (1n << BigInt(k)) * params.beta;
  }

  export function pairWitnessBound(params: BigIntScalarCommitParams): bigint {
    return 2n * params.beta;
  }

  function validAmountWitness(
    params: BigIntScalarCommitParams,
    k: number,
    r: BigIntVecInput
  ): boolean {
    try {
      const witness = normalizeBigIntVec(r, 'r');
      return (
        witness.length === params.n2 &&
        bigintAllBounded(witness, amountWitnessBound(params, k))
      );
    } catch {
      return false;
    }
  }

  function validPairWitness(params: BigIntScalarCommitParams, r: BigIntVecInput): boolean {
    try {
      const witness = normalizeBigIntVec(r, 'r');
      return witness.length === params.n2 && bigintAllBounded(witness, pairWitnessBound(params));
    } catch {
      return false;
    }
  }

  function validMask(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    y: BigIntVecInput
  ): boolean {
    try {
      const bound = normalizeConfidentialBigInt(gamma, 'gamma');
      const mask = normalizeBigIntVec(y, 'y');
      return mask.length === params.n2 && bigintAllBounded(mask, bound);
    } catch {
      return false;
    }
  }

  export function amountResponseBound(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    challenge: number
  ): bigint {
    if (challenge !== 0 && challenge !== 1) {
      throw new Error('challenge must be binary');
    }
    return normalizeConfidentialBigInt(gamma, 'gamma') + BigInt(challenge) * amountWitnessBound(params, k);
  }

  export function pairResponseBound(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    challenge: number
  ): bigint {
    if (challenge !== 0 && challenge !== 1) {
      throw new Error('challenge must be binary');
    }
    return normalizeConfidentialBigInt(gamma, 'gamma') + BigInt(challenge) * pairWitnessBound(params);
  }

  function validAmountResponse(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    challenge: number,
    z: BigIntVecInput
  ): boolean {
    try {
      const response = normalizeBigIntVec(z, 'z');
      return (
        response.length === params.n2 &&
        bigintAllBounded(response, amountResponseBound(params, gamma, k, challenge))
      );
    } catch {
      return false;
    }
  }

  function validPairResponse(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    challenge: number,
    z: BigIntVecInput
  ): boolean {
    try {
      const response = normalizeBigIntVec(z, 'z');
      return (
        response.length === params.n2 &&
        bigintAllBounded(response, pairResponseBound(params, gamma, challenge))
      );
    } catch {
      return false;
    }
  }

  function rangeRelation(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    amountOpening: OpeningInput,
    bitOpenings: readonly OpeningInput[],
    compOpenings: readonly OpeningInput[]
  ): boolean {
    try {
      const amount = normalizeBigIntVec(cAmount, 'cAmount');
      return (
        ConfidentialBalanceBigInt.validScalarParams(params) &&
        ConfidentialBalanceBigInt.validCommitKey(params, ck) &&
        commit(params, ck, amountOpening).every((value, index) => value === amount[index]) &&
        bitOpenings.length === compOpenings.length &&
        bitOpenings.every((bitOpening, index) =>
          bitPairRelation(params, bitOpening, compOpenings[index])
        ) &&
        amountOfOpening(amountOpening) === recomposeBits(bitOpenings)
      );
    } catch {
      return false;
    }
  }

  export function fsRounds(): number {
    return CT_FS_ROUNDS;
  }

  export function fsFields(
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    cBits: BigIntMatrixInput,
    cComps: BigIntMatrixInput,
    aAmounts: BigIntMatrixInput,
    aPairss: readonly BigIntMatrixInput[]
  ): BigIntVec {
    return [
      bigintMatrixSum(normalizeBigIntMatrix(ck, 'ck')),
      bigintSum(normalizeBigIntVec(cAmount, 'cAmount')),
      bigintMatrixSum(normalizeBigIntMatrix(cBits, 'cBits')),
      bigintMatrixSum(normalizeBigIntMatrix(cComps, 'cComps')),
      bigintMatrixSum(normalizeBigIntMatrix(aAmounts, 'aAmounts')),
      aPairss.reduce((acc, rows, index) =>
        acc + bigintMatrixSum(normalizeBigIntMatrix(rows, `aPairss[${index}]`)), 0n),
    ];
  }

  export function fsChallenges(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    cBits: BigIntMatrixInput,
    cComps: BigIntMatrixInput,
    aAmounts: BigIntMatrixInput,
    aPairss: readonly BigIntMatrixInput[],
    rounds: number = CT_FS_ROUNDS
  ): number[] {
    assertSafeArrayLength(rounds, 'rounds');
    if (!ConfidentialBalanceBigInt.validScalarParams(params)) {
      throw new Error('invalid scalar commitment parameters');
    }
    const fields = fsFields(ck, cAmount, cBits, cComps, aAmounts, aPairss);
    return Array.from({ length: rounds }, (_, round) =>
      binaryFsChallenge(CT_FS_RANGE_DOMAIN, fields, round)
    );
  }

  function sigmaVerify(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    c: BigIntVecInput,
    a: BigIntVecInput,
    challenge: number,
    z: BigIntVecInput,
    validResponse: (challenge: number, z: BigIntVecInput) => boolean
  ): boolean {
    try {
      const commitment = normalizeBigIntVec(c, 'c');
      const announcement = normalizeBigIntVec(a, 'a');
      const responseCommitment = ConfidentialBalanceBigInt.randCommit(params, ck, z);
      const expected = bigintVecMod(
        bigintVecAdd(announcement, bigintScalarMult(BigInt(challenge), commitment)),
        params.q
      );
      return (
        commitment.length === params.m &&
        announcement.length === params.m &&
        (challenge === 0 || challenge === 1) &&
        validResponse(challenge, z) &&
        responseCommitment.every((value, index) => value === expected[index])
      );
    } catch {
      return false;
    }
  }

  export function fsProve(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    amountOpening: OpeningInput,
    bitOpenings: readonly OpeningInput[],
    compOpenings: readonly OpeningInput[],
    yAmounts: BigIntMatrixInput,
    yPairss: readonly BigIntMatrixInput[]
  ): BigIntRangeProof | null {
    try {
      assertSafeArrayLength(k, 'k');
      const amountMasks = normalizeBigIntMatrix(yAmounts, 'yAmounts');
      const pairMasks = yPairss.map((rows, index) => normalizeBigIntMatrix(rows, `yPairss[${index}]`));
      if (
        bitOpenings.length !== k ||
        compOpenings.length !== k ||
        amountMasks.length !== CT_FS_ROUNDS ||
        pairMasks.length !== CT_FS_ROUNDS ||
        !rangeRelation(params, ck, cAmount, amountOpening, bitOpenings, compOpenings) ||
        !amountMasks.every((mask) => validMask(params, gamma, mask)) ||
        !pairMasks.every((roundMasks) =>
          roundMasks.length === k && roundMasks.every((mask) => validMask(params, gamma, mask))
        )
      ) {
        return null;
      }

      const bits = bitOpenings.map((opening, index) => commit(params, ck, normalizeOpening(opening, `bitOpenings[${index}]`)));
      const comps = compOpenings.map((opening, index) => commit(params, ck, normalizeOpening(opening, `compOpenings[${index}]`)));
      const amountWitness = rangeAmountOpening(params, amountOpening, bitOpenings).rand;
      const pairWitnesses = rangePairOpenings(params, bitOpenings, compOpenings).map((opening) => opening.rand);
      if (
        !validAmountWitness(params, k, amountWitness) ||
        !pairWitnesses.every((witness) => validPairWitness(params, witness))
      ) {
        return null;
      }

      const amountAs = amountMasks.map((mask) => ConfidentialBalanceBigInt.sigmaCommit(params, ck, mask));
      const pairAss = pairMasks.map((roundMasks) =>
        roundMasks.map((mask) => ConfidentialBalanceBigInt.sigmaCommit(params, ck, mask))
      );
      const challenges = fsChallenges(params, ck, cAmount, bits, comps, amountAs, pairAss);
      const amountZs = amountMasks.map((mask, index) =>
        ConfidentialBalanceBigInt.sigmaRespond(amountWitness, mask, challenges[index])
      );
      const pairZss = pairMasks.map((roundMasks, round) =>
        roundMasks.map((mask, index) =>
          ConfidentialBalanceBigInt.sigmaRespond(pairWitnesses[index], mask, challenges[round])
        )
      );

      if (
        !amountZs.every((response, index) =>
          validAmountResponse(params, gamma, k, challenges[index], response)
        ) ||
        !pairZss.every((roundResponses, round) =>
          roundResponses.every((response) =>
            validPairResponse(params, gamma, challenges[round], response)
          )
        )
      ) {
        return null;
      }

      return { bits, comps, amountAs, amountZs, pairAss, pairZss };
    } catch {
      return null;
    }
  }

  export function fsVerify(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    cAmount: BigIntVecInput,
    proof: BigIntRangeProof
  ): boolean {
    try {
      assertSafeArrayLength(k, 'k');
      const bits = normalizeBigIntMatrix(proof.bits, 'proof.bits');
      const comps = normalizeBigIntMatrix(proof.comps, 'proof.comps');
      const amountAs = normalizeBigIntMatrix(proof.amountAs, 'proof.amountAs');
      const amountZs = normalizeBigIntMatrix(proof.amountZs, 'proof.amountZs');
      const pairAss = proof.pairAss.map((rows, index) => normalizeBigIntMatrix(rows, `proof.pairAss[${index}]`));
      const pairZss = proof.pairZss.map((rows, index) => normalizeBigIntMatrix(rows, `proof.pairZss[${index}]`));
      if (
        bits.length !== k ||
        comps.length !== k ||
        amountAs.length !== CT_FS_ROUNDS ||
        amountZs.length !== CT_FS_ROUNDS ||
        pairAss.length !== CT_FS_ROUNDS ||
        pairZss.length !== CT_FS_ROUNDS ||
        !ConfidentialBalanceBigInt.validCommitKey(params, ck)
      ) {
        return false;
      }
      const amountCommit = amountCommitment(params, ck, cAmount, bits);
      const pairs = pairCommitments(params, ck, bits, comps);
      const challenges = fsChallenges(params, ck, cAmount, bits, comps, amountAs, pairAss);
      return amountAs.every((announcement, index) =>
        sigmaVerify(
          params,
          gamma,
          ck,
          amountCommit,
          announcement,
          challenges[index],
          amountZs[index],
          (challenge, response) => validAmountResponse(params, gamma, k, challenge, response)
        )
      ) && pairAss.every((roundAnnouncements, round) =>
        roundAnnouncements.length === k &&
        pairZss[round].length === k &&
        roundAnnouncements.every((announcement, index) =>
          sigmaVerify(
            params,
            gamma,
            ck,
            pairs[index],
            announcement,
            challenges[round],
            pairZss[round][index],
            (challenge, response) => validPairResponse(params, gamma, challenge, response)
          )
        )
      );
    } catch {
      return false;
    }
  }
}

/**
 * BigInt reference implementation for the confidential-nullifier proof slice.
 *
 * This tracks the q83 widened arithmetic path for note nullifiers. It is a
 * reference/preview surface until every production proof API and transaction
 * field has canonical bignum integration.
 */
export namespace ConfidentialNullifierBigInt {
  export const transcriptDst = CT_FS_DST;
  export const fsDomain = CT_FS_NULLIFIER_DOMAIN;
  export const fieldEncoding = CT_BIGNUM_ENCODING;

  type OpeningInput = {
    msg: BigIntVecInput;
    rand: BigIntVecInput;
  };

  function normalizeOpening(opening: OpeningInput, label: string): BigIntCommitOpening {
    return {
      msg: normalizeBigIntVec(opening.msg, `${label}.msg`),
      rand: normalizeBigIntVec(opening.rand, `${label}.rand`),
    };
  }

  function validOpening(params: BigIntScalarCommitParams, opening: OpeningInput): boolean {
    try {
      const normalized = normalizeOpening(opening, 'opening');
      return (
        validOpeningShape(params, normalized) &&
        bigintAllBounded(normalized.msg, params.beta) &&
        bigintAllBounded(normalized.rand, params.beta)
      );
    } catch {
      return false;
    }
  }

  function validOpeningShape(params: BigIntScalarCommitParams, opening: OpeningInput): boolean {
    try {
      const normalized = normalizeOpening(opening, 'opening');
      return (
        ConfidentialBalanceBigInt.validScalarParams(params) &&
        normalized.msg.length === params.n1 &&
        normalized.rand.length === params.n2
      );
    } catch {
      return false;
    }
  }

  function commit(
    params: BigIntScalarCommitParams,
    key: BigIntMatrixInput,
    opening: OpeningInput
  ): BigIntVec {
    const normalized = normalizeOpening(opening, 'opening');
    if (!validOpeningShape(params, normalized) || !ConfidentialBalanceBigInt.validCommitKey(params, key)) {
      throw new Error('invalid nullifier commitment input');
    }
    return bigintMatVecMultMod(
      normalizeBigIntMatrix(key, 'key'),
      [...normalized.msg, ...normalized.rand],
      params.q
    );
  }

  export function nullifier(
    params: BigIntScalarCommitParams,
    nk: BigIntMatrixInput,
    opening: OpeningInput
  ): BigIntVec {
    return commit(params, nk, opening);
  }

  function validMask(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    y: OpeningInput
  ): boolean {
    try {
      const bound = normalizeConfidentialBigInt(gamma, 'gamma');
      const mask = normalizeOpening(y, 'y');
      return (
        ConfidentialBalanceBigInt.validScalarParams(params) &&
        mask.msg.length === params.n1 &&
        mask.rand.length === params.n2 &&
        bigintAllBounded(mask.msg, bound) &&
        bigintAllBounded(mask.rand, bound)
      );
    } catch {
      return false;
    }
  }

  export function responseBound(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    challenge: number
  ): bigint {
    if (challenge !== 0 && challenge !== 1) {
      throw new Error('challenge must be binary');
    }
    return normalizeConfidentialBigInt(gamma, 'gamma') + BigInt(challenge) * params.beta;
  }

  function validResponse(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    challenge: number,
    z: OpeningInput
  ): boolean {
    try {
      const response = normalizeOpening(z, 'z');
      const bound = responseBound(params, gamma, challenge);
      return (
        response.msg.length === params.n1 &&
        response.rand.length === params.n2 &&
        bigintAllBounded(response.msg, bound) &&
        bigintAllBounded(response.rand, bound)
      );
    } catch {
      return false;
    }
  }

  function sigmaRespond(
    op: BigIntCommitOpening,
    y: BigIntCommitOpening,
    challenge: number
  ): BigIntCommitOpening {
    return {
      msg: bigintVecAdd(y.msg, bigintScalarMult(BigInt(challenge), op.msg)),
      rand: bigintVecAdd(y.rand, bigintScalarMult(BigInt(challenge), op.rand)),
    };
  }

  function relation(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    c: BigIntVecInput,
    nf: BigIntVecInput,
    opening: OpeningInput
  ): boolean {
    try {
      const commitment = normalizeBigIntVec(c, 'c');
      const nullifierValue = normalizeBigIntVec(nf, 'nf');
      const cComputed = commit(params, ck, opening);
      const nfComputed = nullifier(params, nk, opening);
      return (
        commitment.length === params.m &&
        nullifierValue.length === params.m &&
        cComputed.every((value, index) => value === commitment[index]) &&
        nfComputed.every((value, index) => value === nullifierValue[index])
      );
    } catch {
      return false;
    }
  }

  export function fsRounds(): number {
    return CT_FS_ROUNDS;
  }

  export function fsFields(
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    c: BigIntVecInput,
    nf: BigIntVecInput,
    aCommits: BigIntMatrixInput,
    aNullifiers: BigIntMatrixInput
  ): BigIntVec {
    return [
      bigintMatrixSum(normalizeBigIntMatrix(ck, 'ck')),
      bigintMatrixSum(normalizeBigIntMatrix(nk, 'nk')),
      bigintSum(normalizeBigIntVec(c, 'c')),
      bigintSum(normalizeBigIntVec(nf, 'nf')),
      bigintMatrixSum(normalizeBigIntMatrix(aCommits, 'aCommits')),
      bigintMatrixSum(normalizeBigIntMatrix(aNullifiers, 'aNullifiers')),
    ];
  }

  export function fsChallenges(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    c: BigIntVecInput,
    nf: BigIntVecInput,
    aCommits: BigIntMatrixInput,
    aNullifiers: BigIntMatrixInput,
    rounds: number = CT_FS_ROUNDS
  ): number[] {
    assertSafeArrayLength(rounds, 'rounds');
    if (!ConfidentialBalanceBigInt.validScalarParams(params)) {
      throw new Error('invalid scalar commitment parameters');
    }
    const fields = fsFields(ck, nk, c, nf, aCommits, aNullifiers);
    return Array.from({ length: rounds }, (_, round) =>
      binaryFsChallenge(CT_FS_NULLIFIER_DOMAIN, fields, round)
    );
  }

  export function fsProve(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    c: BigIntVecInput,
    nf: BigIntVecInput,
    opening: OpeningInput,
    ys: readonly OpeningInput[]
  ): BigIntNullifierProof | null {
    try {
      const normalizedOpening = normalizeOpening(opening, 'opening');
      const masks = ys.map((mask, index) => normalizeOpening(mask, `ys[${index}]`));
      if (
        masks.length !== CT_FS_ROUNDS ||
        !ConfidentialBalanceBigInt.validCommitKey(params, ck) ||
        !ConfidentialBalanceBigInt.validCommitKey(params, nk) ||
        !validOpening(params, normalizedOpening) ||
        !relation(params, ck, nk, c, nf, normalizedOpening) ||
        !masks.every((mask) => validMask(params, gamma, mask))
      ) {
        return null;
      }

      const aCommits = masks.map((mask) => commit(params, ck, mask));
      const aNullifiers = masks.map((mask) => nullifier(params, nk, mask));
      const challenges = fsChallenges(params, ck, nk, c, nf, aCommits, aNullifiers);
      const zs = masks.map((mask, index) => sigmaRespond(normalizedOpening, mask, challenges[index]));
      if (!zs.every((response, index) => validResponse(params, gamma, challenges[index], response))) {
        return null;
      }
      return {
        aCommits,
        aNullifiers,
        zMsgs: zs.map((response) => response.msg),
        zRands: zs.map((response) => response.rand),
      };
    } catch {
      return null;
    }
  }

  export function fsVerify(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    c: BigIntVecInput,
    nf: BigIntVecInput,
    proof: BigIntNullifierProof
  ): boolean {
    try {
      const aCommits = normalizeBigIntMatrix(proof.aCommits, 'proof.aCommits');
      const aNullifiers = normalizeBigIntMatrix(proof.aNullifiers, 'proof.aNullifiers');
      const zMsgs = normalizeBigIntMatrix(proof.zMsgs, 'proof.zMsgs');
      const zRands = normalizeBigIntMatrix(proof.zRands, 'proof.zRands');
      if (
        aCommits.length !== CT_FS_ROUNDS ||
        aNullifiers.length !== CT_FS_ROUNDS ||
        zMsgs.length !== CT_FS_ROUNDS ||
        zRands.length !== CT_FS_ROUNDS ||
        !ConfidentialBalanceBigInt.validCommitKey(params, ck) ||
        !ConfidentialBalanceBigInt.validCommitKey(params, nk)
      ) {
        return false;
      }
      const commitment = normalizeBigIntVec(c, 'c');
      const nullifierValue = normalizeBigIntVec(nf, 'nf');
      if (commitment.length !== params.m || nullifierValue.length !== params.m) {
        return false;
      }
      const challenges = fsChallenges(params, ck, nk, commitment, nullifierValue, aCommits, aNullifiers);
      return aCommits.every((aCommit, index) => {
        const z = { msg: zMsgs[index], rand: zRands[index] };
        const challenge = challenges[index];
        const expectedCommit = bigintVecMod(
          bigintVecAdd(aCommit, bigintScalarMult(BigInt(challenge), commitment)),
          params.q
        );
        const expectedNullifier = bigintVecMod(
          bigintVecAdd(aNullifiers[index], bigintScalarMult(BigInt(challenge), nullifierValue)),
          params.q
        );
        const responseCommit = commit(params, ck, z);
        const responseNullifier = nullifier(params, nk, z);
        return (
          validResponse(params, gamma, challenge, z) &&
          responseCommit.every((value, coord) => value === expectedCommit[coord]) &&
          responseNullifier.every((value, coord) => value === expectedNullifier[coord])
        );
      });
    } catch {
      return false;
    }
  }
}

/**
 * Confidential-range proof helpers over SIS commitments.
 *
 * This extends the confidential-balance slice with explicit bit-decomposition
 * commitments so callers can prove a committed amount lies in `[0, 2^k)`.
 */
export namespace ConfidentialRange {
  export function oneOpening(params: ScalarCommitParams): CommitOpening {
    return Isabella.crOneOpening(params);
  }

  export function validBitOpening(params: ScalarCommitParams, opening: CommitOpening): boolean {
    return Isabella.crValidBitOpening(params, opening);
  }

  export function bitPairRelation(
    params: ScalarCommitParams,
    bitOpening: CommitOpening,
    compOpening: CommitOpening
  ): boolean {
    return Isabella.crBitPairRelation(params, bitOpening, compOpening);
  }

  export function weightedCommitment(
    params: ScalarCommitParams,
    ck: IntMatrix,
    bitCommitments: IntMatrix
  ): IntVec {
    return normalizeVec(Isabella.crWeightedCommitment(params, ck, bitCommitments));
  }

  export function amountCommitment(
    params: ScalarCommitParams,
    ck: IntMatrix,
    cAmount: IntVec,
    cBits: IntMatrix
  ): IntVec {
    return normalizeVec(Isabella.crAmountCommitment(params, ck, cAmount, cBits));
  }

  export function pairCommitment(
    params: ScalarCommitParams,
    ck: IntMatrix,
    cBit: IntVec,
    cComp: IntVec
  ): IntVec {
    return normalizeVec(Isabella.crPairCommitment(params, ck, cBit, cComp));
  }

  export function amountWitnessBound(params: ScalarCommitParams, k: number): number {
    return Isabella.crAmountWitnessBound(params, k);
  }

  export function pairWitnessBound(params: ScalarCommitParams): number {
    return Isabella.crPairWitnessBound(params);
  }

  export function validAmountWitness(params: ScalarCommitParams, k: number, r: IntVec): boolean {
    return Isabella.crValidAmountWitness(params, k, r);
  }

  export function validPairWitness(params: ScalarCommitParams, r: IntVec): boolean {
    return Isabella.crValidPairWitness(params, r);
  }

  export function validMask(params: ScalarCommitParams, gamma: number, y: IntVec): boolean {
    return Isabella.crValidMask(params, gamma, y);
  }

  export function validAmountResponse(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    challenge: number,
    z: IntVec
  ): boolean {
    return Isabella.crValidAmountResponse(params, gamma, k, challenge, z);
  }

  export function validPairResponse(
    params: ScalarCommitParams,
    gamma: number,
    challenge: number,
    z: IntVec
  ): boolean {
    return Isabella.crValidPairResponse(params, gamma, challenge, z);
  }

  export function canonicalChallenge(
    params: ScalarCommitParams,
    ck: IntMatrix,
    cAmount: IntVec,
    cBits: IntMatrix,
    cComps: IntMatrix,
    aAmounts: IntMatrix,
    aPairss: IntMatrix[]
  ): number {
    return Isabella.crCanonicalChallenge(params, ck, cAmount, cBits, cComps, aAmounts, aPairss);
  }

  export function fsProve(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    cAmount: IntVec,
    amountOpening: CommitOpening,
    bitOpenings: CommitOpening[],
    compOpenings: CommitOpening[],
    yAmounts: IntMatrix,
    yPairss: IntMatrix[]
  ): RangeProofLike | null {
    const bitMsgs = bitOpenings.map(op => op.msg);
    const bitRands = bitOpenings.map(op => op.rand);
    const compMsgs = compOpenings.map(op => op.msg);
    const compRands = compOpenings.map(op => op.rand);
    return normalizeRangeProof(
      Isabella.crFsProve(
        params,
        gamma,
        k,
        ck,
        cAmount,
        amountOpening,
        bitMsgs,
        bitRands,
        compMsgs,
        compRands,
        yAmounts,
        yPairss
      )
    );
  }

  export function fsVerify(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    cAmount: IntVec,
    proof: RangeProofLike
  ): boolean {
    try {
      const checkedProof = normalizeRangeProof(proof);
      return checkedProof !== null && Isabella.crFsVerify(params, gamma, k, ck, cAmount, checkedProof);
    } catch {
      return false;
    }
  }

  export function proofShape(proof: RangeProofLike): 'legacy' | 'rounds' | 'lists' {
    if ('rounds' in proof && Array.isArray(proof.rounds)) {
      return 'rounds';
    }
    if ('amountAs' in proof && 'amountZs' in proof && 'pairAss' in proof && 'pairZss' in proof) {
      return 'lists';
    }
    return 'legacy';
  }
}

/**
 * Cryptographic Merkle helpers for confidential note membership.
 *
 * This is the SHA3-256 runtime target for `Authenticated_Merkle.thy`. The
 * The compatibility transaction verifier still exposes the algebraic ledger
 * scaffold, while `ConfidentialTransaction.fsVerifyMerkle` uses these roots
 * for the cryptographic membership path.
 */
export namespace ConfidentialMerkle {
  export const dst = CT_MERKLE_DST;
  export const tags = CT_MERKLE_TAGS;

  export function encodeLeaf(commitment: IntVec): string {
    return merkleLeafPreimage(commitment).toString('hex');
  }

  export function encodeEmpty(width: number): string {
    return merkleEmptyPreimage(width).toString('hex');
  }

  export function encodeNode(left: MerkleDigest, right: MerkleDigest): string {
    return merkleNodePreimage(left, right).toString('hex');
  }

  export function leaf(commitment: IntVec): MerkleDigest {
    return merkleHashLeaf(commitment);
  }

  export function empty(width: number): MerkleDigest {
    return merkleHashEmpty(width);
  }

  export function node(left: MerkleDigest, right: MerkleDigest): MerkleDigest {
    return merkleHashNode(left, right);
  }

  export function root(commitments: IntMatrix, emptyWidth?: number): MerkleDigest {
    const width = emptyWidth ?? commitments[0]?.length ?? 0;
    assertNonNegativeSafeI64(width, 'emptyWidth');
    assertMerkleCommitmentWidths(commitments, width);
    if (commitments.length === 0) {
      return merkleHashEmpty(width);
    }
    let level = commitments.map(merkleHashLeaf);
    while (level.length > 1) {
      level = merkleCompressLevel(width, level);
    }
    return level[0];
  }

  export function pathRoot(
    commitment: IntVec,
    siblings: MerkleDigest[],
    directions: boolean[]
  ): MerkleDigest {
    if (siblings.length !== directions.length) {
      throw new Error('Merkle siblings and directions must have the same length');
    }
    let acc = merkleHashLeaf(commitment);
    for (let index = 0; index < siblings.length; index += 1) {
      const sibling = siblings[index];
      acc = directions[index]
        ? merkleHashNode(sibling, acc)
        : merkleHashNode(acc, sibling);
    }
    return acc;
  }

  export function membershipProve(
    commitments: IntMatrix,
    commitment: IntVec
  ): MerkleMembershipProof | null {
    const index = commitments.findIndex((entry) => JSON.stringify(entry) === JSON.stringify(commitment));
    if (index < 0) {
      return null;
    }

    const width = commitments[0]?.length ?? commitment.length;
    assertMerkleCommitmentWidths(commitments, width);
    let level = commitments.map(merkleHashLeaf);
    const siblings: MerkleDigest[] = [];
    const directions: boolean[] = [];
    let current = index;

    while (level.length > 1) {
      const isRight = current % 2 === 1;
      directions.push(isRight);
      siblings.push(
        isRight
          ? level[current - 1]
          : current + 1 < level.length
            ? level[current + 1]
            : merkleHashEmpty(width)
      );
      level = merkleCompressLevel(width, level);
      current = Math.floor(current / 2);
    }

    return {
      index,
      root: level[0],
      siblings,
      directions,
    };
  }

  export function membershipVerify(
    commitment: IntVec,
    proof: MerkleMembershipProof
  ): boolean {
    try {
      if (proof.siblings.length !== proof.directions.length) {
        return false;
      }
      if (
        JSON.stringify(proof.directions) !==
        JSON.stringify(merkleIndexDirections(proof.siblings.length, proof.index))
      ) {
        return false;
      }
      assertDigestHex(proof.root, 'root');
      return pathRoot(commitment, proof.siblings, proof.directions) === proof.root;
    } catch {
      return false;
    }
  }
}

/**
 * Versioned bignum Merkle helpers for widened confidential-note commitments.
 *
 * This namespace is intentionally separate from `ConfidentialMerkle`: it hashes
 * note commitments with the canonical confidential bignum codec and a distinct
 * DST so q83-compatible leaves do not silently collide with the existing
 * signed-64 transaction/Merkle encoding.
 */
export namespace ConfidentialMerkleBigInt {
  export const dst = CT_MERKLE_BIGNUM_DST;
  export const tags = CT_MERKLE_TAGS;
  export const integerEncoding = CT_BIGNUM_ENCODING;
  export const digestEncoding = 'len_i64_le || 32 raw digest bytes';

  export function encodeLeaf(commitment: BigIntVecInput): string {
    return merkleBignumLeafPreimage(commitment).toString('hex');
  }

  export function encodeEmpty(width: number): string {
    return merkleBignumEmptyPreimage(width).toString('hex');
  }

  export function encodeNode(left: MerkleDigest, right: MerkleDigest): string {
    return merkleBignumNodePreimage(left, right).toString('hex');
  }

  export function leaf(commitment: BigIntVecInput): MerkleDigest {
    return merkleBignumHashLeaf(commitment);
  }

  export function empty(width: number): MerkleDigest {
    return merkleBignumHashEmpty(width);
  }

  export function node(left: MerkleDigest, right: MerkleDigest): MerkleDigest {
    return merkleBignumHashNode(left, right);
  }

  export function root(commitments: readonly BigIntVecInput[], emptyWidth?: number): MerkleDigest {
    const width = emptyWidth ?? commitments[0]?.length ?? 0;
    assertNonNegativeSafeI64(width, 'emptyWidth');
    const normalized = assertBigIntMerkleCommitmentWidths(commitments, width);
    if (normalized.length === 0) {
      return merkleBignumHashEmpty(width);
    }
    let level = normalized.map(merkleBignumHashLeaf);
    while (level.length > 1) {
      level = merkleBignumCompressLevel(width, level);
    }
    return level[0];
  }

  export function pathRoot(
    commitment: BigIntVecInput,
    siblings: MerkleDigest[],
    directions: boolean[]
  ): MerkleDigest {
    if (siblings.length !== directions.length) {
      throw new Error('Merkle siblings and directions must have the same length');
    }
    let acc = merkleBignumHashLeaf(commitment);
    for (let index = 0; index < siblings.length; index += 1) {
      const sibling = siblings[index];
      acc = directions[index]
        ? merkleBignumHashNode(sibling, acc)
        : merkleBignumHashNode(acc, sibling);
    }
    return acc;
  }

  export function membershipProve(
    commitments: readonly BigIntVecInput[],
    commitment: BigIntVecInput
  ): MerkleMembershipProof | null {
    const normalizedCommitments = normalizeBigIntMatrix(commitments, 'commitments');
    const normalizedCommitment = normalizeBigIntVec(commitment, 'commitment');
    const index = normalizedCommitments.findIndex((entry) => sameBigIntVec(entry, normalizedCommitment));
    if (index < 0) {
      return null;
    }

    const width = normalizedCommitments[0]?.length ?? normalizedCommitment.length;
    const checkedCommitments = assertBigIntMerkleCommitmentWidths(normalizedCommitments, width);
    let level = checkedCommitments.map(merkleBignumHashLeaf);
    const siblings: MerkleDigest[] = [];
    const directions: boolean[] = [];
    let current = index;

    while (level.length > 1) {
      const isRight = current % 2 === 1;
      directions.push(isRight);
      siblings.push(
        isRight
          ? level[current - 1]
          : current + 1 < level.length
            ? level[current + 1]
            : merkleBignumHashEmpty(width)
      );
      level = merkleBignumCompressLevel(width, level);
      current = Math.floor(current / 2);
    }

    return {
      index,
      root: level[0],
      siblings,
      directions,
    };
  }

  export function membershipVerify(
    commitment: BigIntVecInput,
    proof: MerkleMembershipProof
  ): boolean {
    try {
      if (proof.siblings.length !== proof.directions.length) {
        return false;
      }
      if (
        JSON.stringify(proof.directions) !==
        JSON.stringify(merkleIndexDirections(proof.siblings.length, proof.index))
      ) {
        return false;
      }
      assertDigestHex(proof.root, 'root');
      return pathRoot(commitment, proof.siblings, proof.directions) === proof.root;
    } catch {
      return false;
    }
  }
}

/**
 * Confidential-transaction proof helpers over SIS commitments.
 *
 * This composes deterministic nullifiers, explicit membership proofs,
 * confidential-balance proofs, and output range proofs into a contract-friendly
 * 2-in/2-out transfer verifier.
 */
export namespace ConfidentialTransaction {
  export const transactionDst = CT_TRANSACTION_DST;
  export const transactionProtocolId = CT_TRANSACTION_PROTOCOL_ID;
  export const transactionTags = CT_TRANSACTION_TAGS;

  export function transactionContextPreimageHex(
    context: ConfidentialTransactionContext
  ): string {
    return transactionContextPreimage(context).toString('hex');
  }

  export function transactionContextDigest(
    context: ConfidentialTransactionContext
  ): MerkleDigest {
    return sha3Hex(transactionContextPreimage(context));
  }

  export function transactionMerkleProofPreimageHex(
    proof: MerkleTransactionProof
  ): string {
    return transactionMerkleProofPreimage(proof).toString('hex');
  }

  export function transactionMerkleProofDigest(
    proof: MerkleTransactionProof
  ): MerkleDigest {
    return sha3Hex(transactionMerkleProofPreimage(proof));
  }

  export function transactionEnvelopePreimageHex(
    envelope: ConfidentialTransactionEnvelope
  ): string {
    return transactionEnvelopePreimage(envelope).toString('hex');
  }

  export function transactionEnvelopeDigest(
    envelope: ConfidentialTransactionEnvelope
  ): MerkleDigest {
    return sha3Hex(transactionEnvelopePreimage(envelope));
  }

  export function transactionWalletProofRequestPreimageHex(
    request: ConfidentialWalletProofRequest
  ): string {
    return transactionWalletProofRequestPreimage(request).toString('hex');
  }

  export function transactionWalletProofRequestDigest(
    request: ConfidentialWalletProofRequest
  ): MerkleDigest {
    return sha3Hex(transactionWalletProofRequestPreimage(request));
  }

  export function transactionAcceptedRootWindowPreimageHex(
    window: ConfidentialAcceptedRootWindow
  ): string {
    return transactionAcceptedRootWindowPreimage(window).toString('hex');
  }

  export function transactionAcceptedRootWindowDigest(
    window: ConfidentialAcceptedRootWindow
  ): MerkleDigest {
    return sha3Hex(transactionAcceptedRootWindowPreimage(window));
  }

  export function transactionAcceptedRootWindowRoots(
    window: ConfidentialAcceptedRootWindow
  ): MerkleAcceptedRoot[] {
    transactionAcceptedRootWindowPreimage(window);
    return window.roots.map((entry) => entry.root);
  }

  export function transactionContextMatchesAcceptedRootWindow(
    context: ConfidentialTransactionContext,
    window: ConfidentialAcceptedRootWindow
  ): boolean {
    try {
      transactionContextPreimage(context);
      transactionAcceptedRootWindowPreimage(window);
      return (
        context.protocolVersion === window.protocolVersion &&
        context.networkId === window.networkId &&
        context.assetId === window.assetId &&
        context.ledgerEpoch === window.ledgerEpoch &&
        window.roots.some((entry) => sameAcceptedRoot(entry.root, context.root))
      );
    } catch {
      return false;
    }
  }

  export function transactionWalletProofRequestFromWindow(
    context: ConfidentialTransactionContext,
    acceptedRootWindow: ConfidentialAcceptedRootWindow,
    spentNullifiers: IntMatrix
  ): ConfidentialWalletProofRequest {
    if (!transactionContextMatchesAcceptedRootWindow(context, acceptedRootWindow)) {
      throw new Error('context is not accepted by the root window');
    }
    const request = {
      context,
      acceptedRoots: transactionAcceptedRootWindowRoots(acceptedRootWindow),
      spentNullifiers,
    };
    transactionWalletProofRequestPreimage(request);
    return request;
  }

  export function transactionContextMatchesPolicy(
    context: ConfidentialTransactionContext,
    policy: ConfidentialTransactionContextPolicy
  ): boolean {
    try {
      const protocolVersion = policy.protocolVersion ?? 1;
      const publicFee = policy.publicFee ?? 0;
      if (protocolVersion !== 1) {
        return false;
      }
      assertNonNegativeSafeI64(publicFee, 'policy.publicFee');
      return (
        context.protocolVersion === protocolVersion &&
        context.networkId === policy.networkId &&
        context.assetId === policy.assetId &&
        context.publicFee === publicFee &&
        (policy.ledgerEpoch === undefined || context.ledgerEpoch === policy.ledgerEpoch) &&
        (policy.root === undefined || sameAcceptedRoot(context.root, policy.root))
      );
    } catch {
      return false;
    }
  }

  export function transactionContextPolicyIsComplete(
    policy: ConfidentialTransactionContextPolicy
  ): boolean {
    try {
      if (
        policy.protocolVersion === undefined ||
        policy.ledgerEpoch === undefined ||
        policy.root === undefined ||
        policy.publicFee === undefined
      ) {
        return false;
      }
      assertNonNegativeSafeI64(policy.protocolVersion, 'policy.protocolVersion');
      if (policy.protocolVersion !== 1) {
        return false;
      }
      encodeAsciiString(policy.networkId, 'policy.networkId');
      assertNonNegativeSafeI64(policy.assetId, 'policy.assetId');
      assertNonNegativeSafeI64(policy.ledgerEpoch, 'policy.ledgerEpoch');
      encodeAcceptedRoot(policy.root, 'policy.root');
      assertNonNegativeSafeI64(policy.publicFee, 'policy.publicFee');
      return true;
    } catch {
      return false;
    }
  }

  export function nullifier(
    params: ScalarCommitParams,
    nk: IntMatrix,
    opening: CommitOpening
  ): IntVec {
    return normalizeVec(Isabella.ctNullifier(params, nk, opening));
  }

  export function canonicalNullifierChallenge(
    params: ScalarCommitParams,
    ck: IntMatrix,
    nk: IntMatrix,
    c: IntVec,
    nf: IntVec,
    aCommit: IntVec,
    aNullifier: IntVec
  ): number {
    return Isabella.ctNullifierCanonicalChallenge(params, ck, nk, c, nf, aCommit, aNullifier);
  }

  export function nullifierFsProve(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    nk: IntMatrix,
    c: IntVec,
    nf: IntVec,
    opening: CommitOpening,
    ys: CommitOpening[]
  ): NullifierProofLike | null {
    return normalizeNullifierProof(
      Isabella.ctNullifierFsProve(params, gamma, ck, nk, c, nf, opening, ys)
    );
  }

  /**
   * Sample a CSPRNG-backed nullifier proof mask opening.
   */
  export function sampleNullifierMask(params: ScalarCommitParams, gamma: number): CommitOpening {
    return ConfidentialSampling.opening(params.n1, params.n2, gamma);
  }

  /**
   * Sample one CSPRNG-backed nullifier proof mask opening per Fiat-Shamir round.
   */
  export function sampleNullifierMasks(
    params: ScalarCommitParams,
    gamma: number,
    rounds: number = ConfidentialBalance.fsRounds()
  ): CommitOpening[] {
    return ConfidentialSampling.openings(rounds, params.n1, params.n2, gamma);
  }

  export function nullifierFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    nk: IntMatrix,
    c: IntVec,
    nf: IntVec,
    proof: NullifierProofLike
  ): boolean {
    try {
      const checkedProof = normalizeNullifierProof(proof);
      return checkedProof !== null && Isabella.ctNullifierFsVerify(
        params,
        gamma,
        ck,
        nk,
        c,
        nf,
        checkedProof
      );
    } catch {
      return false;
    }
  }

  export function ledgerRoot(params: ScalarCommitParams, ledger: IntMatrix): IntVec {
    return normalizeVec(Isabella.ctLedgerRoot(params, ledger));
  }

  export function membershipProve(
    params: ScalarCommitParams,
    ledger: IntMatrix,
    c: IntVec
  ): MembershipProof | null {
    return normalizeMembershipProof(Isabella.ctMembershipProve(params, ledger, c));
  }

  export function membershipVerify(
    params: ScalarCommitParams,
    c: IntVec,
    proof: MembershipProof
  ): boolean {
    return Isabella.ctMembershipVerify(params, c, proof);
  }

  export function merkleLedgerRoot(ledger: IntMatrix): MerkleDigest {
    return ConfidentialMerkle.root(ledger);
  }

  export function merkleMembershipProve(
    ledger: IntMatrix,
    c: IntVec
  ): MerkleMembershipProof | null {
    return ConfidentialMerkle.membershipProve(ledger, c);
  }

  export function merkleMembershipVerify(
    c: IntVec,
    proof: MerkleMembershipProof
  ): boolean {
    return ConfidentialMerkle.membershipVerify(c, proof);
  }

  export function commitmentLedger(notes: VerifiedNote[]): IntMatrix {
    return normalizeMat(Isabella.ctCommitmentLedger(notes));
  }

  export function ledgerValid(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    root: IntVec,
    notes: VerifiedNote[],
    spent: IntMatrix
  ): boolean {
    return Isabella.ctLedgerValid(params, gamma, k, ck, root, notes, spent);
  }

  export function ledgerValidMerkle(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    root: MerkleDigest,
    notes: VerifiedNote[],
    spent: IntMatrix
  ): boolean {
    return (
      ConfidentialBalance.validScalarParams(params) &&
      validCommitKeyShape(params, ck) &&
      root === ConfidentialMerkle.root(commitmentLedger(notes)) &&
      distinctMat(spent) &&
      notes.every((note) =>
        ConfidentialRange.fsVerify(params, gamma, k, ck, note.commitment, note.rangeProof)
      )
    );
  }

  export function ledgerStepValid(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    return ledgerStepValidMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      notes,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  export function ledgerStepValidScaffold(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: TransactionProof
  ): boolean {
    return Isabella.ctLedgerStepValidScaffold(
      params,
      gamma,
      k,
      ck,
      nk,
      notes,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  export function semanticStepValidScaffold(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: TransactionProof
  ): boolean {
    return ledgerStepValidScaffold(
      params,
      gamma,
      k,
      ck,
      nk,
      notes,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  /**
   * Stable semantic ledger-step validation.
   *
   * The semantic default is the cryptographic Merkle-root path. Scaffold
   * validation remains available only through
   * `ledgerStepValidScaffold` / `semanticStepValidScaffold`, making the
   * non-production boundary explicit.
   */
  export function semanticStepValid(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    return ledgerStepValidMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      notes,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  export function ledgerStepValidMerkle(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    try {
      const preRoot = ConfidentialMerkle.root(commitmentLedger(notes));
      const updatedNotes = ledgerApplyNotesMerkle(notes, proof, cOut1, cOut2);
      const updatedSpent = ledgerApplySpent(spent, nf1, nf2);
      const postRoot = ConfidentialMerkle.root(commitmentLedger(updatedNotes));
      return (
        ledgerValidMerkle(params, gamma, k, ck, preRoot, notes, spent) &&
        fsVerifyMerkle(
          params,
          gamma,
          k,
          ck,
          nk,
          preRoot,
          spent,
          cIn1,
          cIn2,
          cOut1,
          cOut2,
          nf1,
          nf2,
          proof
        ) &&
        ledgerValidMerkle(params, gamma, k, ck, postRoot, updatedNotes, updatedSpent)
      );
    } catch {
      return false;
    }
  }

  export function semanticStepValidMerkle(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    notes: VerifiedNote[],
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    return ledgerStepValidMerkle(
      params,
      gamma,
      k,
      ck,
      nk,
      notes,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  export function nullifierProofShape(
    proof: NullifierProofLike
  ): 'legacy' | 'rounds' | 'lists' {
    if ('rounds' in proof && Array.isArray(proof.rounds)) {
      return 'rounds';
    }
    if (
      'aCommits' in proof &&
      'aNullifiers' in proof &&
      'zMsgs' in proof &&
      'zRands' in proof
    ) {
      return 'lists';
    }
    return 'legacy';
  }

  export function fsProve(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    ledger: IntMatrix,
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening,
    out1Bits: CommitOpening[],
    out1Comps: CommitOpening[],
    out2Bits: CommitOpening[],
    out2Comps: CommitOpening[],
    yIn1: CommitOpening[],
    yIn2: CommitOpening[],
    yBalance: IntMatrix,
    yOut1: IntMatrix,
    yOut1Pairs: IntMatrix[],
    yOut2: IntMatrix,
    yOut2Pairs: IntMatrix[]
  ): TransactionProof | null {
    return normalizeTransactionProof(
      Isabella.ctFsProve(
        params,
        gamma,
        k,
        ck,
        nk,
        ledger,
        spent,
        cIn1,
        cIn2,
        cOut1,
        cOut2,
        nf1,
        nf2,
        opIn1,
        opIn2,
        opOut1,
        opOut2,
        out1Bits,
        out1Comps,
        out2Bits,
        out2Comps,
        yIn1,
        yIn2,
        yBalance,
        yOut1,
        yOut1Pairs,
        yOut2,
        yOut2Pairs
      )
    );
  }

  export function fsVerify(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    root: IntVec,
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: TransactionProof
  ): boolean {
    try {
      const checkedProof = normalizeTransactionProof(proof);
      return checkedProof !== null && Isabella.ctFsVerify(
        params,
        gamma,
        k,
        ck,
        nk,
        root,
        spent,
        cIn1,
        cIn2,
        cOut1,
        cOut2,
        nf1,
        nf2,
        checkedProof
      );
    } catch {
      return false;
    }
  }

  export function fsProveMerkle(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    ledger: IntMatrix,
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening,
    out1Bits: CommitOpening[],
    out1Comps: CommitOpening[],
    out2Bits: CommitOpening[],
    out2Comps: CommitOpening[],
    yIn1: CommitOpening[],
    yIn2: CommitOpening[],
    yBalance: IntMatrix,
    yOut1: IntMatrix,
    yOut1Pairs: IntMatrix[],
    yOut2: IntMatrix,
    yOut2Pairs: IntMatrix[]
  ): MerkleTransactionProof | null {
    const scaffoldProof = fsProve(
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      opIn1,
      opIn2,
      opOut1,
      opOut2,
      out1Bits,
      out1Comps,
      out2Bits,
      out2Comps,
      yIn1,
      yIn2,
      yBalance,
      yOut1,
      yOut1Pairs,
      yOut2,
      yOut2Pairs
    );
    const in1Member = ConfidentialMerkle.membershipProve(ledger, cIn1);
    const in2Member = ConfidentialMerkle.membershipProve(ledger, cIn2);
    if (scaffoldProof === null || in1Member === null || in2Member === null) {
      return null;
    }
    if (in1Member.index === in2Member.index) {
      return null;
    }
    return normalizeMerkleTransactionProof({
      in1Member,
      in2Member,
      in1Nullifier: scaffoldProof.in1Nullifier,
      in2Nullifier: scaffoldProof.in2Nullifier,
      balance: scaffoldProof.balance,
      out1Range: scaffoldProof.out1Range,
      out2Range: scaffoldProof.out2Range,
    });
  }

  export function fsProveMerkleWithFee(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    ledger: IntMatrix,
    spent: IntMatrix,
    publicFee: number,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    opIn1: CommitOpening,
    opIn2: CommitOpening,
    opOut1: CommitOpening,
    opOut2: CommitOpening,
    out1Bits: CommitOpening[],
    out1Comps: CommitOpening[],
    out2Bits: CommitOpening[],
    out2Comps: CommitOpening[],
    yIn1: CommitOpening[],
    yIn2: CommitOpening[],
    yBalance: IntMatrix,
    yOut1: IntMatrix,
    yOut1Pairs: IntMatrix[],
    yOut2: IntMatrix,
    yOut2Pairs: IntMatrix[]
  ): MerkleTransactionProof | null {
    try {
      assertNonNegativeSafeI64(publicFee, 'publicFee');
      const inputAmount =
        ConfidentialBalance.amountOfOpening(opIn1) +
        ConfidentialBalance.amountOfOpening(opIn2);
      const outputAmount =
        ConfidentialBalance.amountOfOpening(opOut1) +
        ConfidentialBalance.amountOfOpening(opOut2);
      if (inputAmount !== outputAmount + publicFee) {
        return null;
      }
      const in1Member = ConfidentialMerkle.membershipProve(ledger, cIn1);
      const in2Member = ConfidentialMerkle.membershipProve(ledger, cIn2);
      if (in1Member === null || in2Member === null || in1Member.index === in2Member.index) {
        return null;
      }
      const in1Nullifier = nullifierFsProve(params, gamma, ck, nk, cIn1, nf1, opIn1, yIn1);
      const in2Nullifier = nullifierFsProve(params, gamma, ck, nk, cIn2, nf2, opIn2, yIn2);
      const balance = ConfidentialBalance.fsProve(
        params,
        gamma,
        ck,
        ConfidentialBalance.feeBalanceCommitment(
          params,
          ck,
          cIn1,
          cIn2,
          cOut1,
          cOut2,
          publicFee
        ),
        ConfidentialBalance.aggregateRandomness(opIn1, opIn2, opOut1, opOut2),
        yBalance
      );
      const out1Range = ConfidentialRange.fsProve(
        params,
        gamma,
        k,
        ck,
        cOut1,
        opOut1,
        out1Bits,
        out1Comps,
        yOut1,
        yOut1Pairs
      );
      const out2Range = ConfidentialRange.fsProve(
        params,
        gamma,
        k,
        ck,
        cOut2,
        opOut2,
        out2Bits,
        out2Comps,
        yOut2,
        yOut2Pairs
      );
      if (
        in1Nullifier === null ||
        in2Nullifier === null ||
        balance === null ||
        out1Range === null ||
        out2Range === null
      ) {
        return null;
      }
      return normalizeMerkleTransactionProof({
        in1Member,
        in2Member,
        in1Nullifier,
        in2Nullifier,
        balance,
        out1Range,
        out2Range,
      });
    } catch {
      return null;
    }
  }

  export function fsVerifyMerkle(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    root: MerkleDigest,
    spent: IntMatrix,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    try {
      const checkedProof = normalizeMerkleTransactionProof(proof);
      return checkedProof !== null && (
        validCommitKeyShape(params, ck) &&
        validCommitKeyShape(params, nk) &&
        ConfidentialMerkle.membershipVerify(cIn1, checkedProof.in1Member) &&
        ConfidentialMerkle.membershipVerify(cIn2, checkedProof.in2Member) &&
        checkedProof.in1Member.root === root &&
        checkedProof.in2Member.root === root &&
        checkedProof.in1Member.index !== checkedProof.in2Member.index &&
        !containsVec(spent, nf1) &&
        !containsVec(spent, nf2) &&
        !sameVec(nf1, nf2) &&
        nullifierFsVerify(params, gamma, ck, nk, cIn1, nf1, checkedProof.in1Nullifier) &&
        nullifierFsVerify(params, gamma, ck, nk, cIn2, nf2, checkedProof.in2Nullifier) &&
        ConfidentialBalance.fsVerify(
          params,
          gamma,
          ck,
          ConfidentialBalance.balanceCommitment(cIn1, cIn2, cOut1, cOut2, params.q),
          checkedProof.balance
        ) &&
        ConfidentialRange.fsVerify(params, gamma, k, ck, cOut1, checkedProof.out1Range) &&
        ConfidentialRange.fsVerify(params, gamma, k, ck, cOut2, checkedProof.out2Range)
      );
    } catch {
      return false;
    }
  }

  export function fsVerifyMerkleWithFee(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    root: MerkleDigest,
    spent: IntMatrix,
    publicFee: number,
    cIn1: IntVec,
    cIn2: IntVec,
    cOut1: IntVec,
    cOut2: IntVec,
    nf1: IntVec,
    nf2: IntVec,
    proof: MerkleTransactionProof
  ): boolean {
    try {
      assertNonNegativeSafeI64(publicFee, 'publicFee');
      const checkedProof = normalizeMerkleTransactionProof(proof);
      return (
        checkedProof !== null &&
        validCommitKeyShape(params, ck) &&
        validCommitKeyShape(params, nk) &&
        ConfidentialMerkle.membershipVerify(cIn1, checkedProof.in1Member) &&
        ConfidentialMerkle.membershipVerify(cIn2, checkedProof.in2Member) &&
        checkedProof.in1Member.root === root &&
        checkedProof.in2Member.root === root &&
        checkedProof.in1Member.index !== checkedProof.in2Member.index &&
        !containsVec(spent, nf1) &&
        !containsVec(spent, nf2) &&
        !sameVec(nf1, nf2) &&
        nullifierFsVerify(params, gamma, ck, nk, cIn1, nf1, checkedProof.in1Nullifier) &&
        nullifierFsVerify(params, gamma, ck, nk, cIn2, nf2, checkedProof.in2Nullifier) &&
        ConfidentialBalance.fsVerify(
          params,
          gamma,
          ck,
          ConfidentialBalance.feeBalanceCommitment(
            params,
            ck,
            cIn1,
            cIn2,
            cOut1,
            cOut2,
            publicFee
          ),
          checkedProof.balance
        ) &&
        ConfidentialRange.fsVerify(params, gamma, k, ck, cOut1, checkedProof.out1Range) &&
        ConfidentialRange.fsVerify(params, gamma, k, ck, cOut2, checkedProof.out2Range)
      );
    } catch {
      return false;
    }
  }

  export function fsVerifyMerkleEnvelope(
    params: ScalarCommitParams,
    gamma: number,
    k: number,
    ck: IntMatrix,
    nk: IntMatrix,
    spent: IntMatrix,
    envelope: ConfidentialTransactionEnvelope,
    policy: ConfidentialTransactionContextPolicy
  ): boolean {
    try {
      const contextDigest = transactionContextDigest(envelope.context);
      return (
        transactionContextPolicyIsComplete(policy) &&
        envelope.contextDigest === contextDigest &&
        transactionContextMatchesPolicy(envelope.context, policy) &&
        fsVerifyMerkleWithFee(
          params,
          gamma,
          k,
          ck,
          nk,
          envelope.context.root.digest,
          spent,
          envelope.context.publicFee,
          envelope.context.cIn1,
          envelope.context.cIn2,
          envelope.context.cOut1,
          envelope.context.cOut2,
          envelope.context.nf1,
          envelope.context.nf2,
          envelope.proof
        ) &&
        envelope.proof.in1Member.siblings.length === envelope.context.root.depth &&
        envelope.proof.in2Member.siblings.length === envelope.context.root.depth
      );
    } catch {
      return false;
    }
  }

  export function ledgerApplyNotes(
    notes: VerifiedNote[],
    proof: TransactionProof,
    cOut1: IntVec,
    cOut2: IntVec
  ): VerifiedNote[] {
    return normalizeVerifiedNotes(Isabella.ctLedgerApplyNotes(notes, proof, cOut1, cOut2));
  }

  export function ledgerApplyNotesMerkle(
    notes: VerifiedNote[],
    proof: MerkleTransactionProof,
    cOut1: IntVec,
    cOut2: IntVec
  ): VerifiedNote[] {
    const in1Index = proof.in1Member.index;
    const in2Index = proof.in2Member.index;
    if (
      in1Index < 0 ||
      in2Index < 0 ||
      in1Index >= notes.length ||
      in2Index >= notes.length
    ) {
      throw new RangeError('Merkle membership index is outside the note ledger');
    }
    const remaining = notes.filter((_, index) => index !== in1Index && index !== in2Index);
    return normalizeVerifiedNotes([
      { commitment: cOut1, rangeProof: proof.out1Range },
      { commitment: cOut2, rangeProof: proof.out2Range },
      ...remaining,
    ]);
  }

  export function ledgerApplySpent(
    spent: IntMatrix,
    nf1: IntVec,
    nf2: IntVec
  ): IntMatrix {
    return normalizeMat(Isabella.ctLedgerApplySpent(spent, nf1, nf2));
  }
}

/**
 * Versioned bignum transaction digest helpers for widened SIS-note parameters.
 *
 * These helpers intentionally do not replace `ConfidentialTransaction` yet:
 * they bind q83-scale commitments, nullifiers, fees, spent snapshots, and proof
 * responses with the canonical bignum codec under `ISABELLA-CT-TX-BIGNUM-v1`.
 */
export namespace ConfidentialTransactionBigInt {
  export const transactionDst = CT_TRANSACTION_BIGNUM_DST;
  export const merkleDst = CT_MERKLE_BIGNUM_DST;
  export const transactionProtocolId = CT_TRANSACTION_PROTOCOL_ID;
  export const transactionTags = CT_TRANSACTION_TAGS;
  export const integerEncoding = CT_BIGNUM_ENCODING;
  export const digestEncoding = 'len_i64_le || 32 raw digest bytes';

  export function transactionContextPreimageHex(
    context: BigIntConfidentialTransactionContext
  ): string {
    return transactionBignumContextPreimage(context).toString('hex');
  }

  export function transactionContextDigest(
    context: BigIntConfidentialTransactionContext
  ): MerkleDigest {
    return sha3Hex(transactionBignumContextPreimage(context));
  }

  export function transactionMerkleProofPreimageHex(
    proof: BigIntMerkleTransactionProof
  ): string {
    return transactionBignumMerkleProofPreimage(proof).toString('hex');
  }

  export function transactionMerkleProofDigest(
    proof: BigIntMerkleTransactionProof
  ): MerkleDigest {
    return sha3Hex(transactionBignumMerkleProofPreimage(proof));
  }

  export function transactionEnvelopePreimageHex(
    envelope: BigIntConfidentialTransactionEnvelope
  ): string {
    return transactionBignumEnvelopePreimage(envelope).toString('hex');
  }

  export function transactionEnvelopeDigest(
    envelope: BigIntConfidentialTransactionEnvelope
  ): MerkleDigest {
    return sha3Hex(transactionBignumEnvelopePreimage(envelope));
  }

  export function transactionWalletProofRequestPreimageHex(
    request: BigIntConfidentialWalletProofRequest
  ): string {
    return transactionBignumWalletProofRequestPreimage(request).toString('hex');
  }

  export function transactionWalletProofRequestDigest(
    request: BigIntConfidentialWalletProofRequest
  ): MerkleDigest {
    return sha3Hex(transactionBignumWalletProofRequestPreimage(request));
  }

  export function transactionAcceptedRootWindowPreimageHex(
    window: ConfidentialAcceptedRootWindow
  ): string {
    return transactionBignumAcceptedRootWindowPreimage(window).toString('hex');
  }

  export function transactionAcceptedRootWindowDigest(
    window: ConfidentialAcceptedRootWindow
  ): MerkleDigest {
    return sha3Hex(transactionBignumAcceptedRootWindowPreimage(window));
  }

  export function transactionAcceptedRootWindowRoots(
    window: ConfidentialAcceptedRootWindow
  ): MerkleAcceptedRoot[] {
    transactionBignumAcceptedRootWindowPreimage(window);
    return window.roots.map((entry) => entry.root);
  }

  export function transactionContextMatchesAcceptedRootWindow(
    context: BigIntConfidentialTransactionContext,
    window: ConfidentialAcceptedRootWindow
  ): boolean {
    try {
      transactionBignumContextPreimage(context);
      transactionBignumAcceptedRootWindowPreimage(window);
      return (
        context.protocolVersion === window.protocolVersion &&
        context.networkId === window.networkId &&
        context.assetId === window.assetId &&
        context.ledgerEpoch === window.ledgerEpoch &&
        window.roots.some((entry) => sameAcceptedRoot(entry.root, context.root))
      );
    } catch {
      return false;
    }
  }

  export function transactionWalletProofRequestFromWindow(
    context: BigIntConfidentialTransactionContext,
    window: ConfidentialAcceptedRootWindow,
    spentNullifiers: readonly BigIntVecInput[]
  ): BigIntConfidentialWalletProofRequest {
    if (!transactionContextMatchesAcceptedRootWindow(context, window)) {
      throw new Error('context does not match accepted-root window');
    }
    const request = {
      context,
      acceptedRoots: transactionAcceptedRootWindowRoots(window),
      spentNullifiers,
    };
    transactionBignumWalletProofRequestPreimage(request);
    return request;
  }

  export function merkleLedgerRoot(
    commitments: readonly BigIntVecInput[],
    emptyWidth?: number
  ): MerkleDigest {
    return ConfidentialMerkleBigInt.root(commitments, emptyWidth);
  }

  export function merkleMembershipProve(
    commitments: readonly BigIntVecInput[],
    commitment: BigIntVecInput
  ): MerkleMembershipProof | null {
    return ConfidentialMerkleBigInt.membershipProve(commitments, commitment);
  }

  export function merkleMembershipVerify(
    commitment: BigIntVecInput,
    proof: MerkleMembershipProof
  ): boolean {
    return ConfidentialMerkleBigInt.membershipVerify(commitment, proof);
  }

  function normalizeOpening(opening: BigIntCommitOpening, label: string): BigIntCommitOpening {
    assertExactObjectKeys(opening, ['msg', 'rand'], label);
    return {
      msg: normalizeBigIntVec(opening.msg, `${label}.msg`),
      rand: normalizeBigIntVec(opening.rand, `${label}.rand`),
    };
  }

  function normalizePublicFee(fee: ConfidentialBigIntInput, label: string): bigint {
    const normalized = normalizeConfidentialBigInt(fee, label);
    if (normalized < 0n) {
      throw new Error(`${label} must be non-negative`);
    }
    return normalized;
  }

  function amountOfOpening(opening: BigIntCommitOpening): bigint {
    const normalized = normalizeOpening(opening, 'opening');
    if (normalized.msg.length !== 1) {
      throw new Error('amount opening must have one message coordinate');
    }
    return normalized.msg[0];
  }

  function aggregateRandomness(
    opIn1: BigIntCommitOpening,
    opIn2: BigIntCommitOpening,
    opOut1: BigIntCommitOpening,
    opOut2: BigIntCommitOpening
  ): BigIntVec {
    const in1 = normalizeOpening(opIn1, 'opIn1').rand;
    const in2 = normalizeOpening(opIn2, 'opIn2').rand;
    const out1 = normalizeOpening(opOut1, 'opOut1').rand;
    const out2 = normalizeOpening(opOut2, 'opOut2').rand;
    return bigintVecAdd(
      bigintVecAdd(in1, in2),
      bigintScalarMult(-1n, bigintVecAdd(out1, out2))
    );
  }

  function balanceCommitment(
    params: BigIntScalarCommitParams,
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput
  ): BigIntVec {
    const inputs = bigintVecAdd(
      normalizeBigIntVec(cIn1, 'cIn1'),
      normalizeBigIntVec(cIn2, 'cIn2')
    );
    const outputs = bigintVecAdd(
      normalizeBigIntVec(cOut1, 'cOut1'),
      normalizeBigIntVec(cOut2, 'cOut2')
    );
    return bigintVecMod(bigintVecAdd(inputs, bigintScalarMult(-1n, outputs)), params.q);
  }

  function publicAmountCommitment(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    fee: ConfidentialBigIntInput
  ): BigIntVec {
    const normalizedFee = normalizePublicFee(fee, 'publicFee');
    if (!ConfidentialBalanceBigInt.validCommitKey(params, ck)) {
      throw new Error('invalid commitment key');
    }
    return bigintMatVecMultMod(
      normalizeBigIntMatrix(ck, 'ck'),
      [normalizedFee, ...Array.from({ length: params.n2 }, () => 0n)],
      params.q
    );
  }

  function feeBalanceCommitment(
    params: BigIntScalarCommitParams,
    ck: BigIntMatrixInput,
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput,
    fee: ConfidentialBigIntInput
  ): BigIntVec {
    return bigintVecMod(
      bigintVecAdd(
        balanceCommitment(params, cIn1, cIn2, cOut1, cOut2),
        bigintScalarMult(-1n, publicAmountCommitment(params, ck, fee))
      ),
      params.q
    );
  }

  export function transactionContextMatchesPolicy(
    context: BigIntConfidentialTransactionContext,
    policy: BigIntConfidentialTransactionContextPolicy
  ): boolean {
    try {
      const protocolVersion = policy.protocolVersion ?? 1;
      const publicFee = normalizePublicFee(policy.publicFee ?? 0n, 'policy.publicFee');
      if (protocolVersion !== 1) {
        return false;
      }
      return (
        context.protocolVersion === protocolVersion &&
        context.networkId === policy.networkId &&
        context.assetId === policy.assetId &&
        normalizePublicFee(context.publicFee, 'context.publicFee') === publicFee &&
        (policy.ledgerEpoch === undefined || context.ledgerEpoch === policy.ledgerEpoch) &&
        (policy.root === undefined || sameAcceptedRoot(context.root, policy.root))
      );
    } catch {
      return false;
    }
  }

  export function transactionContextPolicyIsComplete(
    policy: BigIntConfidentialTransactionContextPolicy
  ): boolean {
    try {
      if (
        policy.protocolVersion === undefined ||
        policy.ledgerEpoch === undefined ||
        policy.root === undefined ||
        policy.publicFee === undefined
      ) {
        return false;
      }
      assertNonNegativeSafeI64(policy.protocolVersion, 'policy.protocolVersion');
      if (policy.protocolVersion !== 1) {
        return false;
      }
      encodeAsciiString(policy.networkId, 'policy.networkId');
      assertNonNegativeSafeI64(policy.assetId, 'policy.assetId');
      assertNonNegativeSafeI64(policy.ledgerEpoch, 'policy.ledgerEpoch');
      encodeAcceptedRoot(policy.root, 'policy.root');
      normalizePublicFee(policy.publicFee, 'policy.publicFee');
      return true;
    } catch {
      return false;
    }
  }

  export function fsProveMerkle(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    ledger: readonly BigIntVecInput[],
    spent: readonly BigIntVecInput[],
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput,
    nf1: BigIntVecInput,
    nf2: BigIntVecInput,
    opIn1: BigIntCommitOpening,
    opIn2: BigIntCommitOpening,
    opOut1: BigIntCommitOpening,
    opOut2: BigIntCommitOpening,
    out1Bits: readonly BigIntCommitOpening[],
    out1Comps: readonly BigIntCommitOpening[],
    out2Bits: readonly BigIntCommitOpening[],
    out2Comps: readonly BigIntCommitOpening[],
    yIn1: readonly BigIntCommitOpening[],
    yIn2: readonly BigIntCommitOpening[],
    yBalance: BigIntMatrixInput,
    yOut1: BigIntMatrixInput,
    yOut1Pairs: readonly BigIntMatrixInput[],
    yOut2: BigIntMatrixInput,
    yOut2Pairs: readonly BigIntMatrixInput[]
  ): BigIntMerkleTransactionProof | null {
    return fsProveMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      ledger,
      spent,
      0n,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      opIn1,
      opIn2,
      opOut1,
      opOut2,
      out1Bits,
      out1Comps,
      out2Bits,
      out2Comps,
      yIn1,
      yIn2,
      yBalance,
      yOut1,
      yOut1Pairs,
      yOut2,
      yOut2Pairs
    );
  }

  export function fsProveMerkleWithFee(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    ledger: readonly BigIntVecInput[],
    spent: readonly BigIntVecInput[],
    publicFee: ConfidentialBigIntInput,
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput,
    nf1: BigIntVecInput,
    nf2: BigIntVecInput,
    opIn1: BigIntCommitOpening,
    opIn2: BigIntCommitOpening,
    opOut1: BigIntCommitOpening,
    opOut2: BigIntCommitOpening,
    out1Bits: readonly BigIntCommitOpening[],
    out1Comps: readonly BigIntCommitOpening[],
    out2Bits: readonly BigIntCommitOpening[],
    out2Comps: readonly BigIntCommitOpening[],
    yIn1: readonly BigIntCommitOpening[],
    yIn2: readonly BigIntCommitOpening[],
    yBalance: BigIntMatrixInput,
    yOut1: BigIntMatrixInput,
    yOut1Pairs: readonly BigIntMatrixInput[],
    yOut2: BigIntMatrixInput,
    yOut2Pairs: readonly BigIntMatrixInput[]
  ): BigIntMerkleTransactionProof | null {
    try {
      const fee = normalizePublicFee(publicFee, 'publicFee');
      const spentRows = normalizeBigIntMatrix(spent, 'spent');
      const nf1Vec = normalizeBigIntVec(nf1, 'nf1');
      const nf2Vec = normalizeBigIntVec(nf2, 'nf2');
      if (
        containsBigIntVec(spentRows, nf1Vec) ||
        containsBigIntVec(spentRows, nf2Vec) ||
        sameBigIntVec(nf1Vec, nf2Vec)
      ) {
        return null;
      }
      const inputAmount = amountOfOpening(opIn1) + amountOfOpening(opIn2);
      const outputAmount = amountOfOpening(opOut1) + amountOfOpening(opOut2);
      if (inputAmount !== outputAmount + fee) {
        return null;
      }
      const in1Member = ConfidentialMerkleBigInt.membershipProve(ledger, cIn1);
      const in2Member = ConfidentialMerkleBigInt.membershipProve(ledger, cIn2);
      if (in1Member === null || in2Member === null || in1Member.index === in2Member.index) {
        return null;
      }
      const in1Nullifier = ConfidentialNullifierBigInt.fsProve(
        params,
        gamma,
        ck,
        nk,
        cIn1,
        nf1,
        opIn1,
        yIn1
      );
      const in2Nullifier = ConfidentialNullifierBigInt.fsProve(
        params,
        gamma,
        ck,
        nk,
        cIn2,
        nf2,
        opIn2,
        yIn2
      );
      const balance = ConfidentialBalanceBigInt.fsProve(
        params,
        gamma,
        ck,
        feeBalanceCommitment(params, ck, cIn1, cIn2, cOut1, cOut2, fee),
        aggregateRandomness(opIn1, opIn2, opOut1, opOut2),
        yBalance
      );
      const out1Range = ConfidentialRangeBigInt.fsProve(
        params,
        gamma,
        k,
        ck,
        cOut1,
        opOut1,
        out1Bits,
        out1Comps,
        yOut1,
        yOut1Pairs
      );
      const out2Range = ConfidentialRangeBigInt.fsProve(
        params,
        gamma,
        k,
        ck,
        cOut2,
        opOut2,
        out2Bits,
        out2Comps,
        yOut2,
        yOut2Pairs
      );
      if (
        in1Nullifier === null ||
        in2Nullifier === null ||
        balance === null ||
        out1Range === null ||
        out2Range === null
      ) {
        return null;
      }
      return {
        in1Member,
        in2Member,
        in1Nullifier,
        in2Nullifier,
        balance,
        out1Range,
        out2Range,
      };
    } catch {
      return null;
    }
  }

  export function fsVerifyMerkle(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    root: MerkleDigest,
    spent: readonly BigIntVecInput[],
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput,
    nf1: BigIntVecInput,
    nf2: BigIntVecInput,
    proof: BigIntMerkleTransactionProof
  ): boolean {
    return fsVerifyMerkleWithFee(
      params,
      gamma,
      k,
      ck,
      nk,
      root,
      spent,
      0n,
      cIn1,
      cIn2,
      cOut1,
      cOut2,
      nf1,
      nf2,
      proof
    );
  }

  export function fsVerifyMerkleWithFee(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    root: MerkleDigest,
    spent: readonly BigIntVecInput[],
    publicFee: ConfidentialBigIntInput,
    cIn1: BigIntVecInput,
    cIn2: BigIntVecInput,
    cOut1: BigIntVecInput,
    cOut2: BigIntVecInput,
    nf1: BigIntVecInput,
    nf2: BigIntVecInput,
    proof: BigIntMerkleTransactionProof
  ): boolean {
    try {
      normalizePublicFee(publicFee, 'publicFee');
      transactionBignumMerkleProofPreimage(proof);
      const spentRows = normalizeBigIntMatrix(spent, 'spent');
      const nf1Vec = normalizeBigIntVec(nf1, 'nf1');
      const nf2Vec = normalizeBigIntVec(nf2, 'nf2');
      return (
        ConfidentialBalanceBigInt.validCommitKey(params, ck) &&
        ConfidentialBalanceBigInt.validCommitKey(params, nk) &&
        ConfidentialMerkleBigInt.membershipVerify(cIn1, proof.in1Member) &&
        ConfidentialMerkleBigInt.membershipVerify(cIn2, proof.in2Member) &&
        proof.in1Member.root === root &&
        proof.in2Member.root === root &&
        proof.in1Member.index !== proof.in2Member.index &&
        !containsBigIntVec(spentRows, nf1Vec) &&
        !containsBigIntVec(spentRows, nf2Vec) &&
        !sameBigIntVec(nf1Vec, nf2Vec) &&
        ConfidentialNullifierBigInt.fsVerify(
          params,
          gamma,
          ck,
          nk,
          cIn1,
          nf1Vec,
          normalizeBigIntNullifierProofInput(proof.in1Nullifier, 'proof.in1Nullifier')
        ) &&
        ConfidentialNullifierBigInt.fsVerify(
          params,
          gamma,
          ck,
          nk,
          cIn2,
          nf2Vec,
          normalizeBigIntNullifierProofInput(proof.in2Nullifier, 'proof.in2Nullifier')
        ) &&
        ConfidentialBalanceBigInt.fsVerify(
          params,
          gamma,
          ck,
          feeBalanceCommitment(params, ck, cIn1, cIn2, cOut1, cOut2, publicFee),
          normalizeBigIntBalanceProofInput(proof.balance, 'proof.balance')
        ) &&
        ConfidentialRangeBigInt.fsVerify(
          params,
          gamma,
          k,
          ck,
          cOut1,
          normalizeBigIntRangeProofInput(proof.out1Range, 'proof.out1Range')
        ) &&
        ConfidentialRangeBigInt.fsVerify(
          params,
          gamma,
          k,
          ck,
          cOut2,
          normalizeBigIntRangeProofInput(proof.out2Range, 'proof.out2Range')
        )
      );
    } catch {
      return false;
    }
  }

  export function fsVerifyMerkleEnvelope(
    params: BigIntScalarCommitParams,
    gamma: ConfidentialBigIntInput,
    k: number,
    ck: BigIntMatrixInput,
    nk: BigIntMatrixInput,
    spent: readonly BigIntVecInput[],
    envelope: BigIntConfidentialTransactionEnvelope,
    policy: BigIntConfidentialTransactionContextPolicy
  ): boolean {
    try {
      const contextDigest = transactionContextDigest(envelope.context);
      return (
        transactionContextPolicyIsComplete(policy) &&
        envelope.contextDigest === contextDigest &&
        transactionContextMatchesPolicy(envelope.context, policy) &&
        fsVerifyMerkleWithFee(
          params,
          gamma,
          k,
          ck,
          nk,
          envelope.context.root.digest,
          spent,
          envelope.context.publicFee,
          envelope.context.cIn1,
          envelope.context.cIn2,
          envelope.context.cOut1,
          envelope.context.cOut2,
          envelope.context.nf1,
          envelope.context.nf2,
          envelope.proof
        ) &&
        envelope.proof.in1Member.siblings.length === envelope.context.root.depth &&
        envelope.proof.in2Member.siblings.length === envelope.context.root.depth
      );
    } catch {
      return false;
    }
  }
}

// Re-export everything for convenience
export { Isabella as runtime };
