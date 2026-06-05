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

import { createHash } from 'node:crypto';

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
  ctLedgerStepValid(
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

function normalizeVerifiedNote(note: VerifiedNote): VerifiedNote {
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

const CT_MERKLE_DST = 'ISABELLA-CT-MERKLE-v1';
const CT_MERKLE_TAGS = {
  leaf: 0,
  node: 1,
  empty: 2,
} as const;

function assertSafeI64(value: number, label: string): void {
  if (!Number.isSafeInteger(value)) {
    throw new RangeError(`${label} must be a safe signed integer`);
  }
}

function assertNonNegativeSafeI64(value: number, label: string): void {
  assertSafeI64(value, label);
  if (value < 0) {
    throw new RangeError(`${label} must be non-negative`);
  }
}

function encodeI64LE(value: number, label: string): Buffer {
  assertSafeI64(value, label);
  const out = Buffer.alloc(8);
  out.writeBigInt64LE(BigInt(value), 0);
  return out;
}

function encodeIntVector(values: IntVec, label: string): Buffer {
  assertNonNegativeSafeI64(values.length, `${label}.length`);
  return Buffer.concat([
    encodeI64LE(values.length, `${label}.length`),
    ...values.map((value, index) => encodeI64LE(value, `${label}[${index}]`)),
  ]);
}

function merklePreimage(tag: number, body: Buffer): Buffer {
  return Buffer.concat([
    Buffer.from(CT_MERKLE_DST, 'ascii'),
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

function merkleEmptyPreimage(width: number): Buffer {
  assertNonNegativeSafeI64(width, 'width');
  return merklePreimage(CT_MERKLE_TAGS.empty, encodeI64LE(width, 'width'));
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

function merkleHashLeaf(commitment: IntVec): MerkleDigest {
  return sha3Hex(merkleLeafPreimage(commitment));
}

function merkleHashEmpty(width: number): MerkleDigest {
  return sha3Hex(merkleEmptyPreimage(width));
}

function merkleHashNode(left: MerkleDigest, right: MerkleDigest): MerkleDigest {
  return sha3Hex(merkleNodePreimage(left, right));
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
    return Isabella.cbFsVerify(params, gamma, ck, c, proof);
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
    return Isabella.crFsVerify(params, gamma, k, ck, cAmount, proof);
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
 * current transaction verifier still uses the algebraic ledger scaffold, so
 * these helpers are exposed separately until the formal transaction relation is
 * migrated to cryptographic roots.
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
 * Confidential-transaction proof helpers over SIS commitments.
 *
 * This composes deterministic nullifiers, explicit membership proofs,
 * confidential-balance proofs, and output range proofs into a contract-friendly
 * 2-in/2-out transfer verifier.
 */
export namespace ConfidentialTransaction {
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

  export function nullifierFsVerify(
    params: ScalarCommitParams,
    gamma: number,
    ck: IntMatrix,
    nk: IntMatrix,
    c: IntVec,
    nf: IntVec,
    proof: NullifierProofLike
  ): boolean {
    return Isabella.ctNullifierFsVerify(
      params,
      gamma,
      ck,
      nk,
      c,
      nf,
      proof
    );
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
    proof: TransactionProof
  ): boolean {
    return Isabella.ctLedgerStepValid(
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
   * Stable alias for semantic ledger-step validation.
   *
   * This keeps the public SDK naming explicit while preserving the original
   * generated `ledgerStepValid` entrypoint for compatibility.
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
    proof: TransactionProof
  ): boolean {
    return ledgerStepValid(
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
    return Isabella.ctFsVerify(
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
      proof
    );
  }

  export function ledgerApplyNotes(
    notes: VerifiedNote[],
    proof: TransactionProof,
    cOut1: IntVec,
    cOut2: IntVec
  ): VerifiedNote[] {
    return normalizeVerifiedNotes(Isabella.ctLedgerApplyNotes(notes, proof, cOut1, cOut2));
  }

  export function ledgerApplySpent(
    spent: IntMatrix,
    nf1: IntVec,
    nf2: IntVec
  ): IntMatrix {
    return normalizeMat(Isabella.ctLedgerApplySpent(spent, nf1, nf2));
  }
}

// Re-export everything for convenience
export { Isabella as runtime };
