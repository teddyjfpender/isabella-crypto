import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = process.env.ISABELLA_PROJECT_ROOT
  ? path.resolve(process.env.ISABELLA_PROJECT_ROOT)
  : path.join(__dirname, '..', '..');
const typeScriptEntry = process.env.ISABELLA_TS_ENTRY
  ? path.resolve(process.env.ISABELLA_TS_ENTRY)
  : path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');

type IntVec = number[];
type IntMatrix = number[][];
type CommitOpening = { msg: IntVec; rand: IntVec };
type BalanceProof = { a: IntVec; z: IntVec };
type BalanceRound = { a: IntVec; z: IntVec; challenge?: boolean | number };
type BalanceProofLike =
  | BalanceProof
  | { rounds: BalanceRound[] }
  | { as: IntMatrix; zs: IntMatrix; challenges?: Array<boolean | number> };
type RangeProof = {
  bits: IntMatrix;
  comps: IntMatrix;
  amountAs: IntMatrix;
  amountZs: IntMatrix;
  pairAss: IntMatrix[];
  pairZss: IntMatrix[];
  challenges?: Array<boolean | number>;
};
type RangeProofLike =
  | RangeProof
  | { rounds: unknown[] }
  | {
      bits: IntMatrix;
      comps: IntMatrix;
      amountAs: IntMatrix;
      amountZs: IntMatrix;
      pairAss?: IntMatrix[];
      pairZss?: IntMatrix[];
      challenges?: Array<boolean | number>;
    }
  | {
      bits: IntMatrix;
      comps: IntMatrix;
      amountA: IntVec;
      amountZ: IntVec;
      pairAs: IntMatrix;
      pairZs: IntMatrix;
    };
type NullifierProof = {
  aCommit: IntVec;
  aNullifier: IntVec;
  zMsg: IntVec;
  zRand: IntVec;
};
type NullifierRound = {
  aCommit: IntVec;
  aNullifier: IntVec;
  zMsg: IntVec;
  zRand: IntVec;
  challenge?: boolean | number;
};
type NullifierProofLike =
  | NullifierProof
  | { rounds: NullifierRound[] }
  | {
      aCommits: IntMatrix;
      aNullifiers: IntMatrix;
      zMsgs: IntMatrix;
      zRands: IntMatrix;
      challenges?: Array<boolean | number>;
    };
type MembershipProof = {
  index: number;
  root: IntVec;
  siblings: IntMatrix;
  directions: boolean[];
};
type TransactionProof = {
  in1Member: MembershipProof;
  in2Member: MembershipProof;
  in1Nullifier: NullifierProofLike;
  in2Nullifier: NullifierProofLike;
  balance: BalanceProofLike;
  out1Range: RangeProofLike;
  out2Range: RangeProofLike;
};
type VerifiedNote = { commitment: IntVec; rangeProof: RangeProofLike };

function balanceProofShape(proof: BalanceProofLike): 'single' | 'rounds' | 'lists' {
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  if ('as' in proof && 'zs' in proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return 'lists';
  }
  return 'single';
}

function normalizeBalanceProof(proof: BalanceProofLike): BalanceRound[] {
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return proof.rounds;
  }
  if ('as' in proof && 'zs' in proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return proof.as.map((a, index) => ({
      a,
      z: proof.zs[index] ?? [],
      challenge: proof.challenges?.[index],
    }));
  }
  return [{ a: proof.a, z: proof.z }];
}

function rangeProofShape(proof: RangeProofLike): 'legacy' | 'rounds' | 'lists' {
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  if ('amountAs' in proof || 'amountZs' in proof || 'pairAss' in proof || 'pairZss' in proof) {
    return 'lists';
  }
  if ('bits' in proof && 'comps' in proof && 'amountA' in proof && 'amountZ' in proof && 'pairAs' in proof && 'pairZs' in proof) {
    return 'legacy';
  }
  return 'lists';
}

function nullifierProofShape(proof: NullifierProofLike): 'legacy' | 'rounds' | 'lists' {
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

function cloneJson<T>(value: T): T {
  return JSON.parse(JSON.stringify(value)) as T;
}

function tamperMembershipProof(proof: MembershipProof): MembershipProof {
  const tampered = cloneJson(proof);
  tampered.root[0] = tampered.root[0] + 1;
  return tampered;
}

function tamperMembershipPath(proof: MembershipProof): MembershipProof {
  const tampered = cloneJson(proof);
  if (tampered.directions.length > 0) {
    tampered.directions[0] = !tampered.directions[0];
  } else {
    tampered.index = tampered.index + 1;
  }
  return tampered;
}

function tamperNullifierProof(proof: NullifierProofLike): NullifierProofLike {
  const tampered = cloneJson(proof);
  if ('rounds' in tampered && Array.isArray(tampered.rounds) && tampered.rounds.length > 0) {
    tampered.rounds[0].zMsg[0] = tampered.rounds[0].zMsg[0] + 1;
    return tampered;
  }
  if ('aCommits' in tampered && Array.isArray(tampered.zMsgs) && tampered.zMsgs.length > 0) {
    tampered.zMsgs[0][0] = tampered.zMsgs[0][0] + 1;
    return tampered;
  }
  tampered.zMsg[0] = tampered.zMsg[0] + 1;
  return tampered;
}

function truncateNullifierProof(proof: NullifierProofLike): NullifierProofLike {
  const truncated = cloneJson(proof);
  if ('rounds' in truncated && Array.isArray(truncated.rounds) && truncated.rounds.length > 0) {
    truncated.rounds = truncated.rounds.slice(0, truncated.rounds.length - 1);
    return truncated;
  }
  if ('aCommits' in truncated && Array.isArray(truncated.zMsgs) && truncated.zMsgs.length > 0) {
    truncated.zMsgs = truncated.zMsgs.slice(0, truncated.zMsgs.length - 1);
    return truncated;
  }
  return {
    aCommits: [truncated.aCommit],
    aNullifiers: [truncated.aNullifier],
    zMsgs: [],
    zRands: [truncated.zRand],
  };
}

function tamperRangeProof(proof: RangeProofLike): RangeProofLike {
  const tampered = cloneJson(proof);
  if ('rounds' in tampered && Array.isArray(tampered.rounds) && tampered.rounds.length > 0) {
    const round = tampered.rounds[0] as { amountZ?: IntVec };
    if (round.amountZ && round.amountZ.length > 0) {
      round.amountZ[0] = round.amountZ[0] + 1;
    }
    return tampered;
  }
  if ('amountAs' in tampered && Array.isArray(tampered.amountZs) && tampered.amountZs.length > 0) {
    tampered.amountZs[0][0] = tampered.amountZs[0][0] + 1;
    return tampered;
  }
  tampered.amountZ[0] = tampered.amountZ[0] + 1;
  return tampered;
}

function truncateRangeProof(proof: RangeProofLike): RangeProofLike {
  const truncated = cloneJson(proof);
  if ('rounds' in truncated && Array.isArray(truncated.rounds) && truncated.rounds.length > 0) {
    truncated.rounds = truncated.rounds.slice(0, truncated.rounds.length - 1);
    return truncated;
  }
  if ('amountAs' in truncated && Array.isArray(truncated.amountZs) && truncated.amountZs.length > 0) {
    truncated.amountZs = truncated.amountZs.slice(0, truncated.amountZs.length - 1);
    return truncated;
  }
  return {
    bits: truncated.bits,
    comps: truncated.comps,
    amountAs: [],
    amountZs: [],
    pairAss: [truncated.pairAs],
    pairZss: [truncated.pairZs],
  };
}

function enumerateVectors(length: number, bound: number): IntMatrix {
  if (length === 0) {
    return [[]];
  }
  const tails = enumerateVectors(length - 1, bound);
  const result: IntMatrix = [];
  for (let head = -bound; head <= bound; head += 1) {
    for (const tail of tails) {
      result.push([head, ...tail]);
    }
  }
  return result;
}

function vecKey(v: IntVec): string {
  return JSON.stringify(v);
}

async function loadSdk() {
  return import(pathToFileURL(typeScriptEntry).href);
}

async function main(): Promise<void> {
  const sdk = await loadSdk();
  console.log('audit-confidential: probing repaired confidential transaction surface');
  const safeBool = (thunk: () => boolean): boolean => {
    try {
      return thunk();
    } catch {
      return false;
    }
  };
  const safeNullable = <T>(thunk: () => T): T | null => {
    try {
      return thunk();
    } catch {
      return null;
    }
  };
  const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
  const gamma = 5;
  const k = 3;
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const nk = [
    [1, 0, 0],
    [0, 1, 0],
  ];

  const commitOfOpening = (opening: CommitOpening): IntVec =>
    sdk.Zq.matVecMultMod(ck, sdk.Vec.concat(opening.msg, opening.rand), params.q);

  const validWitnesses = enumerateVectors(params.n2, 64).filter((r) =>
    sdk.ConfidentialBalance.validWitness(params, r)
  );
  const witnessImage = new Map<string, IntVec>();
  for (const r of validWitnesses) {
    witnessImage.set(
      vecKey(sdk.ConfidentialBalance.randCommit(params, ck, r)),
      r
    );
  }
  const statementSpaceSize = params.q ** params.m;

  console.log('audit-confidential: derived witness image summary');

  const forgeBalanceProof = (statement: IntVec): BalanceProofLike | null => {
    for (const y of enumerateVectors(params.n2, gamma)) {
      if (!sdk.ConfidentialBalance.validMask(params, gamma, y)) {
        continue;
      }
      const a = sdk.ConfidentialBalance.sigmaCommit(params, ck, y);
      const challenge = sdk.ConfidentialBalance.canonicalChallenge(params, ck, statement, a);
      if (challenge !== 0) {
        continue;
      }
      const proof = { a, z: y };
      if (sdk.ConfidentialBalance.fsVerify(params, gamma, ck, statement, proof)) {
        return proof;
      }
    }
    return null;
  };

  const emptyRangeProof = {
    bits: [],
    comps: [],
    amountAs: Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => [0, 0]),
    amountZs: Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => [0, 0]),
    pairAss: Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => []),
    pairZss: Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => []),
  };

  const opening5 = { msg: [5], rand: [1, 2] };
  const opening2 = { msg: [2], rand: [1, 0] };
  const bitOpenings5 = [
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 1] },
  ];
  const compOpenings5 = [
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, -1] },
  ];
  const fsRounds = sdk.ConfidentialBalance.fsRounds();
  const runFullSemanticAudit =
    process.env.ISABELLA_CONFIDENTIAL_AUDIT_FULL === '1' || fsRounds <= 32;
  if (!runFullSemanticAudit) {
    console.log(
      `audit-confidential: skipping full semantic fixture for ${fsRounds} FS rounds; set ISABELLA_CONFIDENTIAL_AUDIT_FULL=1 to run it`
    );
  }
  const yAmount5 = Array.from({ length: fsRounds }, () => [0, 1]);
  const yPairs5 = Array.from({ length: fsRounds }, () => [
    [1, 0],
    [0, 0],
    [1, -1],
  ]);
  const bitOpenings2 = [
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 0] },
  ];
  const compOpenings2 = [
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 1] },
  ];
  const yAmount2 = Array.from({ length: fsRounds }, () => [1, 0]);
  const yPairs2 = Array.from({ length: fsRounds }, () => [
    [0, 1],
    [1, 0],
    [0, 0],
  ]);

  const cAmount5 = commitOfOpening(opening5);
  const balanceProofShapeProbe = (() => {
    const witness = [1, 2];
    const mask = [0, 1];
    const masks = Array.from({ length: sdk.ConfidentialBalance.fsRounds() }, () => mask);
    const c = sdk.ConfidentialBalance.randCommit(params, ck, witness);
    const proof = sdk.ConfidentialBalance.fsProve(params, gamma, ck, c, witness, masks);
    return proof === null ? 'unavailable' : balanceProofShape(proof as BalanceProofLike);
  })();
  const emptyBitRangeProofAccepted = safeBool(() =>
    sdk.ConfidentialRange.fsVerify(
      params,
      gamma,
      k,
      ck,
      cAmount5,
      emptyRangeProof
    )
  );

  const balanceFalseStatement = balanceProofShapeProbe === 'single' ? (() => {
    for (let x = 0; x < params.q; x += 1) {
      for (let y = 0; y < params.q; y += 1) {
        const candidate = [x, y];
        if (witnessImage.has(vecKey(candidate))) {
          continue;
        }
        const proof = forgeBalanceProof(candidate);
        if (proof !== null) {
          return { statement: candidate, proof };
        }
      }
    }
    return null;
  })() : null;

  const opIn1 = { msg: [4], rand: [1, 0] };
  const opIn2 = { msg: [3], rand: [0, 1] };
  const in1Bits = [
    { msg: [0], rand: [0, 1] },
    { msg: [0], rand: [1, 0] },
    { msg: [1], rand: [1, 1] },
  ];
  const in1Comps = [
    { msg: [1], rand: [1, 0] },
    { msg: [1], rand: [0, 1] },
    { msg: [0], rand: [0, -1] },
  ];
  const in2Bits = [
    { msg: [1], rand: [1, 0] },
    { msg: [1], rand: [0, 1] },
    { msg: [0], rand: [0, 0] },
  ];
  const in2Comps = [
    { msg: [0], rand: [0, 1] },
    { msg: [0], rand: [1, 0] },
    { msg: [1], rand: [1, 1] },
  ];
  const cIn1 = commitOfOpening(opIn1);
  const cIn2 = commitOfOpening(opIn2);
  const nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn1);
  const nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn2);
  const ledger = [cIn1, cIn2, [9, 4]];
  const root = sdk.ConfidentialTransaction.ledgerRoot(params, ledger);
  const spent: IntMatrix = [];

  const outputs = [
    {
      name: 'amount-5',
      opening: opening5,
      bits: bitOpenings5,
      comps: compOpenings5,
      yAmount: yAmount5,
      yPairs: yPairs5,
    },
    {
      name: 'amount-2',
      opening: opening2,
      bits: bitOpenings2,
      comps: compOpenings2,
      yAmount: yAmount2,
      yPairs: yPairs2,
    },
  ];

  const semanticGap = (() => {
    for (const out1 of outputs) {
      for (const out2 of outputs) {
        const sumIn = opIn1.msg[0] + opIn2.msg[0];
        const sumOut = out1.opening.msg[0] + out2.opening.msg[0];
        if (sumIn === sumOut) {
          continue;
        }
        const cOut1 = commitOfOpening(out1.opening);
        const cOut2 = commitOfOpening(out2.opening);
        const balanceCommitment = sdk.ConfidentialBalance.balanceCommitment(
          cIn1,
          cIn2,
          cOut1,
          cOut2,
          params.q
        );
        const witness = witnessImage.get(vecKey(balanceCommitment));
        if (witness !== undefined) {
          return {
            outputs: [out1.name, out2.name],
            balanceCommitment,
            witness,
            amountDelta: sumOut - sumIn,
          };
        }
      }
    }
    return null;
  })();

  const legacyForgingSurfaceEnabled = balanceProofShapeProbe === 'single';
  const honestRangeProof5 = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialRange.fsProve(
          params,
          gamma,
          k,
          ck,
          cAmount5,
          opening5,
          bitOpenings5,
          compOpenings5,
          yAmount5,
          yPairs5
        )
      )
    : null;
  const honestNullifierProof1 = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialTransaction.nullifierFsProve(
          params,
          gamma,
          ck,
          nk,
          cIn1,
          nf1,
          opIn1,
          Array.from({ length: fsRounds }, () => ({ msg: [0], rand: [1, 0] }))
        )
      )
    : null;
  const honestNullifierProof2 = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialTransaction.nullifierFsProve(
          params,
          gamma,
          ck,
          nk,
          cIn2,
          nf2,
          opIn2,
          Array.from({ length: fsRounds }, () => ({ msg: [1], rand: [0, 1] }))
        )
      )
    : null;
  const in1Member = legacyForgingSurfaceEnabled
    ? safeNullable(() => sdk.ConfidentialTransaction.membershipProve(params, ledger, cIn1))
    : null;
  const in2Member = legacyForgingSurfaceEnabled
    ? safeNullable(() => sdk.ConfidentialTransaction.membershipProve(params, ledger, cIn2))
    : null;
  const honestInputRangeProof1 = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialRange.fsProve(
          params,
          gamma,
          k,
          ck,
          cIn1,
          opIn1,
          in1Bits,
          in1Comps,
          yAmount5,
          yPairs5
        )
      )
    : null;
  const honestInputRangeProof2 = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialRange.fsProve(
          params,
          gamma,
          k,
          ck,
          cIn2,
          opIn2,
          in2Bits,
          in2Comps,
          yAmount2,
          yPairs2
        )
      )
    : null;
  const honestNotes =
    honestInputRangeProof1 !== null && honestInputRangeProof2 !== null
      ? [
          { commitment: cIn1, rangeProof: honestInputRangeProof1 },
          { commitment: cIn2, rangeProof: honestInputRangeProof2 },
        ]
      : null;
  const honestTransactionProof = legacyForgingSurfaceEnabled
    ? safeNullable(() =>
        sdk.ConfidentialTransaction.fsProve(
          params,
          gamma,
          k,
          ck,
          nk,
          ledger,
          spent,
          cIn1,
          cIn2,
          cAmount5,
          commitOfOpening(opening2),
          nf1,
          nf2,
          opIn1,
          opIn2,
          opening5,
          opening2,
          bitOpenings5,
          compOpenings5,
          bitOpenings2,
          compOpenings2,
          Array.from({ length: fsRounds }, () => ({ msg: [0], rand: [1, 0] })),
          Array.from({ length: fsRounds }, () => ({ msg: [1], rand: [0, 1] })),
          Array.from({ length: fsRounds }, () => [0, 1]),
          yAmount5,
          yPairs5,
          yAmount2,
          yPairs2
        )
      )
    : null;
  const semanticNk = [
    [0, 1, 0],
    [1, 0, 0],
  ];
  const semanticRangeK = 1;
  const semanticOpIn1 = { msg: [1], rand: [1, 0] };
  const semanticOpIn2 = { msg: [1], rand: [0, 1] };
  const semanticOpOut1 = { msg: [1], rand: [1, 1] };
  const semanticOpOut2 = { msg: [1], rand: [0, 0] };
  const semanticIn1Bits = [{ msg: [1], rand: [1, 0] }];
  const semanticIn1Comps = [{ msg: [0], rand: [0, 0] }];
  const semanticIn2Bits = [{ msg: [1], rand: [0, 1] }];
  const semanticIn2Comps = [{ msg: [0], rand: [0, 0] }];
  const semanticOut1Bits = [{ msg: [1], rand: [1, 1] }];
  const semanticOut1Comps = [{ msg: [0], rand: [0, 0] }];
  const semanticOut2Bits = [{ msg: [1], rand: [0, 0] }];
  const semanticOut2Comps = [{ msg: [0], rand: [0, 0] }];
  const semanticYIn1 = Array.from({ length: fsRounds }, () => ({ msg: [0], rand: [1, 0] }));
  const semanticYIn2 = Array.from({ length: fsRounds }, () => ({ msg: [1], rand: [0, 1] }));
  const semanticYBalance = Array.from({ length: fsRounds }, () => [0, 1]);
  const semanticYOut1 = Array.from({ length: fsRounds }, () => [0, 1]);
  const semanticYOut1Pairs = Array.from({ length: fsRounds }, () => [[0, 0]]);
  const semanticYOut2 = Array.from({ length: fsRounds }, () => [1, 0]);
  const semanticYOut2Pairs = Array.from({ length: fsRounds }, () => [[0, 0]]);
  const semanticCIn1 = commitOfOpening(semanticOpIn1);
  const semanticCIn2 = commitOfOpening(semanticOpIn2);
  const semanticCOut1 = commitOfOpening(semanticOpOut1);
  const semanticCOut2 = commitOfOpening(semanticOpOut2);
  const semanticSpent: IntMatrix = [];
  const semanticLedger = [semanticCIn1, semanticCIn2];
  const semanticLedgerRoot = sdk.ConfidentialTransaction.ledgerRoot(params, semanticLedger);
  const semanticNf1 = sdk.ConfidentialTransaction.nullifier(params, semanticNk, semanticOpIn1);
  const semanticNf2 = sdk.ConfidentialTransaction.nullifier(params, semanticNk, semanticOpIn2);
  const semanticIn1RangeProof = runFullSemanticAudit ? safeNullable(() =>
    sdk.ConfidentialRange.fsProve(
      params,
      gamma,
      semanticRangeK,
      ck,
      semanticCIn1,
      semanticOpIn1,
      semanticIn1Bits,
      semanticIn1Comps,
      semanticYOut1,
      semanticYOut1Pairs
    )
  ) : null;
  const semanticIn2RangeProof = runFullSemanticAudit ? safeNullable(() =>
    sdk.ConfidentialRange.fsProve(
      params,
      gamma,
      semanticRangeK,
      ck,
      semanticCIn2,
      semanticOpIn2,
      semanticIn2Bits,
      semanticIn2Comps,
      semanticYOut2,
      semanticYOut2Pairs
    )
  ) : null;
  const semanticNotes =
    semanticIn1RangeProof !== null && semanticIn2RangeProof !== null
      ? [
          { commitment: semanticCIn1, rangeProof: semanticIn1RangeProof },
          { commitment: semanticCIn2, rangeProof: semanticIn2RangeProof },
        ]
      : null;
  const semanticTransactionProof = runFullSemanticAudit ? safeNullable(() =>
    sdk.ConfidentialTransaction.fsProve(
      params,
      gamma,
      semanticRangeK,
      ck,
      semanticNk,
      semanticLedger,
      semanticSpent,
      semanticCIn1,
      semanticCIn2,
      semanticCOut1,
      semanticCOut2,
      semanticNf1,
      semanticNf2,
      semanticOpIn1,
      semanticOpIn2,
      semanticOpOut1,
      semanticOpOut2,
      semanticOut1Bits,
      semanticOut1Comps,
      semanticOut2Bits,
      semanticOut2Comps,
      semanticYIn1,
      semanticYIn2,
      semanticYBalance,
      semanticYOut1,
      semanticYOut1Pairs,
      semanticYOut2,
      semanticYOut2Pairs
    )
  ) : null;
  const forgedBalance = legacyForgingSurfaceEnabled
    ? forgeBalanceProof(
        sdk.ConfidentialBalance.balanceCommitment(cIn1, cIn2, cAmount5, cAmount5, params.q)
      )
    : null;

  const semanticLedgerStepApi =
    typeof sdk.ConfidentialTransaction.semanticStepValid === 'function'
      ? 'semanticStepValid'
      : typeof sdk.ConfidentialTransaction.ledgerStepValid === 'function'
      ? 'ledgerStepValid'
      : null;
  const semanticLedgerStepVerifier =
    semanticLedgerStepApi === null
      ? null
      : sdk.ConfidentialTransaction[semanticLedgerStepApi];

  let forgedTransactionAccepted = false;
  let snapshotLedgerStillValidAfterForgedTx = false;
  let semanticLedgerStepStillAcceptsForgedTx:
    | { checked: false; reason: string }
    | { checked: true; accepted: boolean } = semanticLedgerStepVerifier === null
      ? { checked: false, reason: 'no semantic ledger-step verifier is currently exported on the TypeScript surface' }
      : { checked: false, reason: 'semantic ledger-step verifier is available but no forged proof candidate has been constructed yet' };
  if (
    honestRangeProof5 !== null &&
    honestNullifierProof1 !== null &&
    honestNullifierProof2 !== null &&
    in1Member !== null &&
    in2Member !== null &&
    forgedBalance !== null
  ) {
    const forgedProof: TransactionProof = {
      in1Member,
      in2Member,
      in1Nullifier: honestNullifierProof1,
      in2Nullifier: honestNullifierProof2,
      balance: forgedBalance,
      out1Range: honestRangeProof5,
      out2Range: honestRangeProof5,
    };
    forgedTransactionAccepted = safeBool(() =>
      sdk.ConfidentialTransaction.fsVerify(
        params,
        gamma,
        k,
        ck,
        nk,
        root,
        spent,
        cIn1,
        cIn2,
        cAmount5,
        cAmount5,
        nf1,
        nf2,
        forgedProof
      )
    );

    const initialNotes: VerifiedNote[] = [
      { commitment: cIn1, rangeProof: honestRangeProof5 },
      { commitment: cIn2, rangeProof: honestRangeProof5 },
    ];
    const updatedNotes = safeNullable(() =>
      sdk.ConfidentialTransaction.ledgerApplyNotes(
        initialNotes,
        forgedProof,
        cAmount5,
        cAmount5
      )
    );
    const updatedSpent = safeNullable(() =>
      sdk.ConfidentialTransaction.ledgerApplySpent(spent, nf1, nf2)
    );
    snapshotLedgerStillValidAfterForgedTx =
      updatedNotes !== null &&
      updatedSpent !== null &&
      safeBool(() =>
        sdk.ConfidentialTransaction.ledgerValid(
          params,
          gamma,
          k,
          ck,
          sdk.ConfidentialTransaction.ledgerRoot(params, [cAmount5, cAmount5]),
          updatedNotes,
          updatedSpent
        )
      );
    if (semanticLedgerStepVerifier !== null) {
      semanticLedgerStepStillAcceptsForgedTx = {
        checked: true,
        accepted: safeBool(() =>
          semanticLedgerStepVerifier(
            params,
            gamma,
            k,
            ck,
            nk,
            initialNotes,
            spent,
            cIn1,
            cIn2,
            cAmount5,
            cAmount5,
            nf1,
            nf2,
            forgedProof
          )
        ),
      };
    }
  } else if (semanticLedgerStepVerifier !== null && balanceProofShapeProbe !== 'single') {
    semanticLedgerStepStillAcceptsForgedTx = {
      checked: false,
      reason: `no forged proof candidate was constructed for repaired balance proof shape ${balanceProofShapeProbe}`,
    };
  }

  const honestSemanticLedgerStepAccepted:
    | { checked: false; reason: string }
    | { checked: true; accepted: boolean } = semanticLedgerStepVerifier === null
      ? { checked: false, reason: 'no semantic ledger-step verifier is currently exported on the TypeScript surface' }
      : !runFullSemanticAudit
      ? { checked: false, reason: `full semantic fixture skipped for ${fsRounds} Fiat-Shamir rounds` }
      : semanticTransactionProof === null || semanticNotes === null
      ? { checked: false, reason: 'no honest semantic ledger-step fixture was constructed' }
      : {
          checked: true,
          accepted: safeBool(() =>
            semanticLedgerStepVerifier(
              params,
              gamma,
              semanticRangeK,
              ck,
              semanticNk,
              semanticNotes,
              semanticSpent,
              semanticCIn1,
              semanticCIn2,
              semanticCOut1,
              semanticCOut2,
              semanticNf1,
              semanticNf2,
              semanticTransactionProof
            )
          ),
        };

  const tamperingChecks:
    | { checked: false; reason: string }
    | {
        checked: true;
        membershipRejected: boolean;
        membershipPathRejected: boolean;
        nullifierRejected: boolean;
        nullifierTruncationRejected: boolean;
        rangeRejected: boolean;
        rangeTruncationRejected: boolean;
        swappedMembershipRejected: boolean;
        swappedNullifierRejected: boolean;
        swappedOutputRangeRejected: boolean;
      } = semanticTransactionProof === null || semanticNotes === null
      ? { checked: false, reason: 'no honest semantic transaction proof fixture was constructed' }
      : (() => {
          const verifyTransactionProof = (proof: TransactionProof): boolean =>
            safeBool(() =>
              sdk.ConfidentialTransaction.fsVerify(
                params,
                gamma,
                semanticRangeK,
                ck,
                semanticNk,
                semanticLedgerRoot,
                semanticSpent,
                semanticCIn1,
                semanticCIn2,
                semanticCOut1,
                semanticCOut2,
                semanticNf1,
                semanticNf2,
                proof
              )
            );
          const verifyNullifierProof = (proof: NullifierProofLike): boolean =>
            safeBool(() =>
              sdk.ConfidentialTransaction.nullifierFsVerify(
                params,
                gamma,
                ck,
                semanticNk,
                semanticCIn1,
                semanticNf1,
                proof
              )
            );
          const verifyRangeProof = (proof: RangeProofLike): boolean =>
            safeBool(() =>
              sdk.ConfidentialRange.fsVerify(
                params,
                gamma,
                semanticRangeK,
                ck,
                semanticCOut1,
                proof
              )
            );
          const tamperedMembershipTransaction: TransactionProof = {
            ...semanticTransactionProof,
            in1Member: tamperMembershipProof(semanticTransactionProof.in1Member),
          };
          const tamperedMembershipPathTransaction: TransactionProof = {
            ...semanticTransactionProof,
            in1Member: tamperMembershipPath(semanticTransactionProof.in1Member),
          };
          const swappedMembershipTransaction: TransactionProof = {
            ...semanticTransactionProof,
            in1Member: semanticTransactionProof.in2Member,
            in2Member: semanticTransactionProof.in1Member,
          };
          const swappedNullifierTransaction: TransactionProof = {
            ...semanticTransactionProof,
            in1Nullifier: semanticTransactionProof.in2Nullifier,
            in2Nullifier: semanticTransactionProof.in1Nullifier,
          };
          const swappedOutputRangeTransaction: TransactionProof = {
            ...semanticTransactionProof,
            out1Range: semanticTransactionProof.out2Range,
            out2Range: semanticTransactionProof.out1Range,
          };
          return {
            checked: true,
            membershipRejected: !verifyTransactionProof(tamperedMembershipTransaction),
            membershipPathRejected: !verifyTransactionProof(tamperedMembershipPathTransaction),
            nullifierRejected: !verifyNullifierProof(tamperNullifierProof(semanticTransactionProof.in1Nullifier)),
            nullifierTruncationRejected: !verifyNullifierProof(truncateNullifierProof(semanticTransactionProof.in1Nullifier)),
            rangeRejected: !verifyRangeProof(tamperRangeProof(semanticTransactionProof.out1Range)),
            rangeTruncationRejected: !verifyRangeProof(truncateRangeProof(semanticTransactionProof.out1Range)),
            swappedMembershipRejected: !verifyTransactionProof(swappedMembershipTransaction),
            swappedNullifierRejected: !verifyTransactionProof(swappedNullifierTransaction),
            swappedOutputRangeRejected: !verifyTransactionProof(swappedOutputRangeTransaction),
          };
        })();

  const report = {
    protocolSurface: {
      balanceProofShape: balanceProofShapeProbe,
      rangeProofShape:
        semanticTransactionProof === null
          ? 'unavailable'
          : rangeProofShape(semanticTransactionProof.out1Range as RangeProofLike),
      nullifierProofShape:
        semanticTransactionProof === null
          ? 'unavailable'
          : nullifierProofShape(semanticTransactionProof.in1Nullifier as NullifierProofLike),
      semanticLedgerStepApi,
    },
    remediatedChecks: {
      emptyBitRangeProofRejectedUnderExplicitK: !emptyBitRangeProofAccepted,
      honestSemanticLedgerStepAccepted,
      tamperingChecks,
    },
    criticalFindings: {
      balanceWitnessImageCoverage: {
        reachableStatements: witnessImage.size,
        totalStatements: statementSpaceSize,
        coversWholeSpace: witnessImage.size === statementSpaceSize,
      },
      forgedBalanceProofOnFalseStatement:
        balanceProofShapeProbe !== 'single'
          ? {
              found: false,
              reason: `legacy single-round balance forgery search skipped for repaired proof shape ${balanceProofShapeProbe}`,
            }
          : balanceFalseStatement === null
          ? {
              found: false,
              reason:
                witnessImage.size === statementSpaceSize
                  ? 'every commitment in Z_q^m is reachable by some valid balance witness under this key'
                  : 'no false statement with a self-consistent false challenge was found in the full commitment space search',
            }
          : {
              found: true,
              statement: balanceFalseStatement.statement,
              proof: {
                shape: balanceProofShape(balanceFalseStatement.proof),
                rounds: normalizeBalanceProof(balanceFalseStatement.proof),
              },
            },
      relationAbsorbsUnbalancedTransfer: semanticGap,
      forgedUnbalancedTransactionAccepted: forgedTransactionAccepted,
      snapshotLedgerStillValidAfterForgedTx,
      semanticLedgerStepStillAcceptsForgedTx,
    },
  };

  console.log(JSON.stringify(report, null, 2));

  const hasCriticalFinding =
    report.criticalFindings.balanceWitnessImageCoverage.coversWholeSpace ||
    report.criticalFindings.relationAbsorbsUnbalancedTransfer !== null ||
    report.criticalFindings.forgedUnbalancedTransactionAccepted ||
    report.criticalFindings.snapshotLedgerStillValidAfterForgedTx ||
    (report.remediatedChecks.honestSemanticLedgerStepAccepted.checked &&
      !report.remediatedChecks.honestSemanticLedgerStepAccepted.accepted) ||
    (report.remediatedChecks.tamperingChecks.checked &&
      (!report.remediatedChecks.tamperingChecks.membershipRejected ||
        !report.remediatedChecks.tamperingChecks.membershipPathRejected ||
        !report.remediatedChecks.tamperingChecks.nullifierRejected ||
        !report.remediatedChecks.tamperingChecks.nullifierTruncationRejected ||
        !report.remediatedChecks.tamperingChecks.rangeRejected ||
        !report.remediatedChecks.tamperingChecks.rangeTruncationRejected ||
        !report.remediatedChecks.tamperingChecks.swappedMembershipRejected ||
        !report.remediatedChecks.tamperingChecks.swappedNullifierRejected ||
        !report.remediatedChecks.tamperingChecks.swappedOutputRangeRejected)) ||
    (report.criticalFindings.semanticLedgerStepStillAcceptsForgedTx.checked &&
      report.criticalFindings.semanticLedgerStepStillAcceptsForgedTx.accepted);

  process.exitCode = hasCriticalFinding ? 1 : 0;
}

main().catch((error) => {
  console.error(error);
  process.exitCode = 1;
});
