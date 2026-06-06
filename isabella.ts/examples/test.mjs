/**
 * Isabella TypeScript Library Tests
 *
 * Run with: node --test examples/test.mjs
 */

import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
import {
  Zq,
  Vec,
  Mat,
  Dilithium,
  ConfidentialBalance,
  ConfidentialRange,
  ConfidentialTransaction,
} from '../dist/index.js';

function normalizeSignedZero(value) {
  if (Array.isArray(value)) {
    return value.map(normalizeSignedZero);
  }
  return Object.is(value, -0) ? 0 : value;
}

function balanceProofShape(proof) {
  if (proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  if (proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return 'lists';
  }
  return 'single';
}

function normalizeBalanceProof(proof) {
  if (proof && Array.isArray(proof.rounds)) {
    return proof.rounds;
  }
  if (proof && Array.isArray(proof.as) && Array.isArray(proof.zs)) {
    return proof.as.map((a, index) => ({
      a,
      z: proof.zs[index],
      challenge: proof.challenges?.[index],
    }));
  }
  return [{ a: proof.a, z: proof.z }];
}

function tamperBalanceProof(proof) {
  if (proof && Array.isArray(proof.rounds) && proof.rounds.length > 0) {
    return {
      ...proof,
      rounds: proof.rounds.map((round, index) =>
        index === 0 ? { ...round, z: [round.z[0] + 1, ...round.z.slice(1)] } : round
      ),
    };
  }
  if (proof && Array.isArray(proof.as) && Array.isArray(proof.zs) && proof.zs.length > 0) {
    return {
      ...proof,
      zs: proof.zs.map((z, index) => (index === 0 ? [z[0] + 1, ...z.slice(1)] : z)),
    };
  }
  return { a: proof.a, z: [proof.z[0] + 1, proof.z[1]] };
}

function rangeProofShape(proof) {
  if (
    proof &&
    Array.isArray(proof.bits) &&
    Array.isArray(proof.comps) &&
    Array.isArray(proof.pairAs) &&
    Array.isArray(proof.pairZs)
  ) {
    return 'legacy';
  }
  if (proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  if (proof && (Array.isArray(proof.amountAs) || Array.isArray(proof.amountZs) || Array.isArray(proof.pairAss) || Array.isArray(proof.pairZss))) {
    return 'lists';
  }
  return 'unknown';
}

function normalizeRangeProof(proof, context) {
  const shape = rangeProofShape(proof);
  if (shape === 'legacy') {
    return {
      bits: proof.bits,
      comps: proof.comps,
      rounds: [
        {
          amountA: proof.amountA,
          amountZ: proof.amountZ,
          pairAs: proof.pairAs,
          pairZs: proof.pairZs,
        },
      ],
    };
  }
  if (shape === 'rounds') {
    return proof;
  }
  if (shape === 'lists') {
    return {
      bits: proof.bits,
      comps: proof.comps,
      rounds: proof.amountAs.map((amountA, index) => ({
        amountA,
        amountZ: proof.amountZs[index],
        pairAs: proof.pairAss[index],
        pairZs: proof.pairZss[index],
        challenge: proof.challenges?.[index],
      })),
    };
  }
  throw new Error(`${context} has unknown range-proof serialization (shape=${shape}).`);
}

function tamperRangeProof(proof) {
  const shape = rangeProofShape(proof);
  if (shape === 'legacy') {
    return {
      ...proof,
      amountZ: [proof.amountZ[0] + 1, ...proof.amountZ.slice(1)],
    };
  }
  if (shape === 'rounds') {
    return {
      ...proof,
      rounds: proof.rounds.map((round, index) =>
        index === 0
          ? { ...round, amountZ: [round.amountZ[0] + 1, ...round.amountZ.slice(1)] }
          : round
      ),
    };
  }
  if (shape === 'lists') {
    return {
      ...proof,
      amountZs: proof.amountZs.map((amountZ, index) =>
        index === 0 ? [amountZ[0] + 1, ...amountZ.slice(1)] : amountZ
      ),
    };
  }
  throw new Error(`Cannot tamper unknown range-proof serialization (shape=${shape}).`);
}

function nullifierProofShape(proof) {
  if (
    proof &&
    Array.isArray(proof.aCommits) &&
    Array.isArray(proof.aNullifiers) &&
    Array.isArray(proof.zMsgs) &&
    Array.isArray(proof.zRands)
  ) {
    return 'lists';
  }
  if (proof && Array.isArray(proof.rounds)) {
    return 'rounds';
  }
  return 'legacy';
}

describe('Zq - Modular Arithmetic', () => {
  test('modCentered basic cases', () => {
    assert.equal(Zq.modCentered(0, 5), 0);
    assert.equal(Zq.modCentered(2, 5), 2);
    assert.equal(Zq.modCentered(3, 5), -2);
    assert.equal(Zq.modCentered(7, 5), 2);
    assert.equal(Zq.modCentered(-3, 5), 2);
  });

  test('modCentered range property', () => {
    const q = 17;
    for (let x = -50; x <= 50; x++) {
      const r = Zq.modCentered(x, q);
      assert.ok(r > -q/2 && r <= q/2, `modCentered(${x}, ${q}) = ${r} not in range`);
    }
  });

  test('vecMod', () => {
    assert.deepEqual(Zq.vecMod([0, 5, 10, 15], 7), [0, 5, 3, 1]);
  });

  test('vecModCentered', () => {
    assert.deepEqual(Zq.vecModCentered([0, 5, 10, 15], 7), [0, -2, 3, 1]);
  });

  test('dist0 is non-negative', () => {
    const q = 13;
    for (let x = -20; x <= 20; x++) {
      assert.ok(Zq.dist0(q, x) >= 0, `dist0(${q}, ${x}) should be non-negative`);
    }
  });

  test('dist0 equals abs of modCentered', () => {
    const q = 17;
    for (let x = -30; x <= 30; x++) {
      // Use |0 to convert to integer, which normalizes -0 to 0
      const d = Zq.dist0(q, x) | 0;
      const expected = Math.abs(Zq.modCentered(x, q)) | 0;
      assert.equal(d, expected);
    }
  });

  test('encodeBit values', () => {
    assert.equal(Zq.encodeBit(17, false), 0);
    assert.equal(Zq.encodeBit(17, true), 8);  // 17 div 2 = 8
    assert.equal(Zq.encodeBit(100, false), 0);
    assert.equal(Zq.encodeBit(100, true), 50);
  });

  test('decodeBit roundtrip', () => {
    for (const q of [17, 97, 256]) {
      assert.equal(Zq.decodeBit(q, Zq.encodeBit(q, false)), false);
      assert.equal(Zq.decodeBit(q, Zq.encodeBit(q, true)), true);
    }
  });

  test('decodeBit threshold', () => {
    const q = 17;
    // Values close to 0 decode to false
    assert.equal(Zq.decodeBit(q, 0), false);
    assert.equal(Zq.decodeBit(q, 1), false);
    assert.equal(Zq.decodeBit(q, 4), false);  // q/4 = 4
    // Values close to q/2 decode to true
    assert.equal(Zq.decodeBit(q, 8), true);   // q/2 = 8
    assert.equal(Zq.decodeBit(q, 9), true);
  });

  test('matVecMultMod', () => {
    const A = [[1, 2], [3, 4]];
    const v = [5, 6];
    const q = 10;
    // [1*5+2*6, 3*5+4*6] = [17, 39] mod 10 = [7, 9]
    assert.deepEqual(Zq.matVecMultMod(A, v, q), [7, 9]);
  });
});

describe('Vec - Vector Operations', () => {
  test('add', () => {
    assert.deepEqual(Vec.add([1, 2, 3], [4, 5, 6]), [5, 7, 9]);
    assert.deepEqual(Vec.add([], []), []);
  });

  test('sub', () => {
    assert.deepEqual(Vec.sub([5, 7, 9], [1, 2, 3]), [4, 5, 6]);
    assert.deepEqual(Vec.sub([1, 2], [3, 4]), [-2, -2]);
  });

  test('scale', () => {
    assert.deepEqual(Vec.scale(3, [1, 2, 3]), [3, 6, 9]);
    assert.deepEqual(Vec.scale(0, [1, 2, 3]), [0, 0, 0]);
    assert.deepEqual(Vec.scale(-1, [1, 2, 3]), [-1, -2, -3]);
  });

  test('neg', () => {
    assert.deepEqual(Vec.neg([1, -2, 3]), [-1, 2, -3]);
    assert.deepEqual(Vec.neg([]), []);
  });

  test('neg equals scale by -1', () => {
    const v = [1, -2, 3, 0, -5];
    assert.deepEqual(Vec.neg(v), Vec.scale(-1, v));
  });

  test('dot', () => {
    assert.equal(Vec.dot([1, 2, 3], [4, 5, 6]), 32);  // 4+10+18
    assert.equal(Vec.dot([], []), 0);
    assert.equal(Vec.dot([1, 0], [0, 1]), 0);  // orthogonal
  });

  test('concat', () => {
    assert.deepEqual(Vec.concat([1, 2], [3, 4, 5]), [1, 2, 3, 4, 5]);
    assert.deepEqual(Vec.concat([], [1, 2]), [1, 2]);
    assert.deepEqual(Vec.concat([1, 2], []), [1, 2]);
  });

  test('split', () => {
    assert.deepEqual(Vec.split(2, [1, 2, 3, 4, 5]), [[1, 2], [3, 4, 5]]);
    assert.deepEqual(Vec.split(0, [1, 2, 3]), [[], [1, 2, 3]]);
    assert.deepEqual(Vec.split(3, [1, 2, 3]), [[1, 2, 3], []]);
  });

  test('split and concat are inverses', () => {
    const v = [1, 2, 3, 4, 5];
    for (let n = 0; n <= v.length; n++) {
      const [left, right] = Vec.split(n, v);
      assert.deepEqual(Vec.concat(left, right), v);
    }
  });

  test('isValid', () => {
    assert.equal(Vec.isValid(3, [1, 2, 3]), true);
    assert.equal(Vec.isValid(2, [1, 2, 3]), false);
    assert.equal(Vec.isValid(0, []), true);
  });
});

describe('Mat - Matrix Operations', () => {
  test('vecMult', () => {
    const A = [[1, 2, 3], [4, 5, 6]];
    const v = [1, 1, 1];
    assert.deepEqual(Mat.vecMult(A, v), [6, 15]);
  });

  test('vecMult with single row', () => {
    const A = [[2, 3, 4]];
    const v = [1, 2, 3];
    assert.deepEqual(Mat.vecMult(A, v), [20]);  // 2+6+12
  });

  test('transpose', () => {
    const A = [[1, 2, 3], [4, 5, 6]];
    const At = [[1, 4], [2, 5], [3, 6]];
    assert.deepEqual(Mat.transpose(A), At);
  });

  test('transpose of transpose is identity', () => {
    const A = [[1, 2], [3, 4], [5, 6]];
    assert.deepEqual(Mat.transpose(Mat.transpose(A)), A);
  });

  test('isValid', () => {
    const A = [[1, 2, 3], [4, 5, 6]];
    assert.equal(Mat.isValid(2, 3, A), true);
    assert.equal(Mat.isValid(3, 2, A), false);
    assert.equal(Mat.isValid(2, 2, A), false);
  });

  test('isValid empty matrix', () => {
    assert.equal(Mat.isValid(0, 0, []), true);
    assert.equal(Mat.isValid(1, 0, [[]]), true);
  });
});

describe('Integration - LWE Properties', () => {
  test('LWE decryption correctness with small noise', () => {
    const q = 97;
    const s = [1, -1, 2, 0];  // secret
    const a = [23, 45, 12, 67];  // random vector

    for (const bit of [false, true]) {
      // Encrypt: c = <a, s> + encode(bit) + noise
      const inner = Vec.dot(a, s);
      const noise = 3;  // small noise
      const c = (inner + Zq.encodeBit(q, bit) + noise) % q;

      // Decrypt: decode(c - <a, s>)
      const decrypted = Zq.decodeBit(q, Zq.modCentered(c - inner, q));

      assert.equal(decrypted, bit, `Failed for bit=${bit}`);
    }
  });

  test('LWE noise tolerance', () => {
    const q = 97;
    const threshold = Math.floor(q / 4);

    // For bit=false (encoded as 0), noise < q/4 should decode correctly
    for (let noise = 0; noise < threshold; noise++) {
      assert.equal(Zq.decodeBit(q, noise), false, `noise=${noise} should decode to false`);
    }

    // For bit=true (encoded as q/2), values near q/2 should decode correctly
    const encoded1 = Zq.encodeBit(q, true);
    for (let noise = -threshold + 1; noise < threshold; noise++) {
      const val = (encoded1 + noise + q) % q;
      assert.equal(Zq.decodeBit(q, val), true, `q/2+${noise} should decode to true`);
    }
  });
});

describe('Dilithium - Compression and Hint Helpers', () => {
  const params44 = Dilithium.params('44');
  const alpha44 = 2 * params44.gamma2;

  test('params exposes ML-DSA-44 constants', () => {
    assert.deepEqual(params44, {
      n: 256,
      q: 8380417,
      k: 4,
      l: 4,
      eta: 2,
      tau: 39,
      beta: 78,
      gamma1: 131072,
      gamma2: 95232,
      d: 13,
      omega: 80,
    });
  });

  test('modCentered matches centered reduction behavior', () => {
    assert.equal(Dilithium.modCentered(8, 16), 8);
    assert.equal(Dilithium.modCentered(9, 16), -7);
    assert.equal(Dilithium.modCentered(-3, 16), -3);
  });

  test('power2Round reconstructs the original coefficient', () => {
    const r = 1234567;
    const { r1, r0 } = Dilithium.power2Round(r, params44.d);
    assert.equal(r1 * (1 << params44.d) + r0, r);
  });

  test('decompose agrees with highBits and lowBits', () => {
    const r = 543210;
    const split = Dilithium.decompose(r, alpha44);
    assert.equal(split.r1, Dilithium.highBits(r, alpha44));
    assert.equal(split.r0, Dilithium.lowBits(r, alpha44));
  });

  test('makeHint and useHint recover adjusted high bits', () => {
    const r = 100000;
    const z = 2000;
    const hint = Dilithium.makeHint(z, r, alpha44);
    assert.equal(Dilithium.useHint(hint, r, alpha44), Dilithium.highBits(r + z, alpha44));
  });

  test('checkBound uses a strict inequality', () => {
    assert.equal(Dilithium.checkBound(77, params44.beta), true);
    assert.equal(Dilithium.checkBound(params44.beta, params44.beta), false);
  });

  test('hintWeight counts all one bits across rows', () => {
    assert.equal(Dilithium.hintWeight([[1, 0, 1], [0, 1, 0], [1]]), 4);
  });
});

describe('ConfidentialBalance - Deterministic Balance Proof Slice', () => {
  const params = ConfidentialBalance.makeParams(2, 2, 17, 3);
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const gamma = 5;

  function commitOfOpening(opening) {
    return Zq.matVecMultMod(ck, Vec.concat(opening.msg, opening.rand), params.q);
  }

  test('makeParams fixes n1 to 1 and validates the result', () => {
    assert.deepEqual(params, { n1: 1, n2: 2, m: 2, q: 17, beta: 3 });
    assert.equal(ConfidentialBalance.validScalarParams(params), true);
    assert.equal(ConfidentialBalance.validScalarParams({ ...params, n1: 2 }), false);
  });

  test('randCommitKey drops the scalar message column', () => {
    assert.deepEqual(ConfidentialBalance.randCommitKey(params, ck), [[0, 0], [1, 0]]);
  });

  test('balanceCommitment matches the balanced aggregate randomness witness', () => {
    const opIn1 = { msg: [7], rand: [1, 2] };
    const opIn2 = { msg: [4], rand: [0, -1] };
    const opOut1 = { msg: [5], rand: [2, 0] };
    const opOut2 = { msg: [6], rand: [-1, 1] };
    const aggregate = ConfidentialBalance.aggregateRandomness(opIn1, opIn2, opOut1, opOut2);
    const c = ConfidentialBalance.balanceCommitment(
      commitOfOpening(opIn1),
      commitOfOpening(opIn2),
      commitOfOpening(opOut1),
      commitOfOpening(opOut2),
      params.q
    );

    assert.equal(ConfidentialBalance.amountOfOpening(opIn1), 7);
    assert.deepEqual(normalizeSignedZero(aggregate), [0, 0]);
    assert.deepEqual(
      normalizeSignedZero(c),
      normalizeSignedZero(ConfidentialBalance.randCommit(params, ck, aggregate))
    );
  });

  test('fsProve and fsVerify succeed on a valid witness', () => {
    const r = [1, 2];
    const ys = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
    const c = ConfidentialBalance.randCommit(params, ck, r);
    const proof = ConfidentialBalance.fsProve(params, gamma, ck, c, r, ys);

    assert.equal(ConfidentialBalance.validWitness(params, r), true);
    assert.equal(ys.every((y) => ConfidentialBalance.validMask(params, gamma, y)), true);
    assert.ok(proof);
    assert.ok(['single', 'rounds', 'lists'].includes(balanceProofShape(proof)));
    const normalizedProof = normalizeBalanceProof(proof);
    assert.equal(normalizedProof.length, ConfidentialBalance.fsRounds());
    const challenges = ConfidentialBalance.fsChallenges(
      params,
      ck,
      c,
      normalizedProof.map((round) => round.a)
    );
    for (const [index, round] of normalizedProof.entries()) {
      assert.equal(ConfidentialBalance.validResponse(params, gamma, challenges[index], round.z), true);
    }
    assert.equal(ConfidentialBalance.relation(params, ck, c, r), true);
    assert.equal(ConfidentialBalance.fsVerify(params, gamma, ck, c, proof), true);
  });

  test('fsProve returns null when the relation is invalid', () => {
    const ys = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
    const proof = ConfidentialBalance.fsProve(params, gamma, ck, [0, 0], [1, 2], ys);
    assert.equal(proof, null);
  });

  test('sigmaVerify rejects a tampered proof', () => {
    const r = [1, 2];
    const ys = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
    const c = ConfidentialBalance.randCommit(params, ck, r);
    const proof = ConfidentialBalance.fsProve(params, gamma, ck, c, r, ys);
    const tampered = tamperBalanceProof(proof);
    const tamperedRounds = normalizeBalanceProof(tampered);
    const challenge = ConfidentialBalance.fsChallenges(
      params,
      ck,
      c,
      tamperedRounds.map((round) => round.a)
    )[0];

    assert.equal(
      ConfidentialBalance.sigmaVerify(
        params,
        gamma,
        ck,
        c,
        tamperedRounds[0].a,
        challenge,
        tamperedRounds[0].z
      ),
      false
    );
    assert.equal(ConfidentialBalance.fsVerify(params, gamma, ck, c, tampered), false);
  });
});

describe('ConfidentialRange - Deterministic Range Proof Slice', () => {
  const params = ConfidentialBalance.makeParams(2, 2, 17, 6);
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const gamma = 5;
  const rangeK = 3;
  const amountOpening = { msg: [5], rand: [1, 2] };
  const bitOpenings = [
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 1] },
  ];
  const compOpenings = [
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, -1] },
  ];
  const yAmount = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
  const yPairs = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [
    [1, 0],
    [0, 0],
    [1, -1],
  ]);

  function commitOfOpening(opening) {
    return Zq.matVecMultMod(ck, Vec.concat(opening.msg, opening.rand), params.q);
  }

  test('oneOpening and pair commitments keep the bit-complement invariant explicit', () => {
    assert.deepEqual(ConfidentialRange.oneOpening(params), { msg: [1], rand: [0, 0] });
    assert.equal(ConfidentialRange.validBitOpening(params, bitOpenings[0]), true);
    assert.equal(ConfidentialRange.bitPairRelation(params, bitOpenings[0], compOpenings[0]), true);
  });

  test('amountCommitment matches the residual randomness commitment', () => {
    const cAmount = commitOfOpening(amountOpening);
    const cBits = bitOpenings.map(commitOfOpening);
    const residual = [-4, -4];
    const amountCommitment = ConfidentialRange.amountCommitment(params, ck, cAmount, cBits);

    assert.deepEqual(cAmount, [5, 1]);
    assert.deepEqual(
      amountCommitment,
      ConfidentialBalance.randCommit(params, ck, residual)
    );
  });

  test('fsProve and fsVerify succeed on a valid bounded amount witness', () => {
    const cAmount = commitOfOpening(amountOpening);
    const proof = ConfidentialRange.fsProve(
      params,
      gamma,
      rangeK,
      ck,
      cAmount,
      amountOpening,
      bitOpenings,
      compOpenings,
      yAmount,
      yPairs
    );

    assert.ok(proof);
    assert.ok(['legacy', 'rounds', 'lists'].includes(rangeProofShape(proof)));
    const normalizedProof = normalizeRangeProof(proof, 'ConfidentialRange.fsProve');
    assert.equal(normalizedProof.rounds.length, ConfidentialBalance.fsRounds());
    assert.equal(ConfidentialRange.validAmountWitness(params, rangeK, [-4, -4]), true);
    assert.equal(ConfidentialRange.validPairWitness(params, [1, 1]), true);
    for (const round of normalizedProof.rounds) {
      if (round.challenge !== undefined) {
        assert.equal(
          ConfidentialRange.validAmountResponse(
            params,
            gamma,
            rangeK,
            round.challenge,
            round.amountZ
          ),
          true
        );
        for (const z of round.pairZs) {
          assert.equal(ConfidentialRange.validPairResponse(params, gamma, round.challenge, z), true);
        }
      }
    }
    assert.equal(ConfidentialRange.fsVerify(params, gamma, rangeK, ck, cAmount, proof), true);
  });

  test('fsVerify is stable across repeated checks of the same proof object', () => {
    const cAmount = commitOfOpening(amountOpening);
    const proof = ConfidentialRange.fsProve(
      params,
      gamma,
      rangeK,
      ck,
      cAmount,
      amountOpening,
      bitOpenings,
      compOpenings,
      yAmount,
      yPairs
    );

    assert.ok(proof);
    for (let index = 0; index < 5; index += 1) {
      assert.equal(ConfidentialRange.fsVerify(params, gamma, rangeK, ck, cAmount, proof), true);
    }
  });

  test('fsProve returns null when the amount does not match the bit decomposition', () => {
    const badAmount = { msg: [6], rand: amountOpening.rand };
    const cAmount = commitOfOpening(badAmount);
    const proof = ConfidentialRange.fsProve(
      params,
      gamma,
      rangeK,
      ck,
      cAmount,
      badAmount,
      bitOpenings,
      compOpenings,
      yAmount,
      yPairs
    );

    assert.equal(proof, null);
  });

  test('fsVerify rejects a tampered range proof', () => {
    const cAmount = commitOfOpening(amountOpening);
    const proof = ConfidentialRange.fsProve(
      params,
      gamma,
      rangeK,
      ck,
      cAmount,
      amountOpening,
      bitOpenings,
      compOpenings,
      yAmount,
      yPairs
    );
    assert.ok(proof);
    const tampered = tamperRangeProof(proof);

    assert.equal(ConfidentialRange.fsVerify(params, gamma, rangeK, ck, cAmount, tampered), false);
  });
});

describe('ConfidentialTransaction - Nullifiers, Membership, and Transfer Proofs', () => {
  const params = ConfidentialBalance.makeParams(2, 2, 17, 6);
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const nk = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const gamma = 5;
  const rangeK = 3;
  const opIn1 = { msg: [4], rand: [1, 0] };
  const opIn2 = { msg: [3], rand: [0, 1] };
  const opOut1 = { msg: [5], rand: [1, 2] };
  const opOut2 = { msg: [2], rand: [1, 0] };
  const out1Bits = [
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 1] },
  ];
  const out1Comps = [
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, -1] },
  ];
  const out2Bits = [
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 0] },
  ];
  const out2Comps = [
    { msg: [1], rand: [1, 0] },
    { msg: [0], rand: [0, 1] },
    { msg: [1], rand: [1, 1] },
  ];
  const yIn1 = Array.from({ length: ConfidentialBalance.fsRounds() }, () => ({ msg: [0], rand: [1, 0] }));
  const yIn2 = Array.from({ length: ConfidentialBalance.fsRounds() }, () => ({ msg: [1], rand: [0, 1] }));
  const yBalance = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
  const yOut1 = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [0, 1]);
  const yOut1Pairs = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [
    [1, 0],
    [0, 0],
    [1, -1],
  ]);
  const yOut2 = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [1, 0]);
  const yOut2Pairs = Array.from({ length: ConfidentialBalance.fsRounds() }, () => [
    [0, 1],
    [1, 0],
    [0, 0],
  ]);

  function commitOfOpening(opening) {
    return Zq.matVecMultMod(ck, Vec.concat(opening.msg, opening.rand), params.q);
  }

  const cIn1 = commitOfOpening(opIn1);
  const cIn2 = commitOfOpening(opIn2);
  const cOut1 = commitOfOpening(opOut1);
  const cOut2 = commitOfOpening(opOut2);
  const nf1 = ConfidentialTransaction.nullifier(params, nk, opIn1);
  const nf2 = ConfidentialTransaction.nullifier(params, nk, opIn2);
  const ledger = [cIn1, cIn2, [9, 4]];
  const root = ConfidentialTransaction.ledgerRoot(params, ledger);
  const spent = [];

  test('nullifierFsProve and nullifierFsVerify succeed deterministically', () => {
    const proof = ConfidentialTransaction.nullifierFsProve(
      params,
      gamma,
      ck,
      nk,
      cIn1,
      nf1,
      opIn1,
      yIn1
    );

    assert.ok(proof);
    assert.ok(['legacy', 'rounds', 'lists'].includes(nullifierProofShape(proof)));
    assert.deepEqual(ConfidentialTransaction.nullifier(params, nk, opIn1), nf1);
    assert.equal(ConfidentialTransaction.nullifierFsVerify(params, gamma, ck, nk, cIn1, nf1, proof), true);
  });

  test('nullifierFsVerify is stable across repeated checks of the same proof object', () => {
    const proof = ConfidentialTransaction.nullifierFsProve(
      params,
      gamma,
      ck,
      nk,
      cIn1,
      nf1,
      opIn1,
      yIn1
    );

    assert.ok(proof);
    for (let index = 0; index < 5; index += 1) {
      assert.equal(ConfidentialTransaction.nullifierFsVerify(params, gamma, ck, nk, cIn1, nf1, proof), true);
    }
  });

  test('membershipProve and membershipVerify recover the ledger position', () => {
    const proof = ConfidentialTransaction.membershipProve(params, ledger, cIn2);

    assert.ok(proof);
    assert.deepEqual(proof.root, root);
    assert.equal(ConfidentialTransaction.membershipVerify(params, cIn2, proof), true);
    assert.equal(
      ConfidentialTransaction.membershipVerify(params, cIn2, { ...proof, root: [0, 0] }),
      false
    );
  });

  test('fsProve and fsVerify succeed on a valid 2-in/2-out transfer', () => {
    const proof = ConfidentialTransaction.fsProve(
      params,
      gamma,
      rangeK,
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

    assert.ok(proof);
    assert.ok(['legacy', 'rounds', 'lists'].includes(nullifierProofShape(proof.in1Nullifier)));
    assert.ok(['legacy', 'rounds', 'lists'].includes(nullifierProofShape(proof.in2Nullifier)));
    assert.ok(['legacy', 'rounds', 'lists'].includes(rangeProofShape(proof.out1Range)));
    assert.ok(['legacy', 'rounds', 'lists'].includes(rangeProofShape(proof.out2Range)));
    assert.equal(
      ConfidentialTransaction.fsVerify(
        params,
        gamma,
        rangeK,
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
      ),
      true
    );
  });

  test('ledger helpers preserve output proofs and append spent nullifiers', () => {
    const proof = ConfidentialTransaction.fsProve(
      params,
      gamma,
      rangeK,
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
    const notes = [
      { commitment: cIn1, rangeProof: proof.out1Range },
      { commitment: cIn2, rangeProof: proof.out2Range },
    ];
    const updatedNotes = ConfidentialTransaction.ledgerApplyNotes(notes, proof, cOut1, cOut2);
    const updatedSpent = ConfidentialTransaction.ledgerApplySpent(spent, nf1, nf2);

    assert.deepEqual(ConfidentialTransaction.commitmentLedger(updatedNotes), [cOut1, cOut2]);
    assert.equal(
      ConfidentialTransaction.ledgerValid(
        params,
        gamma,
        rangeK,
        ck,
        ConfidentialTransaction.ledgerRoot(params, [cOut1, cOut2]),
        updatedNotes,
        updatedSpent
      ),
      true
    );
    assert.deepEqual(updatedSpent, [nf1, nf2]);
  });

  test('semantic ledger-step verification defaults to the Merkle path with scaffold compatibility explicit', () => {
    const proof = ConfidentialTransaction.fsProveMerkle(
      params,
      gamma,
      rangeK,
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
    const notes = [
      { commitment: cIn1, rangeProof: proof.out1Range },
      { commitment: cIn2, rangeProof: proof.out2Range },
    ];

    assert.equal(typeof ConfidentialTransaction.semanticStepValid, 'function');
    assert.equal(typeof ConfidentialTransaction.ledgerStepValid, 'function');
    assert.equal(typeof ConfidentialTransaction.ledgerStepValidScaffold, 'function');
    assert.equal(typeof ConfidentialTransaction.semanticStepValidScaffold, 'function');
    assert.equal(typeof ConfidentialTransaction.ledgerStepValidMerkle, 'function');

    const merkleStep = ConfidentialTransaction.ledgerStepValidMerkle(
      params,
      gamma,
      rangeK,
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
    assert.equal(
      ConfidentialTransaction.semanticStepValid(
        params,
        gamma,
        rangeK,
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
      ),
      merkleStep
    );
    assert.equal(
      ConfidentialTransaction.ledgerStepValid(
        params,
        gamma,
        rangeK,
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
      ),
      merkleStep
    );

    const scaffoldProof = ConfidentialTransaction.fsProve(
      params,
      gamma,
      rangeK,
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
    const scaffoldStep = ConfidentialTransaction.ledgerStepValidScaffold(
      params,
      gamma,
      rangeK,
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
      scaffoldProof
    );
    assert.equal(
      ConfidentialTransaction.semanticStepValidScaffold(
        params,
        gamma,
        rangeK,
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
        scaffoldProof
      ),
      scaffoldStep
    );
  });

  test('fsVerify rejects a tampered transaction proof', () => {
    const proof = ConfidentialTransaction.fsProve(
      params,
      gamma,
      rangeK,
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
    const tampered = {
      ...proof,
      in2Member: { ...proof.in2Member, index: 0 },
    };

    assert.equal(
      ConfidentialTransaction.fsVerify(
        params,
        gamma,
        rangeK,
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
        tampered
      ),
      false
    );
  });
});

console.log('All tests passed!');
