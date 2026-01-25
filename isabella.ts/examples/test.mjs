/**
 * Isabella TypeScript Library Tests
 *
 * Run with: node --test examples/test.mjs
 */

import { test, describe } from 'node:test';
import assert from 'node:assert/strict';
import { Zq, Vec, Mat } from '../dist/index.js';

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

console.log('All tests passed!');
