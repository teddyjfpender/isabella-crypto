/**
 * Isabella TypeScript Library Example
 *
 * Demonstrates the formally verified lattice cryptography primitives.
 */

import { Zq, Vec, Mat } from '../dist/index.js';

console.log('=== Isabella TypeScript Library Examples ===\n');

// --- Modular Arithmetic ---
console.log('--- Zq: Modular Arithmetic ---');

const q = 17;
console.log(`Modulus q = ${q}`);

// Centered modular reduction
console.log('\nCentered mod reduction (maps to (-q/2, q/2]):');
for (const x of [0, 5, 8, 10, 15, 20, -3]) {
  console.log(`  modCentered(${x}, ${q}) = ${Zq.modCentered(x, q)}`);
}

// Distance from zero
console.log('\nDistance from zero:');
for (const x of [0, 1, 8, 9, 16]) {
  console.log(`  dist0(${q}, ${x}) = ${Zq.dist0(q, x)}`);
}

// Bit encoding for LWE
console.log('\nLWE bit encoding/decoding:');
const encoded0 = Zq.encodeBit(q, false);
const encoded1 = Zq.encodeBit(q, true);
console.log(`  encodeBit(${q}, false) = ${encoded0}`);
console.log(`  encodeBit(${q}, true) = ${encoded1}`);
console.log(`  decodeBit(${q}, ${encoded0}) = ${Zq.decodeBit(q, encoded0)}`);
console.log(`  decodeBit(${q}, ${encoded1}) = ${Zq.decodeBit(q, encoded1)}`);

// --- Vector Operations ---
console.log('\n--- Vec: Vector Operations ---');

const v1 = [1, 2, 3];
const v2 = [4, 5, 6];
console.log(`v1 = [${v1}]`);
console.log(`v2 = [${v2}]`);

console.log(`  add(v1, v2) = [${Vec.add(v1, v2)}]`);
console.log(`  sub(v1, v2) = [${Vec.sub(v1, v2)}]`);
console.log(`  scale(2, v1) = [${Vec.scale(2, v1)}]`);
console.log(`  neg(v1) = [${Vec.neg(v1)}]`);
console.log(`  dot(v1, v2) = ${Vec.dot(v1, v2)}`);

// Vector splitting
const combined = Vec.concat(v1, v2);
console.log(`  concat(v1, v2) = [${combined}]`);
const [left, right] = Vec.split(3, combined);
console.log(`  split(3, concat) = [[${left}], [${right}]]`);

// Validation
console.log(`  isValid(3, v1) = ${Vec.isValid(3, v1)}`);
console.log(`  isValid(4, v1) = ${Vec.isValid(4, v1)}`);

// Modular vector operations
console.log('\nModular vector operations:');
const v3 = [10, 20, 30];
console.log(`v3 = [${v3}]`);
console.log(`  vecMod(v3, ${q}) = [${Zq.vecMod(v3, q)}]`);
console.log(`  vecModCentered(v3, ${q}) = [${Zq.vecModCentered(v3, q)}]`);

// --- Matrix Operations ---
console.log('\n--- Mat: Matrix Operations ---');

const A = [
  [1, 2, 3],
  [4, 5, 6]
];
const x = [1, 1, 1];

console.log('Matrix A:');
A.forEach((row, i) => console.log(`  [${row}]`));
console.log(`Vector x = [${x}]`);

const Ax = Mat.vecMult(A, x);
console.log(`  vecMult(A, x) = [${Ax}]`);

const AxMod = Zq.matVecMultMod(A, x, q);
console.log(`  matVecMultMod(A, x, ${q}) = [${AxMod}]`);

const At = Mat.transpose(A);
console.log('  transpose(A):');
At.forEach((row, i) => console.log(`    [${row}]`));

console.log(`  isValid(2, 3, A) = ${Mat.isValid(2, 3, A)}`);
console.log(`  isValid(3, 2, A) = ${Mat.isValid(3, 2, A)}`);

// --- LWE Encryption Demo ---
console.log('\n--- LWE Encryption Demo ---');

// Parameters
const lweQ = 97;  // Prime modulus
const n = 4;      // Dimension

// Secret key (random small vector)
const s = [1, -1, 0, 1];

// Public matrix (random)
const Apub = [
  [23, 45, 12, 67],
  [89, 11, 34, 56],
  [78, 90, 23, 45]
];

// Public key: b = A*s (mod q)
const b = Zq.matVecMultMod(Apub, s, lweQ);

console.log(`Parameters: q=${lweQ}, n=${n}`);
console.log(`Secret key s = [${s}]`);
console.log(`Public key b = A*s mod q = [${b}]`);

// Encrypt a bit
const plaintext = true;
console.log(`\nEncrypting bit: ${plaintext}`);

// Simple encryption: (subset sum of A rows, subset sum of b + encoded bit)
// For demo, just use first row
const a_enc = Apub[0];
const b_enc = (b[0] + Zq.encodeBit(lweQ, plaintext)) % lweQ;
console.log(`Ciphertext: ([${a_enc}], ${b_enc})`);

// Decrypt: b_enc - <a_enc, s> should decode to plaintext
const inner = Vec.dot(a_enc, s);
const decrypted_val = Zq.modCentered(b_enc - inner, lweQ);
const decrypted = Zq.decodeBit(lweQ, decrypted_val);
console.log(`Decryption: decodeBit(${lweQ}, ${decrypted_val}) = ${decrypted}`);
console.log(`Correct: ${decrypted === plaintext}`);

console.log('\n=== Examples Complete ===');
