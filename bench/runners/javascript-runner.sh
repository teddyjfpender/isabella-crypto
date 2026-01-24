#!/usr/bin/env bash
#
# JavaScript benchmark runner with internal timing
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(cd "${SCRIPT_DIR}/../.." && pwd)"

FUNC="$1"
SIZE="$2"

# Run Node.js benchmark with internal timing
node << EOF
// Load the Isabella runtime - exported to module.exports.Isabella
const { Isabella } = require('${PROJECT_ROOT}/javascript/isabella/dist/isabella.js');

if (!Isabella) {
  console.error('Isabella not found');
  process.exit(1);
}

// Seeded random number generator (using BigInt for precision)
function seededRandom(seed) {
  let s = seed;
  return function() {
    const curr = s;
    s = Number((BigInt(s) * 1103515245n + 12345n) % 2147483648n);
    return curr;
  };
}

// Generate test data
function genVec(seed, n) {
  const rng = seededRandom(seed);
  return Array.from({length: n}, () => rng() % 1000 - 500);
}

function genMatrix(seed, rows, cols) {
  return Array.from({length: rows}, (_, i) => genVec(seed + i, cols));
}

function genBinaryVec(seed, n) {
  const rng = seededRandom(seed);
  return Array.from({length: n}, () => rng() % 2);
}

// Prepare data before timing
const size = ${SIZE};
const v1 = genVec(42, size);
const v2 = genVec(43, size);
const m = genMatrix(42, size, size);
const pkA = genMatrix(42, size, size);
const pkB = genVec(43, size);
const q = 97;
const r = genBinaryVec(44, size);
const skS = genVec(42, size);
const ctU = genVec(43, size);
const ctV = 50;

// Run benchmark with timing
const func = '${FUNC}';

const start = process.hrtime.bigint();

switch (func) {
  case 'inner_prod':
    Isabella.innerProd(v1, v2);
    break;
  case 'mat_vec_mult':
    Isabella.matVecMult(m, v1);
    break;
  case 'vec_add':
    Isabella.vecAdd(v1, v2);
    break;
  case 'lwe_encrypt':
    Isabella.lweEncrypt(pkA, pkB, q, r, true);
    break;
  case 'lwe_decrypt':
    Isabella.lweDecrypt(skS, q, ctU, ctV);
    break;
  default:
    throw new Error('Unknown function: ' + func);
}

const end = process.hrtime.bigint();
const elapsed = Number(end - start) / 1e9;  // Convert to seconds
console.log(JSON.stringify({elapsed}));
EOF
