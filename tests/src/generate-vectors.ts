/**
 * Generate test vectors from noble-post-quantum for validation
 *
 * This script generates test vectors that can be used to validate
 * our Isabelle-generated implementations.
 */

import * as fs from 'fs';
import * as path from 'path';
import { fileURLToPath } from 'url';
import { generateTestVectors, ml_kem512, ml_kem768, ml_kem1024 } from './noble-reference.js';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const vectorsDir = path.join(__dirname, '..', 'vectors');

// Ensure vectors directory exists
if (!fs.existsSync(vectorsDir)) {
  fs.mkdirSync(vectorsDir, { recursive: true });
}

console.log('Generating ML-KEM test vectors using noble-post-quantum...\n');

// Generate comprehensive test vectors
const vectors = generateTestVectors(20);

// Separate by variant
const vectorsByVariant: Record<string, typeof vectors> = {};
for (const vec of vectors) {
  if (!vectorsByVariant[vec.variant]) {
    vectorsByVariant[vec.variant] = [];
  }
  vectorsByVariant[vec.variant].push(vec);
}

// Write combined vectors
const combinedPath = path.join(vectorsDir, 'ml-kem-vectors.json');
fs.writeFileSync(combinedPath, JSON.stringify(vectors, null, 2));
console.log(`Written ${vectors.length} vectors to ${combinedPath}`);

// Write per-variant vectors
for (const [variant, vecs] of Object.entries(vectorsByVariant)) {
  const filename = `${variant.toLowerCase().replace(/-/g, '_')}_vectors.json`;
  const filepath = path.join(vectorsDir, filename);
  fs.writeFileSync(filepath, JSON.stringify(vecs, null, 2));
  console.log(`Written ${vecs.length} vectors to ${filepath}`);
}

// Generate roundtrip validation summary
console.log('\n--- Validation Summary ---');
let allValid = true;
for (const [variant, vecs] of Object.entries(vectorsByVariant)) {
  const validCount = vecs.filter(v => v.valid).length;
  const status = validCount === vecs.length ? '✓' : '✗';
  console.log(`${status} ${variant}: ${validCount}/${vecs.length} roundtrips valid`);
  if (validCount !== vecs.length) allValid = false;
}

// Generate deterministic test vectors with fixed seeds
console.log('\n--- Generating deterministic vectors with fixed seeds ---');

interface DeterministicVector {
  variant: string;
  seed: string;
  publicKey: string;
  secretKey: string;
  encapSeed: string;
  cipherText: string;
  sharedSecret: string;
}

const deterministicVectors: DeterministicVector[] = [];

// Create deterministic seeds
const seeds = [
  new Uint8Array(64).fill(0),  // All zeros
  new Uint8Array(64).fill(1),  // All ones
  new Uint8Array(64).fill(0xff), // All 0xff
  (() => { const s = new Uint8Array(64); for (let i = 0; i < 64; i++) s[i] = i; return s; })(), // Sequential
  (() => { const s = new Uint8Array(64); for (let i = 0; i < 64; i++) s[i] = 64 - i; return s; })(), // Reverse
];

const variants = [
  { name: 'ML-KEM-512', impl: ml_kem512 },
  { name: 'ML-KEM-768', impl: ml_kem768 },
  { name: 'ML-KEM-1024', impl: ml_kem1024 },
];

for (const { name, impl } of variants) {
  for (const seed of seeds) {
    const keys = impl.keygen(seed);
    // Use first 32 bytes of seed as encapsulation randomness
    const encapSeed = seed.slice(0, 32);
    const encap = impl.encapsulate(keys.publicKey, encapSeed);

    deterministicVectors.push({
      variant: name,
      seed: Buffer.from(seed).toString('hex'),
      publicKey: Buffer.from(keys.publicKey).toString('hex'),
      secretKey: Buffer.from(keys.secretKey).toString('hex'),
      encapSeed: Buffer.from(encapSeed).toString('hex'),
      cipherText: Buffer.from(encap.cipherText).toString('hex'),
      sharedSecret: Buffer.from(encap.sharedSecret).toString('hex'),
    });
  }
}

const deterministicPath = path.join(vectorsDir, 'deterministic-vectors.json');
fs.writeFileSync(deterministicPath, JSON.stringify(deterministicVectors, null, 2));
console.log(`Written ${deterministicVectors.length} deterministic vectors to ${deterministicPath}`);

console.log('\n--- Done ---');
if (!allValid) {
  console.error('WARNING: Some roundtrip validations failed!');
  process.exit(1);
}
