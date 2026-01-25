# @isabella/lattice-crypto

Formally verified lattice-based cryptography for TypeScript/JavaScript.

## Installation

```bash
npm install @isabella/lattice-crypto
```

## Usage

```typescript
import { Lattice, LweRegev, type LweCiphertext } from '@isabella/lattice-crypto';

// Direct API usage
const sum = Lattice.vecAdd([1, 2, 3], [4, 5, 6]);  // [5, 7, 9]
const dot = Lattice.innerProd([1, 2], [3, 4]);     // 11

// LWE encryption (Regev scheme)
const q = 97;  // modulus
const pkA: number[][] = [[1, 2], [3, 4], [5, 6]];  // public matrix
const pkB: number[] = [10, 20, 30];                 // public vector
const skS: number[] = [1, 1];                       // secret key

const lwe = new LweRegev(q, pkA, pkB, skS);

// Encrypt a bit
const r = [1, 0, 1];  // random binary vector
const ciphertext = lwe.encrypt(true, r);

// Decrypt
const plaintext = lwe.decrypt(ciphertext);  // true
```

## API Reference

### Vector Operations

```typescript
// Component-wise addition
Lattice.vecAdd(xs: number[], ys: number[]): number[]

// Modular reduction
Lattice.vecMod(v: number[], q: number): number[]

// Inner product (dot product)
Lattice.innerProd(xs: number[], ys: number[]): number

// Matrix-vector multiplication
Lattice.matVecMult(mat: number[][], vec: number[]): number[]

// Matrix transpose
Lattice.transpose(mat: number[][]): number[][]
```

### LWE Encryption

```typescript
// Encode/decode bits for LWE
Lattice.encodeBit(q: number, bit: boolean): number
Lattice.decodeBit(q: number, d: number): boolean

// Low-level encrypt/decrypt
Lattice.lweEncrypt(pkA, pkB, q, r, m): LweCiphertext
Lattice.lweDecrypt(skS, q, ctU, ctV): boolean
```

### LweRegev Class

```typescript
const lwe = new LweRegev(q, pkA, pkB, skS?);

lwe.encrypt(message: boolean, randomVector: number[]): LweCiphertext
lwe.decrypt(ciphertext: LweCiphertext): boolean  // requires skS
lwe.modulus: number
```

## Verified Correctness

This library is extracted from Isabelle/HOL proofs. The proofs establish:

- **Correctness**: When noise is bounded, `decrypt(encrypt(m)) = m`
- **Algebraic laws**: Vector operations satisfy expected properties
- **Type safety**: All operations are well-typed

The OCaml code is compiled to JavaScript via js_of_ocaml, preserving semantics.

## Building from Source

```bash
# From project root
./build-js.sh --setup  # First time only
./build-js.sh

# Build TypeScript
cd typescript/isabella
npm install
npm run build
```

## License

MIT
