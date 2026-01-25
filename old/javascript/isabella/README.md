# Isabella JavaScript Runtime

This directory contains the JavaScript runtime compiled from verified OCaml code via js_of_ocaml.

## Building

From the project root:

```bash
# First time setup (installs OCaml toolchain)
./build-js.sh --setup

# Build JavaScript
./build-js.sh
```

## Output

After building, the compiled JavaScript will be in:
- `dist/isabella.js` - The compiled runtime

## Usage

```javascript
// Load the runtime (sets up global Isabella object)
require('./dist/isabella.js');

// Use the verified functions
const result = Isabella.vecAdd([1, 2, 3], [4, 5, 6]);
console.log(result);  // [5, 7, 9]

// LWE encryption
const ciphertext = Isabella.lweEncrypt(pkA, pkB, q, randomVector, true);
const plaintext = Isabella.lweDecrypt(skS, q, ciphertext.u, ciphertext.v);
```

## How It Works

1. **Isabelle/HOL** proves correctness of lattice crypto algorithms
2. **Isabelle code generation** extracts to OCaml
3. **js_of_ocaml** compiles OCaml bytecode to JavaScript
4. **zarith_stubs_js** provides arbitrary precision integers in JS

The proofs guarantee correctness - the compilation chain preserves semantics.
