# Isabella (OCaml)

Formally verified lattice cryptography library extracted from Isabelle/HOL.

## Overview

Isabella provides lattice-based cryptographic primitives that have been
formally verified in Isabelle/HOL. Every function in this library is
generated from proven-correct specifications, ensuring mathematical
correctness.

## Modules

- **Canon** - Main module re-exporting all functionality
  - **Canon.Zq** - Modular arithmetic over Z_q
  - **Canon.Listvec** - Vector and matrix operations

## Installation

```bash
dune build
```

## Usage

### As a Library

```ocaml
open Canon

(* Centered modular reduction *)
let x = Zq.mod_centered 7 5  (* Result: 2 *)

(* Bit encoding for LWE *)
let encoded = Zq.encode_bit 256 true   (* Result: 128 *)
let decoded = Zq.decode_bit 256 130    (* Result: true *)

(* Vector operations *)
let v1 = [1; 2; 3]
let v2 = [4; 5; 6]
let dot = Listvec.inner_prod v1 v2  (* Result: 32 *)

(* Matrix-vector multiplication mod q *)
let result = Zq.mat_vec_mult_mod [[1;2];[3;4]] [5;6] 10
```

### Command-Line Interface

```bash
# Run examples
dune exec isabella_cli -- examples

# Use specific functions
dune exec isabella_cli -- mod-centered 7 5
dune exec isabella_cli -- dist0 256 130
dune exec isabella_cli -- encode-bit 256 1
dune exec isabella_cli -- decode-bit 256 130
dune exec isabella_cli -- inner-prod "1,2,3" "4,5,6"
```

## Verified Properties

All functions come with machine-checked proofs in Isabelle/HOL:

### Centered Modular Reduction
- `mod_centered x q mod q = x mod q`
- `|mod_centered x q| <= q/2`
- `mod_centered 0 q = 0`

### Distance Function
- `dist0 q x >= 0`
- `dist0 q x <= q/2`
- `dist0 q 0 = 0`

### Bit Encoding/Decoding
- `decode_bit q (encode_bit q b) = b` (for q > 2)
- Small noise tolerance: if `|x| < q/4` then `decode_bit q (encode_bit q b + x) = b`

## License

MIT License - see [LICENSE](LICENSE)
