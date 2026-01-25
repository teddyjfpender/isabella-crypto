(** Canon: Formally verified lattice cryptography from Isabelle/HOL

    This module re-exports all functionality from the Canon library.
    All code is extracted from proven-correct Isabelle specifications.

    {1 Modules}

    - {!module:Zq} - Modular arithmetic over Z_q
    - {!module:Listvec} - Vector and matrix operations

    {1 Example Usage}

    {[
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
    ]}
*)

module Zq = Zq
module Listvec = Listvec
