(** Canon: Formally verified lattice cryptography from Isabelle/HOL

    This module provides access to all verified functions from the Canon library.
    All code is extracted from proven-correct Isabelle specifications.

    Modules:
    - {!Zq} - Modular arithmetic over Z_q
    - {!Listvec} - Vector and matrix operations
    - {!Norms} - Vector norms and bounds
    - {!Decomp} - Gadget decomposition
    - {!Lwe_def} - LWE problem definition
    - {!Sis_def} - SIS problem definition
    - {!Polymod} - Polynomial ring arithmetic
    - {!Modulelwe} - Module-LWE and Module-SIS
    - {!Ntt} - Number Theoretic Transform (O(n log n) Cooley-Tukey)
    - {!Regev_pke} - Regev public-key encryption
    - {!Commit_sis} - SIS-based commitment scheme
    - {!Kyber} - CRYSTALS-Kyber (ML-KEM) key encapsulation
    - {!Dilithium} - CRYSTALS-Dilithium (ML-DSA) digital signatures *)

module Zq = Zq
module Listvec = Listvec
module Norms = Norms
module Decomp = Decomp
module Lwe_def = Lwe_def
module Sis_def = Sis_def
module Polymod = Polymod
module Modulelwe = Modulelwe
module Ntt = Ntt
module Regev_pke = Regev_pke
module Commit_sis = Commit_sis
module Kyber = Kyber
module Dilithium = Dilithium
