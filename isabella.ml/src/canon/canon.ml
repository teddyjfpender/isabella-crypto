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
    - {!Repeated_fs} - Domain-separated Fiat-Shamir transcript helpers
    - {!Confidential_sampling} - CSPRNG-backed confidential-transfer mask sampling
    - {!Confidential_balance} - Confidential balance proof helpers
    - {!Confidential_range} - Confidential range proof helpers
    - {!Confidential_transaction} - Confidential transaction proof helpers
    - {!Confidential_merkle} - Cryptographic confidential-note Merkle helpers
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
module Repeated_fs = Repeated_fs
module Confidential_sampling = Confidential_sampling
module Confidential_balance = Confidential_balance
module Confidential_range = Confidential_range
module Confidential_transaction = Confidential_transaction
module Confidential_merkle = Confidential_merkle
module Kyber = Kyber
module Dilithium = Dilithium
