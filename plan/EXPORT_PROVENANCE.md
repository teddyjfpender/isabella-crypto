# Export Provenance Map

This map is enforced by `./generate.sh` (`verify_haskell_provenance` and
`verify_ocaml_provenance`).

## Haskell (`isabella.hs/src`)

| Module file | Isabelle source |
|---|---|
| `Canon/Algebra/Zq.hs` | `Canon/Algebra/Zq.thy` |
| `Canon/Linear/ListVec.hs` | `Canon/Linear/ListVec.thy` |
| `Canon/Analysis/Norms.hs` | `Canon/Analysis/Norms.thy` |
| `Canon/Hardness/LWE_Def.hs` | `Canon/Hardness/LWE_Def.thy` |
| `Canon/Hardness/SIS_Def.hs` | `Canon/Hardness/SIS_Def.thy` |
| `Canon/Gadgets/Decomp.hs` | `Canon/Gadgets/Decomp.thy` |
| `Canon/Rings/PolyMod.hs` | `Canon/Rings/PolyMod.thy` |
| `Canon/Rings/ModuleLWE.hs` | `Canon/Rings/ModuleLWE.thy` |
| `Canon/Rings/NTT.hs` | `Canon/Rings/NTT.thy` |
| `Canon/Crypto/Regev_PKE.hs` | `Canon/Crypto/Regev_PKE.thy` |
| `Canon/Crypto/Commit_SIS.hs` | `Canon/Crypto/Commit_SIS.thy` |
| `Canon/Crypto/Kyber.hs` | `Canon/Crypto/Kyber.thy` |
| `Canon/Crypto/Dilithium.hs` | `Canon/Crypto/Dilithium.thy` |

Aggregate module:

- `Canon.hs` must include the phrase:
  `All code is extracted from proven-correct Isabelle specifications.`

## OCaml (`isabella.ml/src/canon`)

| Module file | Isabelle source |
|---|---|
| `zq.ml` | `Canon/Algebra/Zq.thy` |
| `listvec.ml` | `Canon/Linear/ListVec.thy` |
| `norms.ml` | `Canon/Analysis/Norms.thy` |
| `lwe_def.ml` | `Canon/Hardness/LWE_Def.thy` |
| `sis_def.ml` | `Canon/Hardness/SIS_Def.thy` |
| `decomp.ml` | `Canon/Gadgets/Decomp.thy` |
| `polymod.ml` | `Canon/Rings/PolyMod.thy` |
| `modulelwe.ml` | `Canon/Rings/ModuleLWE.thy` |
| `ntt.ml` | `Canon/Rings/NTT.thy` |
| `regev_pke.ml` | `Canon/Crypto/Regev_PKE.thy` |
| `commit_sis.ml` | `Canon/Crypto/Commit_SIS.thy` |
| `kyber.ml` | `Canon/Crypto/Kyber.thy` |
| `dilithium.ml` | `Canon/Crypto/Dilithium.thy` |

Aggregate module:

- `canon.ml` must include the phrase:
  `All code is extracted from proven-correct Isabelle specifications.`

