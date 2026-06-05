-- | Isabella CLI - Command-line interface for the Isabella library
--
-- This executable provides a way to interact with and test the
-- formally verified cryptographic primitives from the command line.
module Main where

import System.Environment (getArgs)
import CLI.Commands (OutputFormat(..), runCommand)
import CLI.Examples (runExamples)

main :: IO ()
main = do
    args <- getArgs
    case args of
        [] -> showHelp
        ["--help"] -> showHelp
        ["-h"] -> showHelp
        ["help"] -> showHelp
        ["examples"] -> runExamples
        ["example"] -> runExamples
        ["--json", "examples"] -> putStrLn "{\"error\":\"examples does not support --json\"}"
        ["--json", "example"] -> putStrLn "{\"error\":\"examples does not support --json\"}"
        ("--json":cmd:rest) -> runCommand Json cmd rest
        (cmd:rest) -> runCommand Human cmd rest

showHelp :: IO ()
showHelp = do
    putStrLn "Isabella - Formally Verified Lattice Cryptography"
    putStrLn ""
    putStrLn "Usage: isabella-cli [--json] <command> [options]"
    putStrLn ""
    putStrLn "Commands:"
    putStrLn "  examples           Run example computations"
    putStrLn "  mod-centered X Q   Compute centered modular reduction"
    putStrLn "  dist0 Q X          Compute distance from zero in Z_q"
    putStrLn "  encode-bit Q B     Encode a bit (0 or 1) for LWE"
    putStrLn "  decode-bit Q X     Decode an LWE value to a bit"
    putStrLn "  inner-prod V1 V2   Compute inner product of two vectors"
    putStrLn "  vec-add V1 V2      Add two vectors"
    putStrLn "  transpose M        Transpose a matrix"
    putStrLn "  mat-vec-mult M V Q Matrix-vector multiplication mod q"
    putStrLn "  dil-params V       Get ML-DSA parameters (44, 65, 87)"
    putStrLn "  dil-mod-centered R M  Centered modular reduction for ML-DSA helpers"
    putStrLn "  dil-power2round R D   Split r into (r1, r0) using 2^d"
    putStrLn "  dil-decompose R A     Split r into high/low bits using alpha"
    putStrLn "  dil-highbits R A      Extract high-order bits"
    putStrLn "  dil-lowbits R A       Extract low-order bits"
    putStrLn "  dil-makehint Z R A    Compute hint bit"
    putStrLn "  dil-usehint H R A     Recover high bits using hint"
    putStrLn "  dil-check-bound V B   Check whether |V| < B"
    putStrLn "  dil-hint-weight H     Count total hint bits in a matrix"
    putStrLn "  cb-params M N2 Q BETA Build confidential-balance scalar commitment params"
    putStrLn "  cb-valid-params M N2 Q BETA Check confidential-balance params"
    putStrLn "  cb-rand-commit-key M N2 Q BETA CK  Drop the message column from a commit key"
    putStrLn "  cb-rand-commit M N2 Q BETA CK R     Commit to aggregate randomness"
    putStrLn "  cb-valid-witness M N2 Q BETA R      Check witness bounds"
    putStrLn "  cb-valid-mask M N2 Q BETA G Y       Check mask bounds"
    putStrLn "  cb-valid-response M N2 Q BETA G E Z   Check response bounds"
    putStrLn "  cb-balance-commitment C1 C2 C3 C4 Q Aggregate commitments for zero-balance checking"
    putStrLn "  cb-canonical-challenge M N2 Q BETA CK C A  Deterministic Fiat-Shamir challenge"
    putStrLn "  cb-sigma-commit M N2 Q BETA CK Y    Compute sigma announcement"
    putStrLn "  cb-sigma-respond R Y E              Compute sigma response"
    putStrLn "  cb-sigma-verify M N2 Q BETA G CK C A E Z  Verify sigma step"
    putStrLn "  cb-prove M N2 Q BETA G CK C R Y     Build deterministic balance proof"
    putStrLn "  cb-verify M N2 Q BETA G CK C A Z    Verify deterministic balance proof"
    putStrLn "  cr-amount-commitment M N2 Q BETA CK C BITS  Build the amount residual commitment"
    putStrLn "  cr-prove M N2 Q BETA G K CK C AMOUNT RAND BITS BIT_RANDS COMPS COMP_RANDS YAMOUNTS YPAIRSS  Build deterministic range proof"
    putStrLn "  cr-verify M N2 Q BETA G K CK C BITS COMPS AMOUNT_AS AMOUNT_ZS PAIR_ASS PAIR_ZSS  Verify deterministic range proof"
    putStrLn "  cr-verify-bench I W ...  Benchmark deterministic range verification natively"
    putStrLn "  ct-merkle-leaf C             Hash a confidential note commitment leaf"
    putStrLn "  ct-merkle-empty WIDTH        Hash an empty Merkle placeholder"
    putStrLn "  ct-merkle-node LEFT RIGHT    Hash an internal Merkle node"
    putStrLn "  ct-merkle-root LEDGER        Compute cryptographic Merkle root"
    putStrLn "  ct-merkle-member-prove LEDGER C   Build cryptographic Merkle membership proof"
    putStrLn "  ct-merkle-member-verify LEDGER C  Verify cryptographic Merkle membership proof"
    putStrLn "  ct-nullifier M N2 Q BETA NK AMOUNT RAND  Compute a deterministic note nullifier"
    putStrLn "  ct-nullifier-canonical-challenge M N2 Q BETA CK NK C NF ACOMMIT ANULLIFIER  Deterministic nullifier Fiat-Shamir challenge"
    putStrLn "  ct-nullifier-prove M N2 Q BETA G CK NK C NF AMOUNT RAND YMSGS YRANDS  Build repeated-round deterministic nullifier proof"
    putStrLn "  ct-nullifier-verify M N2 Q BETA G CK NK C NF ACOMMITS ANULLIFIERS ZMSGS ZRANDS  Verify repeated-round deterministic nullifier proof"
    putStrLn "  ct-member-prove M N2 Q BETA LEDGER C   Build explicit ledger membership proof"
    putStrLn "  ct-member-verify M N2 Q BETA LEDGER C  Verify explicit ledger membership proof"
    putStrLn "  ct-ledger-step-verify ... Verify semantic ledger-step validity from verified input notes"
    putStrLn "  ct-prove ...  Build deterministic confidential-transaction proof"
    putStrLn "  ct-prove-merkle ...  Build deterministic confidential-transaction proof with Merkle membership"
    putStrLn "  ct-verify ... Verify deterministic confidential-transaction proof"
    putStrLn "  ct-verify-merkle ... Verify deterministic confidential-transaction proof with Merkle membership"
    putStrLn "  ct-verify-bench I W ... Benchmark deterministic confidential-transaction verification natively"
    putStrLn ""
    putStrLn "Options:"
    putStrLn "  --json             Emit machine-readable JSON for command results"
    putStrLn "  --help, -h         Show this help message"
    putStrLn ""
    putStrLn "Examples:"
    putStrLn "  isabella-cli mod-centered 7 5"
    putStrLn "  isabella-cli dist0 256 130"
    putStrLn "  isabella-cli encode-bit 256 1"
    putStrLn "  isabella-cli decode-bit 256 130"
    putStrLn "  isabella-cli inner-prod \"[1,2,3]\" \"[4,5,6]\""
    putStrLn "  isabella-cli --json transpose \"[[1,2,3],[4,5,6]]\""
    putStrLn "  isabella-cli --json dil-params 44"
    putStrLn "  isabella-cli --json dil-power2round 1234567 13"
    putStrLn "  isabella-cli --json cb-prove 2 2 17 3 5 \"[[5,1,2],[4,-1,3]]\" \"[5,5]\" \"[1,2]\" \"[0,1]\""
    putStrLn "  isabella-cli --json cr-prove 2 2 17 6 5 3 \"[[5,1,2],[4,-1,3]]\" \"[13,8]\" 5 \"[1,2]\" \"[1,0,1]\" \"[[1,0],[0,1],[1,1]]\" \"[0,1,0]\" \"[[0,1],[1,0],[0,-1]]\" \"[[0,1],[0,1],[0,1],[0,1]]\" \"[[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]],[[1,0],[0,0],[1,-1]]]\""
    putStrLn "  isabella-cli --json ct-nullifier 2 2 17 6 \"[[5,1,2],[4,-1,3]]\" 5 \"[1,2]\""
    putStrLn "  isabella-cli --json ct-nullifier-prove 2 2 17 6 5 \"[[5,1,2],[4,-1,3]]\" \"[[5,1,2],[4,-1,3]]\" \"[6,2]\" \"[1,0]\" 4 \"[1,0]\" \"[0,1,0,1]\" \"[[1,0],[0,1],[1,1],[0,0]]\""
    putStrLn ""
    putStrLn "All functions are formally verified in Isabelle/HOL."
