-- | Isabella CLI - Command-line interface for the Isabella library
--
-- This executable provides a way to interact with and test the
-- formally verified cryptographic primitives from the command line.
module Main where

import System.Environment (getArgs)
import CLI.Commands (runCommand)
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
        (cmd:rest) -> runCommand cmd rest

showHelp :: IO ()
showHelp = do
    putStrLn "Isabella - Formally Verified Lattice Cryptography"
    putStrLn ""
    putStrLn "Usage: isabella-cli <command> [options]"
    putStrLn ""
    putStrLn "Commands:"
    putStrLn "  examples           Run example computations"
    putStrLn "  mod-centered X Q   Compute centered modular reduction"
    putStrLn "  dist0 Q X          Compute distance from zero in Z_q"
    putStrLn "  encode-bit Q B     Encode a bit (0 or 1) for LWE"
    putStrLn "  decode-bit Q X     Decode an LWE value to a bit"
    putStrLn "  inner-prod V1 V2   Compute inner product of two vectors"
    putStrLn "  vec-add V1 V2      Add two vectors"
    putStrLn "  mat-vec-mult M V Q Matrix-vector multiplication mod q"
    putStrLn ""
    putStrLn "Options:"
    putStrLn "  --help, -h         Show this help message"
    putStrLn ""
    putStrLn "Examples:"
    putStrLn "  isabella-cli mod-centered 7 5"
    putStrLn "  isabella-cli dist0 256 130"
    putStrLn "  isabella-cli encode-bit 256 1"
    putStrLn "  isabella-cli decode-bit 256 130"
    putStrLn "  isabella-cli inner-prod \"[1,2,3]\" \"[4,5,6]\""
    putStrLn ""
    putStrLn "All functions are formally verified in Isabelle/HOL."
