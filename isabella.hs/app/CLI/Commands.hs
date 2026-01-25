-- | CLI command handlers
module CLI.Commands (runCommand) where

import Canon
import Text.Read (readMaybe)
import Data.Maybe (fromMaybe)

runCommand :: String -> [String] -> IO ()
runCommand cmd args = case cmd of
    "mod-centered" -> cmdModCentered args
    "dist0" -> cmdDist0 args
    "encode-bit" -> cmdEncodeBit args
    "decode-bit" -> cmdDecodeBit args
    "inner-prod" -> cmdInnerProd args
    "vec-add" -> cmdVecAdd args
    "mat-vec-mult" -> cmdMatVecMult args
    _ -> putStrLn $ "Unknown command: " ++ cmd ++ "\nUse --help for usage."

-- Parse helpers
parseInt :: String -> Maybe Int
parseInt = readMaybe

parseVec :: String -> Maybe [Int]
parseVec s = readMaybe s

parseMat :: String -> Maybe [[Int]]
parseMat s = readMaybe s

parseBool :: String -> Maybe Bool
parseBool "0" = Just False
parseBool "1" = Just True
parseBool "false" = Just False
parseBool "true" = Just True
parseBool "False" = Just False
parseBool "True" = Just True
parseBool _ = Nothing

-- Command implementations

cmdModCentered :: [String] -> IO ()
cmdModCentered [xStr, qStr] =
    case (parseInt xStr, parseInt qStr) of
        (Just x, Just q) -> do
            let result = mod_centered x q
            putStrLn $ "mod_centered " ++ show x ++ " " ++ show q ++ " = " ++ show result
        _ -> putStrLn "Error: Expected two integers (X Q)"
cmdModCentered _ = putStrLn "Usage: mod-centered X Q"

cmdDist0 :: [String] -> IO ()
cmdDist0 [qStr, xStr] =
    case (parseInt qStr, parseInt xStr) of
        (Just q, Just x) -> do
            let result = dist0 q x
            putStrLn $ "dist0 " ++ show q ++ " " ++ show x ++ " = " ++ show result
        _ -> putStrLn "Error: Expected two integers (Q X)"
cmdDist0 _ = putStrLn "Usage: dist0 Q X"

cmdEncodeBit :: [String] -> IO ()
cmdEncodeBit [qStr, bStr] =
    case (parseInt qStr, parseBool bStr) of
        (Just q, Just b) -> do
            let result = encode_bit q b
            putStrLn $ "encode_bit " ++ show q ++ " " ++ show b ++ " = " ++ show result
        _ -> putStrLn "Error: Expected integer Q and boolean B (0/1 or true/false)"
cmdEncodeBit _ = putStrLn "Usage: encode-bit Q B"

cmdDecodeBit :: [String] -> IO ()
cmdDecodeBit [qStr, xStr] =
    case (parseInt qStr, parseInt xStr) of
        (Just q, Just x) -> do
            let result = decode_bit q x
            putStrLn $ "decode_bit " ++ show q ++ " " ++ show x ++ " = " ++ show result
        _ -> putStrLn "Error: Expected two integers (Q X)"
cmdDecodeBit _ = putStrLn "Usage: decode-bit Q X"

cmdInnerProd :: [String] -> IO ()
cmdInnerProd [v1Str, v2Str] =
    case (parseVec v1Str, parseVec v2Str) of
        (Just v1, Just v2) -> do
            let result = inner_prod v1 v2
            putStrLn $ "inner_prod " ++ show v1 ++ " " ++ show v2 ++ " = " ++ show result
        _ -> putStrLn "Error: Expected two vectors (e.g., \"[1,2,3]\" \"[4,5,6]\")"
cmdInnerProd _ = putStrLn "Usage: inner-prod \"[v1]\" \"[v2]\""

cmdVecAdd :: [String] -> IO ()
cmdVecAdd [v1Str, v2Str] =
    case (parseVec v1Str, parseVec v2Str) of
        (Just v1, Just v2) -> do
            let result = vec_add v1 v2
            putStrLn $ "vec_add " ++ show v1 ++ " " ++ show v2 ++ " = " ++ show result
        _ -> putStrLn "Error: Expected two vectors"
cmdVecAdd _ = putStrLn "Usage: vec-add \"[v1]\" \"[v2]\""

cmdMatVecMult :: [String] -> IO ()
cmdMatVecMult [mStr, vStr, qStr] =
    case (parseMat mStr, parseVec vStr, parseInt qStr) of
        (Just m, Just v, Just q) -> do
            let result = mat_vec_mult_mod m v q
            putStrLn $ "mat_vec_mult_mod"
            putStrLn $ "  A = " ++ show m
            putStrLn $ "  v = " ++ show v
            putStrLn $ "  q = " ++ show q
            putStrLn $ "  result = " ++ show result
        _ -> putStrLn "Error: Expected matrix M, vector V, and modulus Q"
cmdMatVecMult _ = putStrLn "Usage: mat-vec-mult \"[[row1],[row2]]\" \"[v]\" Q"
