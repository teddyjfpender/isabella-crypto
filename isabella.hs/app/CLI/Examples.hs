-- | Example computations demonstrating the Isabella library
module CLI.Examples (runExamples) where

import qualified Canon.Dilithium as Dilithium
import qualified Canon.Listvec as Listvec
import qualified Canon.Zq as Zq
import Data.Time.Clock (getCurrentTime, diffUTCTime)

runExamples :: IO ()
runExamples = do
    putStrLn "====================================================="
    putStrLn "  Isabella - Formally Verified Lattice Cryptography"
    putStrLn "====================================================="
    putStrLn ""

    section "Centered Modular Reduction"
    example "mod_centered 7 5" $ Zq.mod_centered 7 5
    example "mod_centered 8 5" $ Zq.mod_centered 8 5
    example "mod_centered (-3) 5" $ Zq.mod_centered (-3) 5
    example "mod_centered 13 5" $ Zq.mod_centered 13 5

    section "Distance from Zero"
    example "dist0 256 5" $ Zq.dist0 256 5
    example "dist0 256 130" $ Zq.dist0 256 130
    example "dist0 256 250" $ Zq.dist0 256 250

    section "Bit Encoding/Decoding"
    let q = 256
    putStrLn $ "  Using modulus q = " ++ show q
    putStrLn ""
    example "encode_bit 256 False" $ Zq.encode_bit q False
    example "encode_bit 256 True" $ Zq.encode_bit q True
    example "decode_bit 256 5" $ Zq.decode_bit q 5
    example "decode_bit 256 130" $ Zq.decode_bit q 130

    section "Encoding Round-Trip (with noise)"
    let noise = 10
    putStrLn $ "  Testing decode(encode(b) + noise) with noise = " ++ show noise
    putStrLn ""
    let encoded0 = Zq.encode_bit q False
    let encoded1 = Zq.encode_bit q True
    example "decode_bit (encode_bit False + 10)" $ Zq.decode_bit q (encoded0 + noise)
    example "decode_bit (encode_bit True + 10)" $ Zq.decode_bit q (encoded1 + noise)
    example "decode_bit (encode_bit False - 10)" $ Zq.decode_bit q (encoded0 - noise)
    example "decode_bit (encode_bit True - 10)" $ Zq.decode_bit q (encoded1 - noise)

    section "Vector Operations"
    let v1 = [1, 2, 3, 4, 5]
    let v2 = [10, 20, 30, 40, 50]
    example "inner_prod [1,2,3,4,5] [10,20,30,40,50]" $ Listvec.inner_prod v1 v2
    exampleVec "vec_add [1,2,3,4,5] [10,20,30,40,50]" $ Listvec.vec_add v1 v2
    exampleVec "vec_sub [10,20,30,40,50] [1,2,3,4,5]" $ Listvec.vec_sub v2 v1
    exampleVec "scalar_mult 3 [1,2,3,4,5]" $ Listvec.scalar_mult 3 v1

    section "Vector Modular Operations"
    let v3 = [7, 13, -2, 100, 255]
    let qMod = 10
    exampleVec "vec_mod [7,13,-2,100,255] 10" $ Zq.vec_mod v3 qMod
    exampleVec "vec_mod_centered [7,13,-2,100,255] 10" $ Zq.vec_mod_centered v3 qMod

    section "Matrix-Vector Multiplication"
    let matrix = [[1, 2, 3], [4, 5, 6], [7, 8, 9]]
    let vec = [1, 0, 1]
    exampleVec "mat_vec_mult [[1,2,3],[4,5,6],[7,8,9]] [1,0,1]" $ Listvec.mat_vec_mult matrix vec
    exampleVec "mat_vec_mult_mod same 10" $ Zq.mat_vec_mult_mod matrix vec 10

    section "Matrix Transpose"
    let matrix2 = [[1, 2], [3, 4], [5, 6]]
    putStrLn "  Original: [[1,2],[3,4],[5,6]]"
    exampleMat "transpose" $ Listvec.transpose matrix2

    section "Dilithium Helpers"
    let params44 = Dilithium.mldsa44Params
    let alpha44 = 2 * Dilithium.dilGamma2 params44
    example "Dilithium.modCentered 1234567 alpha44" $ Dilithium.modCentered 1234567 alpha44
    example "Dilithium.power2Round 1234567 d" $ Dilithium.power2Round 1234567 (Dilithium.dilD params44)
    example "Dilithium.decompose 1234567 alpha44" $ Dilithium.decompose 1234567 alpha44
    example "Dilithium.highBits 100000 alpha44" $ Dilithium.highBits 100000 alpha44
    example "Dilithium.makeHint 2000 100000 alpha44" $ Dilithium.makeHint 2000 100000 alpha44
    example "Dilithium.useHint 1 100000 alpha44" $ Dilithium.useHint 1 100000 alpha44
    example "Dilithium.checkBound 77 beta" $ Dilithium.checkBound 77 (Dilithium.dilBeta params44)
    example "Dilithium.hintWeight [[1,0,1],[0,1,0]]" $ Dilithium.hintWeight [[1, 0, 1], [0, 1, 0]]

    section "Performance: Inner Product"
    let size = 10000
    let bigV1 = replicate size 1
    let bigV2 = replicate size 2
    putStrLn $ "  Computing inner product of two " ++ show size ++ "-element vectors..."
    start <- getCurrentTime
    let result = Listvec.inner_prod bigV1 bigV2
    end <- result `seq` getCurrentTime
    putStrLn $ "  Result: " ++ show result
    putStrLn $ "  Time: " ++ show (diffUTCTime end start)

    section "Performance: Matrix-Vector Multiply"
    let rows = 100
    let cols = 100
    let bigMat = replicate rows (replicate cols 1)
    let bigVec = replicate cols 1
    putStrLn $ "  Computing " ++ show rows ++ "x" ++ show cols ++ " matrix * vector..."
    start2 <- getCurrentTime
    let result2 = Listvec.mat_vec_mult bigMat bigVec
    end2 <- (sum result2) `seq` getCurrentTime
    putStrLn $ "  Result sum: " ++ show (sum result2)
    putStrLn $ "  Time: " ++ show (diffUTCTime end2 start2)

    putStrLn ""
    putStrLn "====================================================="
    putStrLn "  All examples completed successfully!"
    putStrLn "  All operations are formally verified in Isabelle/HOL"
    putStrLn "====================================================="

section :: String -> IO ()
section name = do
    putStrLn ""
    putStrLn $ "--- " ++ name ++ " ---"
    putStrLn ""

example :: Show a => String -> a -> IO ()
example expr result = putStrLn $ "  " ++ expr ++ " = " ++ show result

exampleVec :: String -> [Int] -> IO ()
exampleVec expr result = putStrLn $ "  " ++ expr ++ "\n    = " ++ show result

exampleMat :: String -> [[Int]] -> IO ()
exampleMat expr result = do
    putStrLn $ "  " ++ expr ++ ":"
    mapM_ (\row -> putStrLn $ "    " ++ show row) result
