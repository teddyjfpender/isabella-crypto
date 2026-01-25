-- | Basic tests for the Isabella library
module Main where

import Canon
import System.Exit (exitSuccess, exitFailure)

main :: IO ()
main = do
    putStrLn "Running Isabella tests..."
    results <- sequence tests
    if and results
        then do
            putStrLn $ "\nAll " ++ show (length results) ++ " tests passed!"
            exitSuccess
        else do
            putStrLn "\nSome tests failed!"
            exitFailure

tests :: [IO Bool]
tests =
    [ test "mod_centered identity at 0" $
        mod_centered 0 5 == 0

    , test "mod_centered small positive" $
        mod_centered 2 5 == 2

    , test "mod_centered wraps large values" $
        mod_centered 7 5 == 2

    , test "mod_centered negative result" $
        mod_centered 8 5 == -2

    , test "dist0 is non-negative" $
        dist0 256 (-50) >= 0

    , test "dist0 of 0 is 0" $
        dist0 256 0 == 0

    , test "dist0 bound" $
        dist0 256 200 <= 128

    , test "encode_bit False is 0" $
        encode_bit 256 False == 0

    , test "encode_bit True is q/2" $
        encode_bit 256 True == 128

    , test "decode_bit near 0" $
        decode_bit 256 10 == False

    , test "decode_bit near q/2" $
        decode_bit 256 130 == True

    , test "encode/decode round-trip False" $
        decode_bit 256 (encode_bit 256 False) == False

    , test "encode/decode round-trip True" $
        decode_bit 256 (encode_bit 256 True) == True

    , test "encode/decode with small noise False" $
        decode_bit 256 (encode_bit 256 False + 10) == False

    , test "encode/decode with small noise True" $
        decode_bit 256 (encode_bit 256 True + 10) == True

    , test "inner_prod simple" $
        inner_prod [1,2,3] [4,5,6] == 32

    , test "inner_prod zeros" $
        inner_prod [0,0,0] [1,2,3] == 0

    , test "vec_add" $
        vec_add [1,2,3] [4,5,6] == [5,7,9]

    , test "vec_sub" $
        vec_sub [5,7,9] [1,2,3] == [4,5,6]

    , test "scalar_mult" $
        scalar_mult 3 [1,2,3] == [3,6,9]

    , test "vec_neg" $
        vec_neg [1,-2,3] == [-1,2,-3]

    , test "vec_mod" $
        vec_mod [7,13,-2] 5 == [2,3,3]

    , test "mat_vec_mult" $
        mat_vec_mult [[1,0],[0,1]] [3,4] == [3,4]

    , test "transpose" $
        transpose [[1,2],[3,4]] == [[1,3],[2,4]]

    , test "valid_vec true" $
        valid_vec 3 [1,2,3] == True

    , test "valid_vec false" $
        valid_vec 3 [1,2] == False

    , test "split_vec" $
        split_vec 2 [1,2,3,4,5] == ([1,2], [3,4,5])

    , test "vec_concat" $
        vec_concat [1,2] [3,4,5] == [1,2,3,4,5]
    ]

test :: String -> Bool -> IO Bool
test name result = do
    if result
        then putStrLn $ "  ✓ " ++ name
        else putStrLn $ "  ✗ " ++ name
    return result
