-- | CLI command handlers
module CLI.Commands (OutputFormat(..), runCommand) where

import Control.Exception (evaluate)
import Control.Monad (replicateM, replicateM_)
import qualified Canon.Commit_sis as Commit
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Confidential_transaction as ConfidentialTransaction
import qualified Canon.Dilithium as Dilithium
import qualified Canon.Listvec as Listvec
import qualified Canon.Zq as Zq
import Data.List (intercalate, sort)
import GHC.Clock (getMonotonicTimeNSec)
import Text.Read (readMaybe)

data OutputFormat = Human | Json
  deriving (Eq, Show)

runCommand :: OutputFormat -> String -> [String] -> IO ()
runCommand format cmd args = case cmd of
    "mod-centered" -> cmdModCentered format args
    "dist0" -> cmdDist0 format args
    "encode-bit" -> cmdEncodeBit format args
    "decode-bit" -> cmdDecodeBit format args
    "inner-prod" -> cmdInnerProd format args
    "vec-add" -> cmdVecAdd format args
    "transpose" -> cmdTranspose format args
    "mat-vec-mult" -> cmdMatVecMult format args
    "dil-mod-centered" -> cmdDilModCentered format args
    "dil-power2round" -> cmdDilPower2Round format args
    "dil-decompose" -> cmdDilDecompose format args
    "dil-highbits" -> cmdDilHighBits format args
    "dil-lowbits" -> cmdDilLowBits format args
    "dil-makehint" -> cmdDilMakeHint format args
    "dil-usehint" -> cmdDilUseHint format args
    "dil-params" -> cmdDilParams format args
    "dil-check-bound" -> cmdDilCheckBound format args
    "dil-hint-weight" -> cmdDilHintWeight format args
    "cb-params" -> cmdCbParams format args
    "cb-valid-params" -> cmdCbValidParams format args
    "cb-rand-commit-key" -> cmdCbRandCommitKey format args
    "cb-rand-commit" -> cmdCbRandCommit format args
    "cb-valid-witness" -> cmdCbValidWitness format args
    "cb-valid-mask" -> cmdCbValidMask format args
    "cb-valid-response" -> cmdCbValidResponse format args
    "cb-balance-commitment" -> cmdCbBalanceCommitment format args
    "cb-canonical-challenge" -> cmdCbCanonicalChallenge format args
    "cb-sigma-commit" -> cmdCbSigmaCommit format args
    "cb-sigma-respond" -> cmdCbSigmaRespond format args
    "cb-sigma-verify" -> cmdCbSigmaVerify format args
    "cb-prove" -> cmdCbProve format args
    "cb-verify" -> cmdCbVerify format args
    "cr-amount-commitment" -> cmdCrAmountCommitment format args
    "cr-prove" -> cmdCrProve format args
    "cr-verify" -> cmdCrVerify format args
    "cr-verify-bench" -> cmdCrVerifyBench format args
    "ct-nullifier" -> cmdCtNullifier format args
    "ct-nullifier-canonical-challenge" -> cmdCtNullifierCanonicalChallenge format args
    "ct-nullifier-prove" -> cmdCtNullifierProve format args
    "ct-nullifier-verify" -> cmdCtNullifierVerify format args
    "ct-member-prove" -> cmdCtMemberProve format args
    "ct-member-verify" -> cmdCtMemberVerify format args
    "ct-ledger-step-verify" -> cmdCtLedgerStepVerify format args
    "ct-prove" -> cmdCtProve format args
    "ct-verify" -> cmdCtVerify format args
    "ct-verify-bench" -> cmdCtVerifyBench format args
    _ -> putStrLn $ "Unknown command: " ++ cmd ++ "\nUse --help for usage."

-- Parse helpers
parseInt :: String -> Maybe Int
parseInt = readMaybe

parseVec :: String -> Maybe [Int]
parseVec s = readMaybe s

parseMat :: String -> Maybe [[Int]]
parseMat s = readMaybe s

parseCube :: String -> Maybe [[[Int]]]
parseCube s = readMaybe s

parse4D :: String -> Maybe [[[[Int]]]]
parse4D s = readMaybe s

parseBool :: String -> Maybe Bool
parseBool "0" = Just False
parseBool "1" = Just True
parseBool "false" = Just False
parseBool "true" = Just True
parseBool "False" = Just False
parseBool "True" = Just True
parseBool _ = Nothing

jsonString :: String -> String
jsonString = show

jsonBool :: Bool -> String
jsonBool True = "true"
jsonBool False = "false"

jsonBoolList :: [Bool] -> String
jsonBoolList = ("[" ++) . (++ "]") . intercalate "," . map jsonBool

jsonVec :: [Int] -> String
jsonVec = ("[" ++) . (++ "]") . intercalate "," . map show

jsonMat :: [[Int]] -> String
jsonMat = ("[" ++) . (++ "]") . intercalate "," . map jsonVec

jsonCube :: [[[Int]]] -> String
jsonCube = ("[" ++) . (++ "]") . intercalate "," . map jsonMat

jsonObject :: [(String, String)] -> String
jsonObject fields =
    "{" ++ intercalate "," [jsonString key ++ ":" ++ value | (key, value) <- fields] ++ "}"

data BenchStats = BenchStats
  { benchValid :: Bool
  , benchIterations :: Int
  , benchWarmup :: Int
  , benchTotalNs :: Integer
  , benchMeanNs :: Double
  , benchMedianNs :: Double
  , benchStdevNs :: Double
  , benchMinNs :: Integer
  , benchMaxNs :: Integer
  }

meanNs :: [Integer] -> Double
meanNs [] = 0
meanNs xs = fromIntegral (sum xs) / fromIntegral (length xs)

medianNs :: [Integer] -> Double
medianNs [] = 0
medianNs xs =
    let sorted = sort xs
        len = length sorted
        mid = len `div` 2
     in if odd len
            then fromIntegral (sorted !! mid)
            else (fromIntegral (sorted !! (mid - 1)) + fromIntegral (sorted !! mid)) / 2

stdevNs :: [Integer] -> Double -> Double
stdevNs [] _ = 0
stdevNs [_] _ = 0
stdevNs xs mean =
    let variance =
            sum [diff * diff | sample <- xs, let diff = fromIntegral sample - mean]
                / fromIntegral (length xs - 1)
     in sqrt variance

benchmarkBool :: Int -> Int -> (() -> Bool) -> IO BenchStats
benchmarkBool warmup iterations verify = do
    let sample = do
            start <- getMonotonicTimeNSec
            valid <- evaluate (verify ())
            end <- getMonotonicTimeNSec
            pure (valid, toInteger (end - start))
    replicateM_ warmup (evaluate (verify ()) >> pure ())
    samples <- replicateM iterations sample
    let valids = map fst samples
        times = map snd samples
        total = sum times
        mean = meanNs times
        median = medianNs times
        minNs = if null times then 0 else minimum times
        maxNs = if null times then 0 else maximum times
    pure
        BenchStats
            { benchValid = and valids
            , benchIterations = iterations
            , benchWarmup = warmup
            , benchTotalNs = total
            , benchMeanNs = mean
            , benchMedianNs = median
            , benchStdevNs = stdevNs times mean
            , benchMinNs = minNs
            , benchMaxNs = maxNs
            }

jsonBenchStats :: BenchStats -> String
jsonBenchStats stats =
    jsonObject
        [ ("valid", jsonBool (benchValid stats))
        , ("iterations", show (benchIterations stats))
        , ("warmup", show (benchWarmup stats))
        , ("totalNs", show (benchTotalNs stats))
        , ("meanNs", show (benchMeanNs stats))
        , ("medianNs", show (benchMedianNs stats))
        , ("stdevNs", show (benchStdevNs stats))
        , ("minNs", show (benchMinNs stats))
        , ("maxNs", show (benchMaxNs stats))
        ]

outputBenchStats :: OutputFormat -> String -> BenchStats -> IO ()
outputBenchStats Human label stats =
    putStrLn $
        label ++
        " valid=" ++ show (benchValid stats) ++
        ", iterations=" ++ show (benchIterations stats) ++
        ", warmup=" ++ show (benchWarmup stats) ++
        ", totalNs=" ++ show (benchTotalNs stats) ++
        ", meanNs=" ++ show (benchMeanNs stats) ++
        ", medianNs=" ++ show (benchMedianNs stats) ++
        ", stdevNs=" ++ show (benchStdevNs stats) ++
        ", minNs=" ++ show (benchMinNs stats) ++
        ", maxNs=" ++ show (benchMaxNs stats)
outputBenchStats Json _ stats =
    putStrLn $ "{\"result\":" ++ jsonBenchStats stats ++ "}"

outputError :: OutputFormat -> String -> IO ()
outputError Human msg = putStrLn $ "Error: " ++ msg
outputError Json msg = putStrLn $ "{\"error\":" ++ jsonString msg ++ "}"

outputUsage :: OutputFormat -> String -> IO ()
outputUsage Human msg = putStrLn msg
outputUsage Json msg = putStrLn $ "{\"error\":" ++ jsonString msg ++ "}"

outputIntResult :: OutputFormat -> String -> Int -> IO ()
outputIntResult Human label result = putStrLn $ label ++ show result
outputIntResult Json _ result = putStrLn $ "{\"result\":" ++ show result ++ "}"

outputBoolResult :: OutputFormat -> String -> Bool -> IO ()
outputBoolResult Human label result = putStrLn $ label ++ show result
outputBoolResult Json _ result = putStrLn $ "{\"result\":" ++ jsonBool result ++ "}"

outputVecResult :: OutputFormat -> String -> [Int] -> IO ()
outputVecResult Human label result = putStrLn $ label ++ show result
outputVecResult Json _ result = putStrLn $ "{\"result\":" ++ jsonVec result ++ "}"

outputMatResult :: OutputFormat -> String -> [[Int]] -> IO ()
outputMatResult Human label result = putStrLn $ label ++ show result
outputMatResult Json _ result = putStrLn $ "{\"result\":" ++ jsonMat result ++ "}"

jsonCbParams :: Commit.CommitParams -> String
jsonCbParams params =
    jsonObject
        [ ("n1", show (Commit.cp_n1 params))
        , ("n2", show (Commit.cp_n2 params))
        , ("m", show (Commit.cp_m params))
        , ("q", show (Commit.cp_q params))
        , ("beta", show (Commit.cp_beta params))
        ]

jsonCbProof :: ConfidentialBalance.BalanceProof -> String
jsonCbProof proof =
    jsonObject
        [ ("as", jsonMat (ConfidentialBalance.balance_as proof))
        , ("zs", jsonMat (ConfidentialBalance.balance_zs proof))
        ]

jsonCrProof :: ConfidentialRange.RangeProof -> String
jsonCrProof proof =
    jsonObject
        [ ("bits", jsonMat (ConfidentialRange.range_bits proof))
        , ("comps", jsonMat (ConfidentialRange.range_comps proof))
        , ("amountAs", jsonMat (ConfidentialRange.range_amount_as proof))
        , ("amountZs", jsonMat (ConfidentialRange.range_amount_zs proof))
        , ("pairAss", jsonCube (ConfidentialRange.range_pair_ass proof))
        , ("pairZss", jsonCube (ConfidentialRange.range_pair_zss proof))
        ]

jsonCtNullifierProof :: ConfidentialTransaction.NullifierProof -> String
jsonCtNullifierProof proof =
    jsonObject
        [ ("aCommits", jsonMat (ConfidentialTransaction.nullifier_a_commits proof))
        , ("aNullifiers", jsonMat (ConfidentialTransaction.nullifier_a_nullifiers proof))
        , ("zMsgs", jsonMat (ConfidentialTransaction.nullifier_z_msgs proof))
        , ("zRands", jsonMat (ConfidentialTransaction.nullifier_z_rands proof))
        ]

jsonCtMembershipProof :: ConfidentialTransaction.MembershipProof -> String
jsonCtMembershipProof proof =
    jsonObject
        [ ("index", show (ConfidentialTransaction.member_index proof))
        , ("root", jsonVec (ConfidentialTransaction.member_root proof))
        , ("siblings", jsonMat (ConfidentialTransaction.member_siblings proof))
        , ("directions", jsonBoolList (ConfidentialTransaction.member_directions proof))
        ]

jsonCtTransactionProof :: ConfidentialTransaction.TransactionProof -> String
jsonCtTransactionProof proof =
    jsonObject
        [ ("in1Member", jsonCtMembershipProof (ConfidentialTransaction.tx_in1_member proof))
        , ("in2Member", jsonCtMembershipProof (ConfidentialTransaction.tx_in2_member proof))
        , ("in1Nullifier", jsonCtNullifierProof (ConfidentialTransaction.tx_in1_nullifier proof))
        , ("in2Nullifier", jsonCtNullifierProof (ConfidentialTransaction.tx_in2_nullifier proof))
        , ("balance", jsonCbProof (ConfidentialTransaction.tx_balance proof))
        , ("out1Range", jsonCrProof (ConfidentialTransaction.tx_out1_range proof))
        , ("out2Range", jsonCrProof (ConfidentialTransaction.tx_out2_range proof))
        ]

parseCbParams :: String -> String -> String -> String -> Maybe Commit.CommitParams
parseCbParams mStr n2Str qStr betaStr =
    case (parseInt mStr, parseInt n2Str, parseInt qStr, parseInt betaStr) of
        (Just m, Just n2, Just q, Just beta) ->
            Just (ConfidentialBalance.makeScalarCommitParams m n2 q beta)
        _ -> Nothing

makeScalarOpening :: Int -> [Int] -> Commit.CommitOpening
makeScalarOpening amount rand = Commit.makeOpening [amount] rand

makeScalarOpenings :: [Int] -> [[Int]] -> Maybe [Commit.CommitOpening]
makeScalarOpenings amounts rands
    | length amounts == length rands = Just (zipWith makeScalarOpening amounts rands)
    | otherwise = Nothing

makeVerifiedNotes ::
  [[Int]] ->
  [[[Int]]] ->
  [[[Int]]] ->
  [[[Int]]] ->
  [[[Int]]] ->
  [[[[Int]]]] ->
  [[[[Int]]]] ->
  Maybe [ConfidentialTransaction.VerifiedNote]
makeVerifiedNotes commitments bits comps amountAs amountZs pairAs pairZs
  | allEqual
      [ length commitments
      , length bits
      , length comps
      , length amountAs
      , length amountZs
      , length pairAs
      , length pairZs
      ] =
      Just
        (zipWith7
          (\commitment bitRows compRows amountA amountZ pairRows pairZRows ->
            ConfidentialTransaction.makeVerifiedNote
              commitment
              (ConfidentialRange.makeRangeProof bitRows compRows amountA amountZ pairRows pairZRows))
          commitments
          bits
          comps
          amountAs
          amountZs
          pairAs
          pairZs)
  | otherwise = Nothing
  where
    allEqual [] = True
    allEqual (x:xs) = all (== x) xs
    zipWith7 _ [] [] [] [] [] [] [] = []
    zipWith7 f (a:as) (b:bs) (c:cs) (d:ds) (e:es) (g:gs) (h:hs) =
      f a b c d e g h : zipWith7 f as bs cs ds es gs hs
    zipWith7 _ _ _ _ _ _ _ _ = []

prepareCrVerify :: [String] -> Either String (() -> Bool)
prepareCrVerify [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, cAmountStr, bitsStr, compsStr, amountAsStr, amountZsStr, pairAssStr, pairZssStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseInt kStr
        , parseMat ckStr
        , parseVec cAmountStr
        , parseMat bitsStr
        , parseMat compsStr
        , parseMat amountAsStr
        , parseMat amountZsStr
        , parseCube pairAssStr
        , parseCube pairZssStr
        ) of
        (Just params, Just gamma, Just k, Just ck, Just cAmount, Just bits, Just comps, Just amountAs, Just amountZs, Just pairAss, Just pairZss) ->
            let proof = ConfidentialRange.makeRangeProof bits comps amountAs amountZs pairAss pairZss
             in Right (\() -> ConfidentialRange.rangeFsVerify params gamma k ck cAmount proof)
        _ -> Left "Expected params, gamma, commitment key, amount commitment, and proof fields"
prepareCrVerify _ =
    Left "Usage: cr-verify M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

prepareCtVerify :: [String] -> Either String (() -> Bool)
prepareCtVerify [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, ledgerStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1ACommitsStr, in1ANullifiersStr, in1ZMsgsStr, in1ZRandsStr, in2ACommitsStr, in2ANullifiersStr, in2ZMsgsStr, in2ZRandsStr, balanceAStr, balanceZsStr, out1BitsStr, out1CompsStr, out1AmountAStr, out1AmountZStr, out1PairAsStr, out1PairZsStr, out2BitsStr, out2CompsStr, out2AmountAStr, out2AmountZStr, out2PairAsStr, out2PairZsStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseInt kStr
        , parseMat ckStr
        , parseMat nkStr
        , parseMat ledgerStr
        , parseMat spentStr
        , parseVec cIn1Str
        , parseVec cIn2Str
        , parseVec cOut1Str
        , parseVec cOut2Str
        , parseVec nf1Str
        , parseVec nf2Str
        , parseMat in1ACommitsStr
        , parseMat in1ANullifiersStr
        , parseMat in1ZMsgsStr
        , parseMat in1ZRandsStr
        , parseMat in2ACommitsStr
        , parseMat in2ANullifiersStr
        , parseMat in2ZMsgsStr
        , parseMat in2ZRandsStr
        , parseMat balanceAStr
        , parseMat balanceZsStr
        , parseMat out1BitsStr
        , parseMat out1CompsStr
        , parseMat out1AmountAStr
        , parseMat out1AmountZStr
        , parseCube out1PairAsStr
        , parseCube out1PairZsStr
        , parseMat out2BitsStr
        , parseMat out2CompsStr
        , parseMat out2AmountAStr
        , parseMat out2AmountZStr
        , parseCube out2PairAsStr
        , parseCube out2PairZsStr
        ) of
        (Just params, Just gamma, Just k, Just ck, Just nk, Just ledger, Just spent, Just cIn1, Just cIn2, Just cOut1, Just cOut2, Just nf1, Just nf2, Just in1ACommits, Just in1ANullifiers, Just in1ZMsgs, Just in1ZRands, Just in2ACommits, Just in2ANullifiers, Just in2ZMsgs, Just in2ZRands, Just balanceAs, Just balanceZs, Just out1Bits, Just out1Comps, Just out1AmountA, Just out1AmountZ, Just out1PairAs, Just out1PairZs, Just out2Bits, Just out2Comps, Just out2AmountA, Just out2AmountZ, Just out2PairAs, Just out2PairZs) ->
            let root = ConfidentialTransaction.ledgerRoot params ledger
             in case
                    ( ConfidentialTransaction.membershipProve params ledger cIn1
                    , ConfidentialTransaction.membershipProve params ledger cIn2
                    ) of
                    (Just in1Member, Just in2Member) ->
                        let proof =
                                ConfidentialTransaction.makeTransactionProof
                                    in1Member
                                    in2Member
                                    (ConfidentialTransaction.makeNullifierProof in1ACommits in1ANullifiers in1ZMsgs in1ZRands)
                                    (ConfidentialTransaction.makeNullifierProof in2ACommits in2ANullifiers in2ZMsgs in2ZRands)
                                    (ConfidentialBalance.makeBalanceProof balanceAs balanceZs)
                                    (ConfidentialRange.makeRangeProof out1Bits out1Comps out1AmountA out1AmountZ out1PairAs out1PairZs)
                                    (ConfidentialRange.makeRangeProof out2Bits out2Comps out2AmountA out2AmountZ out2PairAs out2PairZs)
                         in Right
                                (\() ->
                                    ConfidentialTransaction.transactionFsVerify
                                        params gamma k ck nk root spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof)
                    _ -> Left "Expected membership proofs for both input commitments in the supplied ledger"
        _ -> Left "Expected params, keys, ledger, commitments, nullifiers, and transaction-proof fields"
prepareCtVerify _ =
    Left "Usage: ct-verify M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

-- Command implementations

cmdModCentered :: OutputFormat -> [String] -> IO ()
cmdModCentered format [xStr, qStr] =
    case (parseInt xStr, parseInt qStr) of
        (Just x, Just q) -> do
            let result = Zq.mod_centered x q
            outputIntResult format ("mod_centered " ++ show x ++ " " ++ show q ++ " = ") result
        _ -> outputError format "Expected two integers (X Q)"
cmdModCentered format _ = outputUsage format "Usage: mod-centered X Q"

cmdDist0 :: OutputFormat -> [String] -> IO ()
cmdDist0 format [qStr, xStr] =
    case (parseInt qStr, parseInt xStr) of
        (Just q, Just x) -> do
            let result = Zq.dist0 q x
            outputIntResult format ("dist0 " ++ show q ++ " " ++ show x ++ " = ") result
        _ -> outputError format "Expected two integers (Q X)"
cmdDist0 format _ = outputUsage format "Usage: dist0 Q X"

cmdEncodeBit :: OutputFormat -> [String] -> IO ()
cmdEncodeBit format [qStr, bStr] =
    case (parseInt qStr, parseBool bStr) of
        (Just q, Just b) -> do
            let result = Zq.encode_bit q b
            outputIntResult format ("encode_bit " ++ show q ++ " " ++ show b ++ " = ") result
        _ -> outputError format "Expected integer Q and boolean B (0/1 or true/false)"
cmdEncodeBit format _ = outputUsage format "Usage: encode-bit Q B"

cmdDecodeBit :: OutputFormat -> [String] -> IO ()
cmdDecodeBit format [qStr, xStr] =
    case (parseInt qStr, parseInt xStr) of
        (Just q, Just x) -> do
            let result = Zq.decode_bit q x
            outputBoolResult format ("decode_bit " ++ show q ++ " " ++ show x ++ " = ") result
        _ -> outputError format "Expected two integers (Q X)"
cmdDecodeBit format _ = outputUsage format "Usage: decode-bit Q X"

cmdInnerProd :: OutputFormat -> [String] -> IO ()
cmdInnerProd format [v1Str, v2Str] =
    case (parseVec v1Str, parseVec v2Str) of
        (Just v1, Just v2) -> do
            let result = Listvec.inner_prod v1 v2
            outputIntResult format ("inner_prod " ++ show v1 ++ " " ++ show v2 ++ " = ") result
        _ -> outputError format "Expected two vectors (e.g., \"[1,2,3]\" \"[4,5,6]\")"
cmdInnerProd format _ = outputUsage format "Usage: inner-prod \"[v1]\" \"[v2]\""

cmdVecAdd :: OutputFormat -> [String] -> IO ()
cmdVecAdd format [v1Str, v2Str] =
    case (parseVec v1Str, parseVec v2Str) of
        (Just v1, Just v2) -> do
            let result = Listvec.vec_add v1 v2
            outputVecResult format ("vec_add " ++ show v1 ++ " " ++ show v2 ++ " = ") result
        _ -> outputError format "Expected two vectors"
cmdVecAdd format _ = outputUsage format "Usage: vec-add \"[v1]\" \"[v2]\""

cmdTranspose :: OutputFormat -> [String] -> IO ()
cmdTranspose format [mStr] =
    case parseMat mStr of
        Just m -> do
            let result = Listvec.transpose m
            outputMatResult format ("transpose " ++ show m ++ " = ") result
        _ -> outputError format "Expected a matrix"
cmdTranspose format _ = outputUsage format "Usage: transpose \"[[row1],[row2]]\""

cmdMatVecMult :: OutputFormat -> [String] -> IO ()
cmdMatVecMult format [mStr, vStr, qStr] =
    case (parseMat mStr, parseVec vStr, parseInt qStr) of
        (Just m, Just v, Just q) -> do
            let result = Zq.mat_vec_mult_mod m v q
            case format of
                Human -> do
                    putStrLn "mat_vec_mult_mod"
                    putStrLn $ "  A = " ++ show m
                    putStrLn $ "  v = " ++ show v
                    putStrLn $ "  q = " ++ show q
                    putStrLn $ "  result = " ++ show result
                Json -> putStrLn $ "{\"result\":" ++ jsonVec result ++ "}"
        _ -> outputError format "Expected matrix M, vector V, and modulus Q"
cmdMatVecMult format _ = outputUsage format "Usage: mat-vec-mult \"[[row1],[row2]]\" \"[v]\" Q"

cmdDilModCentered :: OutputFormat -> [String] -> IO ()
cmdDilModCentered format [rStr, mStr] =
    case (parseInt rStr, parseInt mStr) of
        (Just r, Just m) ->
            let result = Dilithium.modCentered r m
            in case format of
                Human -> putStrLn $ "mod_centered " ++ show r ++ " " ++ show m ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("r", show r), ("m", show m), ("result", show result)]
        _ -> outputError format "Expected two integers (R M)"
cmdDilModCentered format _ = outputUsage format "Usage: dil-mod-centered R M"

cmdDilPower2Round :: OutputFormat -> [String] -> IO ()
cmdDilPower2Round format [rStr, dStr] =
    case (parseInt rStr, parseInt dStr) of
        (Just r, Just d) ->
            let (r1, r0) = Dilithium.power2Round r d
            in case format of
                Human -> putStrLn $ "power2round " ++ show r ++ " " ++ show d ++ " = (r1=" ++ show r1 ++ ", r0=" ++ show r0 ++ ")"
                Json -> putStrLn $ jsonObject [("r", show r), ("d", show d), ("r1", show r1), ("r0", show r0)]
        _ -> outputError format "Expected two integers (R D)"
cmdDilPower2Round format _ = outputUsage format "Usage: dil-power2round R D"

cmdDilDecompose :: OutputFormat -> [String] -> IO ()
cmdDilDecompose format [rStr, alphaStr] =
    case (parseInt rStr, parseInt alphaStr) of
        (Just r, Just alpha) ->
            let (r1, r0) = Dilithium.decompose r alpha
            in case format of
                Human -> putStrLn $ "decompose " ++ show r ++ " " ++ show alpha ++ " = (r1=" ++ show r1 ++ ", r0=" ++ show r0 ++ ")"
                Json -> putStrLn $ jsonObject [("r", show r), ("alpha", show alpha), ("r1", show r1), ("r0", show r0)]
        _ -> outputError format "Expected two integers (R ALPHA)"
cmdDilDecompose format _ = outputUsage format "Usage: dil-decompose R ALPHA"

cmdDilHighBits :: OutputFormat -> [String] -> IO ()
cmdDilHighBits format [rStr, alphaStr] =
    case (parseInt rStr, parseInt alphaStr) of
        (Just r, Just alpha) ->
            let result = Dilithium.highBits r alpha
            in case format of
                Human -> putStrLn $ "highbits " ++ show r ++ " " ++ show alpha ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("r", show r), ("alpha", show alpha), ("result", show result)]
        _ -> outputError format "Expected two integers (R ALPHA)"
cmdDilHighBits format _ = outputUsage format "Usage: dil-highbits R ALPHA"

cmdDilLowBits :: OutputFormat -> [String] -> IO ()
cmdDilLowBits format [rStr, alphaStr] =
    case (parseInt rStr, parseInt alphaStr) of
        (Just r, Just alpha) ->
            let result = Dilithium.lowBits r alpha
            in case format of
                Human -> putStrLn $ "lowbits " ++ show r ++ " " ++ show alpha ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("r", show r), ("alpha", show alpha), ("result", show result)]
        _ -> outputError format "Expected two integers (R ALPHA)"
cmdDilLowBits format _ = outputUsage format "Usage: dil-lowbits R ALPHA"

cmdDilMakeHint :: OutputFormat -> [String] -> IO ()
cmdDilMakeHint format [zStr, rStr, alphaStr] =
    case (parseInt zStr, parseInt rStr, parseInt alphaStr) of
        (Just z, Just r, Just alpha) ->
            let result = Dilithium.makeHint z r alpha
            in case format of
                Human -> putStrLn $ "makehint z=" ++ show z ++ " r=" ++ show r ++ " alpha=" ++ show alpha ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("z", show z), ("r", show r), ("alpha", show alpha), ("result", show result)]
        _ -> outputError format "Expected three integers (Z R ALPHA)"
cmdDilMakeHint format _ = outputUsage format "Usage: dil-makehint Z R ALPHA"

cmdDilUseHint :: OutputFormat -> [String] -> IO ()
cmdDilUseHint format [hStr, rStr, alphaStr] =
    case (parseInt hStr, parseInt rStr, parseInt alphaStr) of
        (Just h, Just r, Just alpha) ->
            let result = Dilithium.useHint h r alpha
            in case format of
                Human -> putStrLn $ "usehint h=" ++ show h ++ " r=" ++ show r ++ " alpha=" ++ show alpha ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("h", show h), ("r", show r), ("alpha", show alpha), ("result", show result)]
        _ -> outputError format "Expected three integers (H R ALPHA)"
cmdDilUseHint format _ = outputUsage format "Usage: dil-usehint H R ALPHA"

cmdDilParams :: OutputFormat -> [String] -> IO ()
cmdDilParams format [variant] =
    case Dilithium.paramsByName variant of
        Just params ->
            case format of
                Human -> do
                    putStrLn $ "ML-DSA-" ++ variant ++ " parameters:"
                    putStrLn $ "  n=" ++ show (Dilithium.dilN params)
                        ++ ", q=" ++ show (Dilithium.dilQ params)
                        ++ ", k=" ++ show (Dilithium.dilK params)
                        ++ ", l=" ++ show (Dilithium.dilL params)
                    putStrLn $ "  eta=" ++ show (Dilithium.dilEta params)
                        ++ ", tau=" ++ show (Dilithium.dilTau params)
                        ++ ", beta=" ++ show (Dilithium.dilBeta params)
                    putStrLn $ "  gamma1=" ++ show (Dilithium.dilGamma1 params)
                        ++ ", gamma2=" ++ show (Dilithium.dilGamma2 params)
                        ++ ", d=" ++ show (Dilithium.dilD params)
                        ++ ", omega=" ++ show (Dilithium.dilOmega params)
                Json ->
                    putStrLn $ jsonObject
                        [ ("n", show (Dilithium.dilN params))
                        , ("q", show (Dilithium.dilQ params))
                        , ("k", show (Dilithium.dilK params))
                        , ("l", show (Dilithium.dilL params))
                        , ("eta", show (Dilithium.dilEta params))
                        , ("tau", show (Dilithium.dilTau params))
                        , ("beta", show (Dilithium.dilBeta params))
                        , ("gamma1", show (Dilithium.dilGamma1 params))
                        , ("gamma2", show (Dilithium.dilGamma2 params))
                        , ("d", show (Dilithium.dilD params))
                        , ("omega", show (Dilithium.dilOmega params))
                        ]
        Nothing -> outputError format "Unknown variant. Use 44, 65, or 87"
cmdDilParams format _ = outputUsage format "Usage: dil-params VARIANT (44, 65, or 87)"

cmdDilCheckBound :: OutputFormat -> [String] -> IO ()
cmdDilCheckBound format [valueStr, boundStr] =
    case (parseInt valueStr, parseInt boundStr) of
        (Just value, Just bound) ->
            let result = Dilithium.checkBound value bound
            in case format of
                Human -> putStrLn $ "coeff_in_range " ++ show value ++ " " ++ show bound ++ " = " ++ show result
                Json -> putStrLn $ jsonObject [("value", show value), ("bound", show bound), ("result", jsonBool result)]
        _ -> outputError format "Expected two integers (VALUE BOUND)"
cmdDilCheckBound format _ = outputUsage format "Usage: dil-check-bound VALUE BOUND"

cmdDilHintWeight :: OutputFormat -> [String] -> IO ()
cmdDilHintWeight format [hintsStr] =
    case parseMat hintsStr of
        Just hints ->
            let result = Dilithium.hintWeight hints
            in outputIntResult format "hint_weight = " result
        Nothing -> outputError format "Expected a matrix of hint bits"
cmdDilHintWeight format _ = outputUsage format "Usage: dil-hint-weight \"[[1,0,1],[0,1,0]]\""

cmdCbParams :: OutputFormat -> [String] -> IO ()
cmdCbParams format [mStr, n2Str, qStr, betaStr] =
    case parseCbParams mStr n2Str qStr betaStr of
        Just params ->
            case format of
                Human -> putStrLn $ "scalar_commit_params = " ++ show params
                Json -> putStrLn $ jsonCbParams params
        Nothing -> outputError format "Expected four integers (M N2 Q BETA)"
cmdCbParams format _ = outputUsage format "Usage: cb-params M N2 Q BETA"

cmdCbValidParams :: OutputFormat -> [String] -> IO ()
cmdCbValidParams format [mStr, n2Str, qStr, betaStr] =
    case parseCbParams mStr n2Str qStr betaStr of
        Just params ->
            outputBoolResult format "valid_scalar_commit_params = "
                (ConfidentialBalance.validScalarCommitParams params)
        Nothing -> outputError format "Expected four integers (M N2 Q BETA)"
cmdCbValidParams format _ = outputUsage format "Usage: cb-valid-params M N2 Q BETA"

cmdCbRandCommitKey :: OutputFormat -> [String] -> IO ()
cmdCbRandCommitKey format [mStr, n2Str, qStr, betaStr, ckStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ckStr) of
        (Just params, Just ck) ->
            outputMatResult format "rand_commit_key = "
                (ConfidentialBalance.randCommitKey params ck)
        _ -> outputError format "Expected params (M N2 Q BETA) and a commitment-key matrix"
cmdCbRandCommitKey format _ = outputUsage format "Usage: cb-rand-commit-key M N2 Q BETA \"[[row1],[row2]]\""

cmdCbRandCommit :: OutputFormat -> [String] -> IO ()
cmdCbRandCommit format [mStr, n2Str, qStr, betaStr, ckStr, rStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ckStr, parseVec rStr) of
        (Just params, Just ck, Just r) ->
            outputVecResult format "rand_commit = "
                (ConfidentialBalance.randCommit params ck r)
        _ -> outputError format "Expected params (M N2 Q BETA), commitment key matrix, and witness vector"
cmdCbRandCommit format _ = outputUsage format "Usage: cb-rand-commit M N2 Q BETA \"[[row1],[row2]]\" \"[r]\""

cmdCbValidWitness :: OutputFormat -> [String] -> IO ()
cmdCbValidWitness format [mStr, n2Str, qStr, betaStr, rStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseVec rStr) of
        (Just params, Just r) ->
            outputBoolResult format "valid_balance_witness = "
                (ConfidentialBalance.validBalanceWitness params r)
        _ -> outputError format "Expected params (M N2 Q BETA) and a witness vector"
cmdCbValidWitness format _ = outputUsage format "Usage: cb-valid-witness M N2 Q BETA \"[r]\""

cmdCbValidMask :: OutputFormat -> [String] -> IO ()
cmdCbValidMask format [mStr, n2Str, qStr, betaStr, gammaStr, yStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr, parseVec yStr) of
        (Just params, Just gamma, Just y) ->
            outputBoolResult format "valid_balance_mask = "
                (ConfidentialBalance.validBalanceMask params gamma y)
        _ -> outputError format "Expected params (M N2 Q BETA), gamma, and a mask vector"
cmdCbValidMask format _ = outputUsage format "Usage: cb-valid-mask M N2 Q BETA GAMMA \"[y]\""

cmdCbValidResponse :: OutputFormat -> [String] -> IO ()
cmdCbValidResponse format [mStr, n2Str, qStr, betaStr, gammaStr, challengeStr, zStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr, parseInt challengeStr, parseVec zStr) of
        (Just params, Just gamma, Just challenge, Just z) ->
            outputBoolResult format "valid_balance_response = "
                (ConfidentialBalance.validBalanceResponse params gamma challenge z)
        _ -> outputError format "Expected params (M N2 Q BETA), gamma, an integer challenge, and a response vector"
cmdCbValidResponse format _ = outputUsage format "Usage: cb-valid-response M N2 Q BETA GAMMA CHALLENGE \"[z]\""

cmdCbBalanceCommitment :: OutputFormat -> [String] -> IO ()
cmdCbBalanceCommitment format [cIn1Str, cIn2Str, cOut1Str, cOut2Str, qStr] =
    case (parseVec cIn1Str, parseVec cIn2Str, parseVec cOut1Str, parseVec cOut2Str, parseInt qStr) of
        (Just cIn1, Just cIn2, Just cOut1, Just cOut2, Just q) ->
            outputVecResult format "balance_commitment = "
                (ConfidentialBalance.balanceCommitment cIn1 cIn2 cOut1 cOut2 q)
        _ -> outputError format "Expected four commitment vectors and modulus Q"
cmdCbBalanceCommitment format _ =
    outputUsage format "Usage: cb-balance-commitment \"[c1]\" \"[c2]\" \"[c3]\" \"[c4]\" Q"

cmdCbCanonicalChallenge :: OutputFormat -> [String] -> IO ()
cmdCbCanonicalChallenge format [mStr, n2Str, qStr, betaStr, ckStr, cStr, aStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ckStr, parseVec cStr, parseVec aStr) of
        (Just params, Just ck, Just c, Just a) ->
            outputIntResult format "canonical_balance_challenge = "
                (ConfidentialBalance.canonicalBalanceChallenge params ck c a)
        _ -> outputError format "Expected params (M N2 Q BETA), commitment key matrix, commitment vector, and announcement vector"
cmdCbCanonicalChallenge format _ =
    outputUsage format "Usage: cb-canonical-challenge M N2 Q BETA \"[[row1],[row2]]\" \"[c]\" \"[a]\""

cmdCbSigmaCommit :: OutputFormat -> [String] -> IO ()
cmdCbSigmaCommit format [mStr, n2Str, qStr, betaStr, ckStr, yStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ckStr, parseVec yStr) of
        (Just params, Just ck, Just y) ->
            outputVecResult format "balance_sigma_commit = "
                (ConfidentialBalance.balanceSigmaCommit params ck y)
        _ -> outputError format "Expected params (M N2 Q BETA), commitment key matrix, and mask vector"
cmdCbSigmaCommit format _ =
    outputUsage format "Usage: cb-sigma-commit M N2 Q BETA \"[[row1],[row2]]\" \"[y]\""

cmdCbSigmaRespond :: OutputFormat -> [String] -> IO ()
cmdCbSigmaRespond format [rStr, yStr, challengeStr] =
    case (parseVec rStr, parseVec yStr, parseInt challengeStr) of
        (Just r, Just y, Just challenge) ->
            outputVecResult format "balance_sigma_respond = "
                (ConfidentialBalance.balanceSigmaRespond r y challenge)
        _ -> outputError format "Expected witness vector, mask vector, and integer challenge"
cmdCbSigmaRespond format _ =
    outputUsage format "Usage: cb-sigma-respond \"[r]\" \"[y]\" CHALLENGE"

cmdCbSigmaVerify :: OutputFormat -> [String] -> IO ()
cmdCbSigmaVerify format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, cStr, aStr, challengeStr, zStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseMat ckStr
        , parseVec cStr
        , parseVec aStr
        , parseInt challengeStr
        , parseVec zStr
        ) of
        (Just params, Just gamma, Just ck, Just c, Just a, Just challenge, Just z) ->
            outputBoolResult format "balance_sigma_verify = "
                (ConfidentialBalance.balanceSigmaVerify params gamma ck c a challenge z)
        _ -> outputError format "Expected params, gamma, commitment key matrix, commitment vector, announcement vector, integer challenge, and response vector"
cmdCbSigmaVerify format _ =
    outputUsage format "Usage: cb-sigma-verify M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[a]\" CHALLENGE \"[z]\""

cmdCbProve :: OutputFormat -> [String] -> IO ()
cmdCbProve format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, cStr, rStr, ysStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseMat ckStr
        , parseVec cStr
        , parseVec rStr
        , parseMat ysStr
        ) of
        (Just params, Just gamma, Just ck, Just c, Just r, Just ys) ->
            case ConfidentialBalance.balanceFsProve params gamma ck c r ys of
                Just proof ->
                    case format of
                        Human -> putStrLn $ "balance_fs_proof = " ++ show proof
                        Json -> putStrLn $ jsonCbProof proof
                Nothing ->
                    case format of
                        Human -> putStrLn "balance_fs_proof = null"
                        Json -> putStrLn "null"
        _ -> outputError format "Expected params, gamma, commitment key matrix, commitment vector, witness vector, and a matrix of mask vectors"
cmdCbProve format _ =
    outputUsage format "Usage: cb-prove M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[r]\" \"[[y1],[y2],...]\""

cmdCbVerify :: OutputFormat -> [String] -> IO ()
cmdCbVerify format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, cStr, asStr, zsStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseMat ckStr
        , parseVec cStr
        , parseMat asStr
        , parseMat zsStr
        ) of
        (Just params, Just gamma, Just ck, Just c, Just as, Just zs) ->
            outputBoolResult format "balance_fs_verify = "
                (ConfidentialBalance.balanceFsVerify params gamma ck c (ConfidentialBalance.makeBalanceProof as zs))
        _ -> outputError format "Expected params, gamma, commitment key matrix, commitment vector, announcement matrix, and response matrix"
cmdCbVerify format _ =
    outputUsage format "Usage: cb-verify M N2 Q BETA GAMMA \"[[row1],[row2]]\" \"[c]\" \"[[a1],[a2],...]\" \"[[z1],[z2],...]\""

cmdCrAmountCommitment :: OutputFormat -> [String] -> IO ()
cmdCrAmountCommitment format [mStr, n2Str, qStr, betaStr, ckStr, cAmountStr, cBitsStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ckStr, parseVec cAmountStr, parseMat cBitsStr) of
        (Just params, Just ck, Just cAmount, Just cBits) ->
            outputVecResult format "range_amount_commitment = "
                (ConfidentialRange.rangeAmountCommitment params ck cAmount cBits)
        _ -> outputError format "Expected params, commitment key, amount commitment, and bit commitments"
cmdCrAmountCommitment format _ =
    outputUsage format "Usage: cr-amount-commitment M N2 Q BETA \"[[row1],[row2]]\" \"[cAmount]\" \"[[cBit1],[cBit2]]\""

cmdCrProve :: OutputFormat -> [String] -> IO ()
cmdCrProve format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, cAmountStr, amountStr, amountRandStr, bitsStr, bitRandsStr, compsStr, compRandsStr, yAmountsStr, yPairssStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseInt kStr
        , parseMat ckStr
        , parseVec cAmountStr
        , parseInt amountStr
        , parseVec amountRandStr
        , parseVec bitsStr
        , parseMat bitRandsStr
        , parseVec compsStr
        , parseMat compRandsStr
        , parseMat yAmountsStr
        , parseCube yPairssStr
        ) of
        (Just params, Just gamma, Just k, Just ck, Just cAmount, Just amount, Just amountRand, Just bits, Just bitRands, Just comps, Just compRands, Just yAmounts, Just yPairss) ->
            case (makeScalarOpenings bits bitRands, makeScalarOpenings comps compRands) of
                (Just bitOps, Just compOps) ->
                    case ConfidentialRange.rangeFsProve params gamma k ck cAmount (makeScalarOpening amount amountRand) bitOps compOps yAmounts yPairss of
                        Just proof ->
                            case format of
                                Human -> putStrLn $ "range_fs_proof = " ++ show proof
                                Json -> putStrLn $ jsonCrProof proof
                        Nothing ->
                            case format of
                                Human -> putStrLn "range_fs_proof = null"
                                Json -> putStrLn "null"
                _ -> outputError format "Bit/value and randomness matrix lengths must match"
        _ -> outputError format "Expected params, gamma, commitment key, amount commitment, scalar opening, bit openings, complement openings, and masks"
cmdCrProve format _ =
    outputUsage format "Usage: cr-prove M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" AMOUNT \"[amountRand]\" \"[bits]\" \"[[bitRands]]\" \"[comps]\" \"[[compRands]]\" \"[[yAmounts]]\" \"[[[yPairss]]]\""

cmdCrVerify :: OutputFormat -> [String] -> IO ()
cmdCrVerify format args =
    case prepareCrVerify args of
        Right verify -> outputBoolResult format "range_fs_verify = " (verify ())
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCrVerifyBench :: OutputFormat -> [String] -> IO ()
cmdCrVerifyBench format (iterationsStr:warmupStr:rest) =
    case (parseInt iterationsStr, parseInt warmupStr) of
        (Just iterations, Just warmup)
            | iterations > 0 && warmup >= 0 ->
                case prepareCrVerify rest of
                    Right verify ->
                        benchmarkBool warmup iterations verify >>= outputBenchStats format "range_fs_verify_bench"
                    Left err
                        | take 5 err == "Usage" -> outputUsage format ("Usage: cr-verify-bench ITERATIONS WARMUP " ++ drop 6 err)
                        | otherwise -> outputError format err
        _ -> outputError format "Expected positive ITERATIONS and non-negative WARMUP"
cmdCrVerifyBench format _ =
    outputUsage format "Usage: cr-verify-bench ITERATIONS WARMUP M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

cmdCtNullifier :: OutputFormat -> [String] -> IO ()
cmdCtNullifier format [mStr, n2Str, qStr, betaStr, nkStr, amountStr, randStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat nkStr, parseInt amountStr, parseVec randStr) of
        (Just params, Just nk, Just amount, Just randVec) ->
            outputVecResult format "nullifier = "
                (ConfidentialTransaction.nullifier params nk (makeScalarOpening amount randVec))
        _ -> outputError format "Expected params, nullifier key, scalar amount, and randomness vector"
cmdCtNullifier format _ =
    outputUsage format "Usage: ct-nullifier M N2 Q BETA \"[[nk]]\" AMOUNT \"[rand]\""

cmdCtNullifierCanonicalChallenge :: OutputFormat -> [String] -> IO ()
cmdCtNullifierCanonicalChallenge format [mStr, n2Str, qStr, betaStr, ckStr, nkStr, cStr, nfStr, aCommitStr, aNullifierStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseMat ckStr
        , parseMat nkStr
        , parseVec cStr
        , parseVec nfStr
        , parseVec aCommitStr
        , parseVec aNullifierStr
        ) of
        (Just params, Just ck, Just nk, Just c, Just nf, Just aCommit, Just aNullifier) ->
            outputIntResult format "canonical_nullifier_challenge = "
                (ConfidentialTransaction.canonicalNullifierChallenge params ck nk c nf aCommit aNullifier)
        _ -> outputError format "Expected params, keys, commitment, nullifier, commitment announcement, and nullifier announcement"
cmdCtNullifierCanonicalChallenge format _ =
    outputUsage format "Usage: ct-nullifier-canonical-challenge M N2 Q BETA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[aCommit]\" \"[aNullifier]\""

cmdCtNullifierProve :: OutputFormat -> [String] -> IO ()
cmdCtNullifierProve format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, nkStr, cStr, nfStr, amountStr, randStr, yMsgsStr, yRandsStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseMat ckStr
        , parseMat nkStr
        , parseVec cStr
        , parseVec nfStr
        , parseInt amountStr
        , parseVec randStr
        , parseVec yMsgsStr
        , parseMat yRandsStr
        ) of
        (Just params, Just gamma, Just ck, Just nk, Just c, Just nf, Just amount, Just randVec, Just yMsgs, Just yRands) ->
            case makeScalarOpenings yMsgs yRands of
                Just ys ->
                    case ConfidentialTransaction.nullifierFsProve
                            params gamma ck nk c nf
                            (makeScalarOpening amount randVec)
                            ys of
                        Just proof ->
                            case format of
                                Human -> putStrLn $ "nullifier_fs_proof = " ++ show proof
                                Json -> putStrLn $ jsonCtNullifierProof proof
                        Nothing ->
                            case format of
                                Human -> putStrLn "nullifier_fs_proof = null"
                                Json -> putStrLn "null"
                Nothing -> outputError format "Mask message and randomness counts must match"
        _ -> outputError format "Expected params, gamma, keys, commitments, witness opening, and mask opening"
cmdCtNullifierProve format _ =
    outputUsage format "Usage: ct-nullifier-prove M N2 Q BETA G \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" AMOUNT \"[rand]\" \"[yMsgs]\" \"[[yRands]]\""

cmdCtNullifierVerify :: OutputFormat -> [String] -> IO ()
cmdCtNullifierVerify format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, nkStr, cStr, nfStr, aCommitsStr, aNullifiersStr, zMsgsStr, zRandsStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseMat ckStr
        , parseMat nkStr
        , parseVec cStr
        , parseVec nfStr
        , parseMat aCommitsStr
        , parseMat aNullifiersStr
        , parseMat zMsgsStr
        , parseMat zRandsStr
        ) of
        (Just params, Just gamma, Just ck, Just nk, Just c, Just nf, Just aCommits, Just aNullifiers, Just zMsgs, Just zRands) ->
            outputBoolResult format "nullifier_fs_verify = "
                (ConfidentialTransaction.nullifierFsVerify
                    params gamma ck nk c nf
                    (ConfidentialTransaction.makeNullifierProof aCommits aNullifiers zMsgs zRands))
        _ -> outputError format "Expected params, gamma, keys, commitments, and nullifier-proof fields"
cmdCtNullifierVerify format _ =
    outputUsage format "Usage: ct-nullifier-verify M N2 Q BETA G \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" \"[[zMsgs]]\" \"[[zRands]]\""

cmdCtMemberProve :: OutputFormat -> [String] -> IO ()
cmdCtMemberProve format [mStr, n2Str, qStr, betaStr, ledgerStr, cStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ledgerStr, parseVec cStr) of
        (Just params, Just ledger, Just c) ->
            case ConfidentialTransaction.membershipProve params ledger c of
                Just proof ->
                    case format of
                        Human -> putStrLn $ "membership_proof = " ++ show proof
                        Json -> putStrLn $ jsonCtMembershipProof proof
                Nothing ->
                    case format of
                        Human -> putStrLn "membership_proof = null"
                        Json -> putStrLn "null"
        _ -> outputError format "Expected params, a ledger matrix, and a commitment vector"
cmdCtMemberProve format _ =
    outputUsage format "Usage: ct-member-prove M N2 Q BETA \"[[c1],[c2],...]\" \"[c]\""

cmdCtMemberVerify :: OutputFormat -> [String] -> IO ()
cmdCtMemberVerify format [mStr, n2Str, qStr, betaStr, ledgerStr, cStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat ledgerStr, parseVec cStr) of
        (Just params, Just ledger, Just c) ->
            outputBoolResult format "membership_verify = "
                (case ConfidentialTransaction.membershipProve params ledger c of
                    Just proof -> ConfidentialTransaction.membershipVerify params c proof
                    Nothing -> False)
        _ -> outputError format "Expected params, a ledger matrix, and a commitment vector"
cmdCtMemberVerify format _ =
    outputUsage format "Usage: ct-member-verify M N2 Q BETA \"[[c1],[c2],...]\" \"[c]\""

cmdCtLedgerStepVerify :: OutputFormat -> [String] -> IO ()
cmdCtLedgerStepVerify format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, noteCommitmentsStr, noteBitsStr, noteCompsStr, noteAmountAsStr, noteAmountZsStr, notePairAsStr, notePairZsStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1ACommitsStr, in1ANullifiersStr, in1ZMsgsStr, in1ZRandsStr, in2ACommitsStr, in2ANullifiersStr, in2ZMsgsStr, in2ZRandsStr, balanceAStr, balanceZsStr, out1BitsStr, out1CompsStr, out1AmountAStr, out1AmountZStr, out1PairAsStr, out1PairZsStr, out2BitsStr, out2CompsStr, out2AmountAStr, out2AmountZStr, out2PairAsStr, out2PairZsStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseInt kStr
        , parseMat ckStr
        , parseMat nkStr
        , parseMat noteCommitmentsStr
        , parseCube noteBitsStr
        , parseCube noteCompsStr
        , parseCube noteAmountAsStr
        , parseCube noteAmountZsStr
        , parse4D notePairAsStr
        , parse4D notePairZsStr
        , parseMat spentStr
        , parseVec cIn1Str
        , parseVec cIn2Str
        , parseVec cOut1Str
        , parseVec cOut2Str
        , parseVec nf1Str
        , parseVec nf2Str
        , parseMat in1ACommitsStr
        , parseMat in1ANullifiersStr
        , parseMat in1ZMsgsStr
        , parseMat in1ZRandsStr
        , parseMat in2ACommitsStr
        , parseMat in2ANullifiersStr
        , parseMat in2ZMsgsStr
        , parseMat in2ZRandsStr
        , parseMat balanceAStr
        , parseMat balanceZsStr
        , parseMat out1BitsStr
        , parseMat out1CompsStr
        , parseMat out1AmountAStr
        , parseMat out1AmountZStr
        , parseCube out1PairAsStr
        , parseCube out1PairZsStr
        , parseMat out2BitsStr
        , parseMat out2CompsStr
        , parseMat out2AmountAStr
        , parseMat out2AmountZStr
        , parseCube out2PairAsStr
        , parseCube out2PairZsStr
        ) of
        (Just params, Just gamma, Just k, Just ck, Just nk, Just noteCommitments, Just noteBits, Just noteComps, Just noteAmountAs, Just noteAmountZs, Just notePairAs, Just notePairZs, Just spent, Just cIn1, Just cIn2, Just cOut1, Just cOut2, Just nf1, Just nf2, Just in1ACommits, Just in1ANullifiers, Just in1ZMsgs, Just in1ZRands, Just in2ACommits, Just in2ANullifiers, Just in2ZMsgs, Just in2ZRands, Just balanceAs, Just balanceZs, Just out1Bits, Just out1Comps, Just out1AmountA, Just out1AmountZ, Just out1PairAs, Just out1PairZs, Just out2Bits, Just out2Comps, Just out2AmountA, Just out2AmountZ, Just out2PairAs, Just out2PairZs) ->
            case ( makeVerifiedNotes noteCommitments noteBits noteComps noteAmountAs noteAmountZs notePairAs notePairZs
                 , ConfidentialTransaction.membershipProve params noteCommitments cIn1
                 , ConfidentialTransaction.membershipProve params noteCommitments cIn2
                 ) of
                (Just notes, Just in1Member, Just in2Member) ->
                    let proof =
                            ConfidentialTransaction.makeTransactionProof
                                in1Member
                                in2Member
                                (ConfidentialTransaction.makeNullifierProof in1ACommits in1ANullifiers in1ZMsgs in1ZRands)
                                (ConfidentialTransaction.makeNullifierProof in2ACommits in2ANullifiers in2ZMsgs in2ZRands)
                                (ConfidentialBalance.makeBalanceProof balanceAs balanceZs)
                                (ConfidentialRange.makeRangeProof out1Bits out1Comps out1AmountA out1AmountZ out1PairAs out1PairZs)
                                (ConfidentialRange.makeRangeProof out2Bits out2Comps out2AmountA out2AmountZ out2PairAs out2PairZs)
                     in outputBoolResult format "ledger_step_valid = "
                            (ConfidentialTransaction.ledgerStepValid
                                params gamma k ck nk notes spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof)
                _ -> outputError format "Expected consistent verified-note inputs and membership proofs for both input commitments"
        _ -> outputError format "Expected params, keys, verified-note ledger fields, nullifiers, and transaction-proof fields"
cmdCtLedgerStepVerify format _ =
    outputUsage format "Usage: ct-ledger-step-verify M N2 Q BETA G K CK NK NOTE_COMMITMENTS NOTE_BITS NOTE_COMPS NOTE_AMOUNT_AS NOTE_AMOUNT_ZS NOTE_PAIR_AS NOTE_PAIR_ZS SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_A OUT1_AMOUNT_Z OUT1_PAIR_AS OUT1_PAIR_ZS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_A OUT2_AMOUNT_Z OUT2_PAIR_AS OUT2_PAIR_ZS"

cmdCtProve :: OutputFormat -> [String] -> IO ()
cmdCtProve format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, ledgerStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1AmountStr, in1RandStr, in2AmountStr, in2RandStr, out1AmountStr, out1RandStr, out2AmountStr, out2RandStr, out1BitsStr, out1BitRandsStr, out1CompsStr, out1CompRandsStr, out2BitsStr, out2BitRandsStr, out2CompsStr, out2CompRandsStr, yIn1MsgsStr, yIn1RandsStr, yIn2MsgsStr, yIn2RandsStr, yBalanceStr, yOut1AmountsStr, yOut1PairssStr, yOut2AmountsStr, yOut2PairssStr] =
    case
        ( parseCbParams mStr n2Str qStr betaStr
        , parseInt gammaStr
        , parseInt kStr
        , parseMat ckStr
        , parseMat nkStr
        , parseMat ledgerStr
        , parseMat spentStr
        , parseVec cIn1Str
        , parseVec cIn2Str
        , parseVec cOut1Str
        , parseVec cOut2Str
        , parseVec nf1Str
        , parseVec nf2Str
        , parseInt in1AmountStr
        , parseVec in1RandStr
        , parseInt in2AmountStr
        , parseVec in2RandStr
        , parseInt out1AmountStr
        , parseVec out1RandStr
        , parseInt out2AmountStr
        , parseVec out2RandStr
        , parseVec out1BitsStr
        , parseMat out1BitRandsStr
        , parseVec out1CompsStr
        , parseMat out1CompRandsStr
        , parseVec out2BitsStr
        , parseMat out2BitRandsStr
        , parseVec out2CompsStr
        , parseMat out2CompRandsStr
        , parseVec yIn1MsgsStr
        , parseMat yIn1RandsStr
        , parseVec yIn2MsgsStr
        , parseMat yIn2RandsStr
        , parseMat yBalanceStr
        , parseMat yOut1AmountsStr
        , parseCube yOut1PairssStr
        , parseMat yOut2AmountsStr
        , parseCube yOut2PairssStr
        ) of
        (Just params, Just gamma, Just k, Just ck, Just nk, Just ledger, Just spent, Just cIn1, Just cIn2, Just cOut1, Just cOut2, Just nf1, Just nf2, Just in1Amount, Just in1Rand, Just in2Amount, Just in2Rand, Just out1Amount, Just out1Rand, Just out2Amount, Just out2Rand, Just out1Bits, Just out1BitRands, Just out1Comps, Just out1CompRands, Just out2Bits, Just out2BitRands, Just out2Comps, Just out2CompRands, Just yIn1Msgs, Just yIn1Rands, Just yIn2Msgs, Just yIn2Rands, Just yBalance, Just yOut1Amounts, Just yOut1Pairss, Just yOut2Amounts, Just yOut2Pairss) ->
            case ( makeScalarOpenings out1Bits out1BitRands
                 , makeScalarOpenings out1Comps out1CompRands
                 , makeScalarOpenings out2Bits out2BitRands
                 , makeScalarOpenings out2Comps out2CompRands
                 , makeScalarOpenings yIn1Msgs yIn1Rands
                 , makeScalarOpenings yIn2Msgs yIn2Rands
                 ) of
                (Just out1BitOps, Just out1CompOps, Just out2BitOps, Just out2CompOps, Just yIn1Ops, Just yIn2Ops) ->
                    case ConfidentialTransaction.transactionFsProve
                            params gamma k ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2
                            (makeScalarOpening in1Amount in1Rand)
                            (makeScalarOpening in2Amount in2Rand)
                            (makeScalarOpening out1Amount out1Rand)
                            (makeScalarOpening out2Amount out2Rand)
                            out1BitOps out1CompOps out2BitOps out2CompOps
                            yIn1Ops
                            yIn2Ops
                            yBalance
                            yOut1Amounts
                            yOut1Pairss
                            yOut2Amounts
                            yOut2Pairss of
                        Just proof ->
                            case format of
                                Human -> putStrLn $ "transaction_fs_proof = " ++ show proof
                                Json -> putStrLn $ jsonCtTransactionProof proof
                        Nothing ->
                            case format of
                                Human -> putStrLn "transaction_fs_proof = null"
                                Json -> putStrLn "null"
                _ -> outputError format "Bit/complement counts must match their randomness matrices"
        _ -> outputError format "Expected params, keys, ledger, commitments, openings, bit decompositions, and mask vectors"
cmdCtProve format _ =
    outputUsage format "Usage: ct-prove M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS"

cmdCtVerify :: OutputFormat -> [String] -> IO ()
cmdCtVerify format args =
    case prepareCtVerify args of
        Right verify -> outputBoolResult format "transaction_fs_verify = " (verify ())
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCtVerifyBench :: OutputFormat -> [String] -> IO ()
cmdCtVerifyBench format (iterationsStr:warmupStr:rest) =
    case (parseInt iterationsStr, parseInt warmupStr) of
        (Just iterations, Just warmup)
            | iterations > 0 && warmup >= 0 ->
                case prepareCtVerify rest of
                    Right verify ->
                        benchmarkBool warmup iterations verify >>= outputBenchStats format "transaction_fs_verify_bench"
                    Left err
                        | take 5 err == "Usage" -> outputUsage format ("Usage: ct-verify-bench ITERATIONS WARMUP " ++ drop 6 err)
                        | otherwise -> outputError format err
        _ -> outputError format "Expected positive ITERATIONS and non-negative WARMUP"
cmdCtVerifyBench format _ =
    outputUsage format "Usage: ct-verify-bench ITERATIONS WARMUP M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"
