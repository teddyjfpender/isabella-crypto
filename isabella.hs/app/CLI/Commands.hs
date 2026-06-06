-- | CLI command handlers
module CLI.Commands (OutputFormat(..), runCommand) where

import Control.Exception (SomeException, catch, evaluate)
import Control.Monad (replicateM, replicateM_)
import qualified Canon.Commit_sis as Commit
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_merkle as ConfidentialMerkle
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Confidential_sampling as ConfidentialSampling
import qualified Canon.Confidential_transaction as ConfidentialTransaction
import qualified Canon.Dilithium as Dilithium
import qualified Canon.Listvec as Listvec
import qualified Canon.ZK.Internal.RepeatedFS as RepeatedFS
import qualified Canon.Zq as Zq
import Data.Bits ((.&.))
import Data.Char (ord)
import Data.List (findIndex, intercalate, sort, zip4)
import Data.Word (Word8)
import GHC.Clock (getMonotonicTimeNSec)
import System.Environment (lookupEnv)
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
    "cb-sample-mask" -> cmdCbSampleMask format args
    "cb-sample-masks" -> cmdCbSampleMasks format args
    "cb-valid-response" -> cmdCbValidResponse format args
    "cb-balance-commitment" -> cmdCbBalanceCommitment format args
    "cb-canonical-challenge" -> cmdCbCanonicalChallenge format args
    "cb-sigma-commit" -> cmdCbSigmaCommit format args
    "cb-sigma-respond" -> cmdCbSigmaRespond format args
    "cb-sigma-verify" -> cmdCbSigmaVerify format args
    "cb-prove" -> cmdCbProve format args
    "cb-verify" -> cmdCbVerify format args
    "ct-balance-bigint-rand-commit" -> cmdCtBalanceBigintRandCommit format args
    "ct-balance-bigint-fs-fields" -> cmdCtBalanceBigintFsFields format args
    "ct-balance-bigint-fs-challenges" -> cmdCtBalanceBigintFsChallenges format args
    "ct-balance-bigint-prove" -> cmdCtBalanceBigintProve format args
    "ct-balance-bigint-verify" -> cmdCtBalanceBigintVerify format args
    "ct-range-bigint-fs-fields" -> cmdCtRangeBigintFsFields format args
    "ct-range-bigint-fs-challenges" -> cmdCtRangeBigintFsChallenges format args
    "ct-range-bigint-prove" -> cmdCtRangeBigintProve format args
    "ct-range-bigint-verify" -> cmdCtRangeBigintVerify format args
    "ct-nullifier-bigint" -> cmdCtNullifierBigint format args
    "ct-nullifier-bigint-fs-fields" -> cmdCtNullifierBigintFsFields format args
    "ct-nullifier-bigint-fs-challenges" -> cmdCtNullifierBigintFsChallenges format args
    "ct-nullifier-bigint-prove" -> cmdCtNullifierBigintProve format args
    "ct-nullifier-bigint-verify" -> cmdCtNullifierBigintVerify format args
    "cr-amount-commitment" -> cmdCrAmountCommitment format args
    "cr-prove" -> cmdCrProve format args
    "cr-verify" -> cmdCrVerify format args
    "cr-verify-bench" -> cmdCrVerifyBench format args
    "ct-merkle-leaf" -> cmdCtMerkleLeaf format args
    "ct-merkle-empty" -> cmdCtMerkleEmpty format args
    "ct-merkle-node" -> cmdCtMerkleNode format args
    "ct-merkle-root" -> cmdCtMerkleRoot format args
    "ct-merkle-member-prove" -> cmdCtMerkleMemberProve format args
    "ct-merkle-member-verify" -> cmdCtMerkleMemberVerify format args
    "ct-bignum-encode" -> cmdCtBignumEncode format args
    "ct-bignum-vector-encode" -> cmdCtBignumVectorEncode format args
    "ct-bignum-merkle-leaf" -> cmdCtBignumMerkleLeaf format args
    "ct-bignum-merkle-empty" -> cmdCtBignumMerkleEmpty format args
    "ct-bignum-merkle-node" -> cmdCtBignumMerkleNode format args
    "ct-bignum-merkle-root" -> cmdCtBignumMerkleRoot format args
    "ct-bignum-merkle-member-prove" -> cmdCtBignumMerkleMemberProve format args
    "ct-bignum-merkle-member-verify" -> cmdCtBignumMerkleMemberVerify format args
    "ct-bignum-transaction-context" -> cmdCtBignumTransactionContext format args
    "ct-bignum-merkle-proof-digest" -> cmdCtBignumMerkleProofDigest format args
    "ct-bignum-merkle-envelope-digest" -> cmdCtBignumMerkleEnvelopeDigest format args
    "ct-bignum-verify-merkle-envelope" -> cmdCtBignumVerifyMerkleEnvelope format args
    "ct-bignum-wallet-proof-request-digest" -> cmdCtBignumWalletProofRequestDigest format args
    "ct-bignum-accepted-root-window-digest" -> cmdCtBignumAcceptedRootWindowDigest format args
    "ct-transaction-context" -> cmdCtTransactionContext format args
    "ct-merkle-proof-digest" -> cmdCtMerkleProofDigest format args
    "ct-merkle-envelope-digest" -> cmdCtMerkleEnvelopeDigest format args
    "ct-wallet-proof-request-digest" -> cmdCtWalletProofRequestDigest format args
    "ct-accepted-root-window-digest" -> cmdCtAcceptedRootWindowDigest format args
    "ct-sample-opening" -> cmdCtSampleOpening format args
    "ct-sample-openings" -> cmdCtSampleOpenings format args
    "ct-nullifier" -> cmdCtNullifier format args
    "ct-sample-nullifier-mask" -> cmdCtSampleNullifierMask format args
    "ct-sample-nullifier-masks" -> cmdCtSampleNullifierMasks format args
    "ct-nullifier-canonical-challenge" -> cmdCtNullifierCanonicalChallenge format args
    "ct-nullifier-prove" -> cmdCtNullifierProve format args
    "ct-nullifier-verify" -> cmdCtNullifierVerify format args
    "ct-member-prove" -> cmdCtMemberProve format args
    "ct-member-verify" -> cmdCtMemberVerify format args
    "ct-ledger-step-verify-scaffold" -> runScaffoldCompat format (cmdCtLedgerStepVerifyScaffold format args)
    "ct-prove-scaffold" -> runScaffoldCompat format (cmdCtProveScaffold format args)
    "ct-prove-merkle" -> cmdCtProveMerkle format args
    "ct-verify-scaffold" -> runScaffoldCompat format (cmdCtVerifyScaffold format args)
    "ct-verify-merkle" -> cmdCtVerifyMerkle format args
    "ct-verify-merkle-envelope" -> cmdCtVerifyMerkleEnvelope format args
    "ct-verify-bench-scaffold" -> runScaffoldCompat format (cmdCtVerifyBenchScaffold format args)
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

parseCanonicalRead :: (Eq a, Read a, Show a) => String -> Maybe a
parseCanonicalRead s = do
    value <- readMaybe s
    if show value == s then Just value else Nothing

maxSafeProtocolInt :: Int
maxSafeProtocolInt = 9007199254740991

safeProtocolInt :: Int -> Bool
safeProtocolInt value =
    value >= negate maxSafeProtocolInt && value <= maxSafeProtocolInt

parseCanonicalInt :: String -> Maybe Int
parseCanonicalInt s = do
    value <- parseCanonicalRead s
    if safeProtocolInt value then Just value else Nothing

parseCanonicalInteger :: String -> Maybe Integer
parseCanonicalInteger s = do
    value <- readMaybe s
    if show (value :: Integer) == s then Just value else Nothing

parseCanonicalIntegerVec :: String -> Maybe [Integer]
parseCanonicalIntegerVec = parseCanonicalRead

parseCanonicalIntegerMat :: String -> Maybe [[Integer]]
parseCanonicalIntegerMat = parseCanonicalRead

parseCanonicalIntegerCube :: String -> Maybe [[[Integer]]]
parseCanonicalIntegerCube = parseCanonicalRead

parseCanonicalVec :: String -> Maybe [Int]
parseCanonicalVec s = do
    value <- parseCanonicalRead s
    if all safeProtocolInt value then Just value else Nothing

parseCanonicalMat :: String -> Maybe [[Int]]
parseCanonicalMat s = do
    value <- parseCanonicalRead s
    if all (all safeProtocolInt) value then Just value else Nothing

parseCanonicalCube :: String -> Maybe [[[Int]]]
parseCanonicalCube s = do
    value <- parseCanonicalRead s
    if all (all (all safeProtocolInt)) value then Just value else Nothing

parseBool :: String -> Maybe Bool
parseBool "0" = Just False
parseBool "1" = Just True
parseBool "false" = Just False
parseBool "true" = Just True
parseBool "False" = Just False
parseBool "True" = Just True
parseBool _ = Nothing

parseBoolVec01 :: String -> Maybe [Bool]
parseBoolVec01 s =
    parseVec s >>= traverse toBool
  where
    toBool 0 = Just False
    toBool 1 = Just True
    toBool _ = Nothing

parseCanonicalBoolVec01 :: String -> Maybe [Bool]
parseCanonicalBoolVec01 s =
    parseCanonicalVec s >>= traverse toBool
  where
    toBool 0 = Just False
    toBool 1 = Just True
    toBool _ = Nothing

bignumHexByte :: Int -> String
bignumHexByte byte =
    let alphabet = "0123456789abcdef"
        hi = (byte `div` 16) `mod` 16
        lo = byte `mod` 16
     in [alphabet !! hi, alphabet !! lo]

bignumMagnitudeLeBytes :: Integer -> [Int]
bignumMagnitudeLeBytes 0 = []
bignumMagnitudeLeBytes value =
    fromInteger (value `mod` 256) : bignumMagnitudeLeBytes (value `div` 256)

bignumLengthLeBytes :: Int -> [Int]
bignumLengthLeBytes value =
    [ (value `div` (256 ^ i)) `mod` 256
    | i <- [0 :: Int .. 7]
    ]

encodeBignumInteger :: Integer -> [Int]
encodeBignumInteger value =
    let negative = value < 0
        magnitude = bignumMagnitudeLeBytes (abs value)
        sign = if negative then 1 else 0
     in sign : bignumLengthLeBytes (length magnitude) ++ magnitude

encodeBignumIntegerVector :: [Integer] -> [Int]
encodeBignumIntegerVector values =
    bignumLengthLeBytes (length values) ++ concatMap encodeBignumInteger values

bignumMerkleDst :: String
bignumMerkleDst = "ISABELLA-CT-MERKLE-BIGNUM-v1"

bignumTransactionDst :: String
bignumTransactionDst = "ISABELLA-CT-TX-BIGNUM-v1"

sisNoteProtocolId :: String
sisNoteProtocolId = "ISABELLA-CT-SIS-NOTE"

transactionInt64LeBytes :: Int -> [Word8]
transactionInt64LeBytes value =
    [ fromIntegral ((asInteger `div` (256 ^ i)) `mod` 256)
    | i <- [0 :: Int .. 7]
    ]
  where
    asInteger = toInteger value

transactionHexByte :: Word8 -> String
transactionHexByte byte =
    let alphabet = "0123456789abcdef"
        value = fromIntegral byte :: Int
        hi = (value `div` 16) `mod` 16
        lo = value `mod` 16
     in [alphabet !! hi, alphabet !! lo]

transactionDigestHex :: [Word8] -> String
transactionDigestHex = concatMap transactionHexByte

transactionHexValue :: Char -> Maybe Word8
transactionHexValue c
    | c >= '0' && c <= '9' = Just (fromIntegral (ord c - ord '0'))
    | c >= 'a' && c <= 'f' = Just (fromIntegral (10 + ord c - ord 'a'))
    | otherwise = Nothing

transactionHexToBytes :: String -> Maybe [Word8]
transactionHexToBytes hex
    | length hex /= 64 = Nothing
    | otherwise = go hex
  where
    go [] = Just []
    go (hi:lo:rest) = do
        hiValue <- transactionHexValue hi
        loValue <- transactionHexValue lo
        tailBytes <- go rest
        pure ((hiValue * 16 + loValue) : tailBytes)
    go _ = Nothing

encodeTransactionAscii :: String -> String -> [Word8]
encodeTransactionAscii label value =
    let bytes = map ord value
        validByte index byte =
          if byte >= 0x20 && byte <= 0x7e
            then fromIntegral byte
            else error (label ++ "[" ++ show index ++ "] must be printable ASCII")
     in transactionInt64LeBytes (length bytes) ++ zipWith validByte [0 :: Int ..] bytes

encodeTransactionDigest :: String -> String -> [Word8]
encodeTransactionDigest label digest =
    case transactionHexToBytes digest of
      Just bytes -> transactionInt64LeBytes (length bytes) ++ bytes
      Nothing -> error (label ++ " must be a canonical lowercase SHA3-256 digest")

encodeTransactionDigestVector :: String -> [String] -> [Word8]
encodeTransactionDigestVector label digests =
    transactionInt64LeBytes (length digests) ++
    concat
      [ encodeTransactionDigest (label ++ "[" ++ show index ++ "]") digest
      | (index, digest) <- zip [0 :: Int ..] digests
      ]

encodeTransactionBoolVec :: [Bool] -> [Word8]
encodeTransactionBoolVec values =
    transactionInt64LeBytes (length values) ++
    concatMap (transactionInt64LeBytes . boolInt) values
  where
    boolInt True = 1
    boolInt False = 0

encodeTransactionAcceptedRoot :: String -> (String, Int) -> [Word8]
encodeTransactionAcceptedRoot label (digest, depth) =
    encodeTransactionDigest (label ++ ".digest") digest ++
    encodeNonNegativeI64 (label ++ ".depth") depth

encodeTransactionAcceptedRootVector :: String -> [(String, Int)] -> [Word8]
encodeTransactionAcceptedRootVector label roots =
    transactionInt64LeBytes (length roots) ++
    concat
      [ encodeTransactionAcceptedRoot (label ++ "[" ++ show index ++ "]") root
      | (index, root) <- zip [0 :: Int ..] roots
      ]

encodeTransactionAcceptedRootWindowEntry :: String -> (String, Int, Int, Int) -> [Word8]
encodeTransactionAcceptedRootWindowEntry label (digest, depth, validFromEpoch, expiresAtEpoch)
    | expiresAtEpoch <= validFromEpoch =
        error (label ++ ".expiresAtEpoch must be greater than validFromEpoch")
    | otherwise =
        encodeTransactionAcceptedRoot (label ++ ".root") (digest, depth) ++
        encodeNonNegativeI64 (label ++ ".validFromEpoch") validFromEpoch ++
        encodeNonNegativeI64 (label ++ ".expiresAtEpoch") expiresAtEpoch

encodeTransactionAcceptedRootWindowEntryVector :: String -> [(String, Int, Int, Int)] -> [Word8]
encodeTransactionAcceptedRootWindowEntryVector label entries =
    transactionInt64LeBytes (length entries) ++
    concat
      [ encodeTransactionAcceptedRootWindowEntry (label ++ "[" ++ show index ++ "]") entry
      | (index, entry) <- zip [0 :: Int ..] entries
      ]

requireSortedUnique :: Ord a => String -> [a] -> ()
requireSortedUnique label values
    | any (uncurry (>=)) (zip values (drop 1 values)) =
        error (label ++ " must be sorted with no duplicates")
    | otherwise = ()

requireCanonicalAcceptedRootSet :: String -> [(String, Int)] -> ()
requireCanonicalAcceptedRootSet label roots
    | null roots = error (label ++ " must not be empty")
    | otherwise =
        let encoded = encodeTransactionAcceptedRootVector label roots
         in length encoded `seq` requireSortedUnique label roots

requireCanonicalAcceptedRootWindow :: Int -> String -> [(String, Int, Int, Int)] -> ()
requireCanonicalAcceptedRootWindow ledgerEpoch label entries
    | null entries = error (label ++ " must not be empty")
    | otherwise =
        let encoded = encodeTransactionAcceptedRootWindowEntryVector label entries
            roots = [(digest, depth) | (digest, depth, _, _) <- entries]
            live = all entryLive entries
         in length encoded `seq`
            if not live
              then error (label ++ " contains a root that is not live at ledgerEpoch")
              else requireSortedUnique label roots
  where
    entryLive (_, _, validFromEpoch, expiresAtEpoch) =
        validFromEpoch <= ledgerEpoch && ledgerEpoch < expiresAtEpoch

bignumBytes :: [Int] -> [Word8]
bignumBytes = map fromIntegral

encodeNonNegativeI64 :: String -> Int -> [Word8]
encodeNonNegativeI64 label value
    | value < 0 = error (label ++ " must be non-negative")
    | otherwise = transactionInt64LeBytes value

encodeBignumValueBytes :: Integer -> [Word8]
encodeBignumValueBytes = bignumBytes . encodeBignumInteger

encodeBignumVectorBytes :: String -> [Integer] -> [Word8]
encodeBignumVectorBytes _ = bignumBytes . encodeBignumIntegerVector

encodeBignumMatrixBytes :: String -> [[Integer]] -> [Word8]
encodeBignumMatrixBytes label rows =
    encodeNonNegativeI64 (label ++ ".length") (length rows) ++
    concat
      [ encodeBignumVectorBytes (label ++ "[" ++ show index ++ "]") row
      | (index, row) <- zip [0 :: Int ..] rows
      ]

encodeBignumCubeBytes :: String -> [[[Integer]]] -> [Word8]
encodeBignumCubeBytes label cubes =
    encodeNonNegativeI64 (label ++ ".length") (length cubes) ++
    concat
      [ encodeBignumMatrixBytes (label ++ "[" ++ show index ++ "]") cube
      | (index, cube) <- zip [0 :: Int ..] cubes
      ]

bignumDigest :: [Word8] -> String
bignumDigest = transactionDigestHex . RepeatedFS.sha3_256

bignumMerklePreimage :: Int -> [Word8] -> [Word8]
bignumMerklePreimage tag body =
    map (fromIntegral . ord) bignumMerkleDst ++ encodeNonNegativeI64 "merkle tag" tag ++ body

bignumMerkleLeaf :: [Integer] -> String
bignumMerkleLeaf commitment =
    bignumDigest (bignumMerklePreimage 0 (encodeBignumVectorBytes "commitment" commitment))

bignumMerkleEmpty :: Int -> String
bignumMerkleEmpty width =
    bignumDigest (bignumMerklePreimage 2 (encodeNonNegativeI64 "width" width))

bignumMerkleNode :: String -> String -> String
bignumMerkleNode left right =
    bignumDigest
      (bignumMerklePreimage
        1
        (encodeTransactionDigest "left" left ++ encodeTransactionDigest "right" right))

sameBignumWidth :: [[Integer]] -> Int -> Bool
sameBignumWidth commitments width =
    all ((== width) . length) commitments

bignumMerkleCompressLevel :: Int -> [String] -> [String]
bignumMerkleCompressLevel _ [] = []
bignumMerkleCompressLevel _ [x] = [x]
bignumMerkleCompressLevel width xs =
    go xs
  where
    go [] = []
    go [left] = [bignumMerkleNode left (bignumMerkleEmpty width)]
    go (left:right:rest) = bignumMerkleNode left right : go rest

bignumMerkleRoot :: [[Integer]] -> String
bignumMerkleRoot commitments =
    let width = case commitments of
          [] -> 0
          first:_ -> length first
     in if not (sameBignumWidth commitments width)
          then error "Bignum Merkle commitments must all have the same width"
          else case commitments of
            [] -> bignumMerkleEmpty 0
            _ -> go (map bignumMerkleLeaf commitments)
              where
                go [] = bignumMerkleEmpty width
                go [x] = x
                go level = go (bignumMerkleCompressLevel width level)

bignumMerklePathRoot :: [Integer] -> [String] -> [Bool] -> Maybe String
bignumMerklePathRoot commitment siblings directions =
    go (bignumMerkleLeaf commitment) siblings directions
  where
    go acc [] [] = Just acc
    go acc (sibling:restSiblings) (False:restDirections) =
        go (bignumMerkleNode acc sibling) restSiblings restDirections
    go acc (sibling:restSiblings) (True:restDirections) =
        go (bignumMerkleNode sibling acc) restSiblings restDirections
    go _ _ _ = Nothing

bignumMerkleMembershipProve :: [[Integer]] -> [Integer] -> Maybe ConfidentialMerkle.MerkleMembershipProof
bignumMerkleMembershipProve ledger commitment = do
    index <- findIndex (== commitment) ledger
    let width = case ledger of
          [] -> length commitment
          first:_ -> length first
    if not (sameBignumWidth ledger width)
      then Nothing
      else go index width index (map bignumMerkleLeaf ledger) [] []
  where
    go _ _ _ [] _ _ = Nothing
    go originalIndex _ _ [rt] siblings directions =
        Just
          ConfidentialMerkle.MerkleMembershipProof
            { ConfidentialMerkle.merkle_index = originalIndex
            , ConfidentialMerkle.merkle_root = rt
            , ConfidentialMerkle.merkle_siblings = reverse siblings
            , ConfidentialMerkle.merkle_directions = reverse directions
            }
    go originalIndex width current level siblings directions =
        let isRight = odd current
            sibling =
              if isRight
                then level !! (current - 1)
                else if current + 1 < length level
                  then level !! (current + 1)
                  else bignumMerkleEmpty width
         in go
              originalIndex
              width
              (current `div` 2)
              (bignumMerkleCompressLevel width level)
              (sibling : siblings)
              (isRight : directions)

bignumIndexDirections :: Int -> Int -> [Bool]
bignumIndexDirections depth index
    | depth <= 0 = []
    | otherwise = odd index : bignumIndexDirections (depth - 1) (index `div` 2)

bignumMerkleMembershipVerify :: [Integer] -> ConfidentialMerkle.MerkleMembershipProof -> Bool
bignumMerkleMembershipVerify commitment proof =
    ConfidentialMerkle.merkle_directions proof ==
      bignumIndexDirections (length (ConfidentialMerkle.merkle_siblings proof)) (ConfidentialMerkle.merkle_index proof) &&
    case (transactionHexToBytes (ConfidentialMerkle.merkle_root proof),
          bignumMerklePathRoot commitment (ConfidentialMerkle.merkle_siblings proof) (ConfidentialMerkle.merkle_directions proof)) of
      (Just _, Just rt) -> rt == ConfidentialMerkle.merkle_root proof
      _ -> False

bignumTransactionTaggedPreimage :: Int -> [Word8] -> [Word8]
bignumTransactionTaggedPreimage tag body =
    map (fromIntegral . ord) bignumTransactionDst ++
    encodeNonNegativeI64 "transaction tag" tag ++
    encodeTransactionAscii "protocolId" sisNoteProtocolId ++
    body

encodeAcceptedRootBytes :: String -> (String, Int) -> [Word8]
encodeAcceptedRootBytes = encodeTransactionAcceptedRoot

encodeAcceptedRootVectorBytes :: String -> [(String, Int)] -> [Word8]
encodeAcceptedRootVectorBytes = encodeTransactionAcceptedRootVector

encodeAcceptedRootWindowEntryVectorBytes :: String -> [(String, Int, Int, Int)] -> [Word8]
encodeAcceptedRootWindowEntryVectorBytes = encodeTransactionAcceptedRootWindowEntryVector

bignumTransactionContextPreimage ::
  Int -> String -> Int -> Int -> String -> Int -> Integer ->
  [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Word8]
bignumTransactionContextPreimage protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
  cIn1 cIn2 cOut1 cOut2 nf1 nf2 =
    map (fromIntegral . ord) bignumTransactionDst ++
    encodeNonNegativeI64 "transaction tag" 0 ++
    encodeTransactionAscii "protocolId" sisNoteProtocolId ++
    encodeNonNegativeI64 "protocolVersion" protocolVersion ++
    encodeTransactionAscii "networkId" networkId ++
    encodeNonNegativeI64 "assetId" assetId ++
    encodeNonNegativeI64 "ledgerEpoch" ledgerEpoch ++
    encodeAcceptedRootBytes "root" (rt, rootDepth) ++
    encodeBignumValueBytes publicFee ++
    encodeBignumVectorBytes "cIn1" cIn1 ++
    encodeBignumVectorBytes "cIn2" cIn2 ++
    encodeBignumVectorBytes "cOut1" cOut1 ++
    encodeBignumVectorBytes "cOut2" cOut2 ++
    encodeBignumVectorBytes "nf1" nf1 ++
    encodeBignumVectorBytes "nf2" nf2

bignumTransactionContextDigest ::
  Int -> String -> Int -> Int -> String -> Int -> Integer ->
  [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> String
bignumTransactionContextDigest protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
  cIn1 cIn2 cOut1 cOut2 nf1 nf2 =
    bignumDigest
      (bignumTransactionContextPreimage
        protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
        cIn1 cIn2 cOut1 cOut2 nf1 nf2)

bignumAcceptedRootWindowDigest :: Int -> String -> Int -> Int -> [String] -> [Int] -> [Int] -> [Int] -> String
bignumAcceptedRootWindowDigest protocolVersion networkId assetId ledgerEpoch roots rootDepths validFromEpochs expiresAtEpochs =
    let lengthsOk =
          length roots == length rootDepths &&
          length roots == length validFromEpochs &&
          length roots == length expiresAtEpochs
        entries = zip4 roots rootDepths validFromEpochs expiresAtEpochs
     in if not lengthsOk
          then error "acceptedRootWindow.roots vectors must have the same length"
          else
            requireCanonicalAcceptedRootWindow ledgerEpoch "acceptedRootWindow.roots" entries `seq`
            bignumDigest
              (bignumTransactionTaggedPreimage
                4
                ( encodeNonNegativeI64 "acceptedRootWindow.protocolVersion" protocolVersion ++
                  encodeTransactionAscii "acceptedRootWindow.networkId" networkId ++
                  encodeNonNegativeI64 "acceptedRootWindow.assetId" assetId ++
                  encodeNonNegativeI64 "acceptedRootWindow.ledgerEpoch" ledgerEpoch ++
                  encodeAcceptedRootWindowEntryVectorBytes "acceptedRootWindow.roots" entries
                ))

bignumMembershipPreimage :: String -> ConfidentialMerkle.MerkleMembershipProof -> [Word8]
bignumMembershipPreimage label proof
    | length (ConfidentialMerkle.merkle_siblings proof) /=
        length (ConfidentialMerkle.merkle_directions proof) =
        error (label ++ ".siblings and directions must have the same length")
    | otherwise =
        encodeNonNegativeI64 (label ++ ".index") (ConfidentialMerkle.merkle_index proof) ++
        encodeTransactionDigest (label ++ ".root") (ConfidentialMerkle.merkle_root proof) ++
        encodeTransactionDigestVector (label ++ ".siblings") (ConfidentialMerkle.merkle_siblings proof) ++
        encodeTransactionBoolVec (ConfidentialMerkle.merkle_directions proof)

bignumNullifierProofPreimage :: String -> BigNfProof -> [Word8]
bignumNullifierProofPreimage label proof =
    encodeBignumMatrixBytes (label ++ ".aCommits") (bigNfACommits proof) ++
    encodeBignumMatrixBytes (label ++ ".aNullifiers") (bigNfANullifiers proof) ++
    encodeBignumMatrixBytes (label ++ ".zMsgs") (bigNfZMsgs proof) ++
    encodeBignumMatrixBytes (label ++ ".zRands") (bigNfZRands proof)

bignumBalanceProofPreimage :: String -> BigCbProof -> [Word8]
bignumBalanceProofPreimage label proof =
    encodeBignumMatrixBytes (label ++ ".as") (bigCbAs proof) ++
    encodeBignumMatrixBytes (label ++ ".zs") (bigCbZs proof)

bignumRangeProofPreimage :: String -> BigCrProof -> [Word8]
bignumRangeProofPreimage label proof =
    encodeBignumMatrixBytes (label ++ ".bits") (bigCrBits proof) ++
    encodeBignumMatrixBytes (label ++ ".comps") (bigCrComps proof) ++
    encodeBignumMatrixBytes (label ++ ".amountAs") (bigCrAmountAs proof) ++
    encodeBignumMatrixBytes (label ++ ".amountZs") (bigCrAmountZs proof) ++
    encodeBignumCubeBytes (label ++ ".pairAss") (bigCrPairAss proof) ++
    encodeBignumCubeBytes (label ++ ".pairZss") (bigCrPairZss proof)

bignumMerkleProofPreimage :: BigMerkleTransactionProof -> [Word8]
bignumMerkleProofPreimage proof =
    bignumTransactionTaggedPreimage 1 $
      bignumMembershipPreimage "in1Member" (bigTxIn1Member proof) ++
      bignumMembershipPreimage "in2Member" (bigTxIn2Member proof) ++
      bignumNullifierProofPreimage "in1Nullifier" (bigTxIn1Nullifier proof) ++
      bignumNullifierProofPreimage "in2Nullifier" (bigTxIn2Nullifier proof) ++
      bignumBalanceProofPreimage "balance" (bigTxBalance proof) ++
      bignumRangeProofPreimage "out1Range" (bigTxOut1Range proof) ++
      bignumRangeProofPreimage "out2Range" (bigTxOut2Range proof)

bignumMerkleProofDigest :: BigMerkleTransactionProof -> String
bignumMerkleProofDigest = bignumDigest . bignumMerkleProofPreimage

bignumEnvelopeDigest ::
  String -> Int -> String -> Int -> Int -> String -> Int -> Integer ->
  [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] ->
  BigMerkleTransactionProof -> String
bignumEnvelopeDigest contextDigest protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
  cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
    let computedDigest =
          bignumTransactionContextDigest
            protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
            cIn1 cIn2 cOut1 cOut2 nf1 nf2
     in if contextDigest /= computedDigest
          then error "contextDigest does not match canonical bignum transaction context"
          else
            bignumDigest
              (bignumTransactionTaggedPreimage
                2
                (encodeTransactionDigest "contextDigest" computedDigest ++
                 encodeTransactionDigest "proofDigest" (bignumMerkleProofDigest proof)))

bignumWalletProofRequestDigest ::
  Int -> String -> Int -> Int -> String -> Int -> Integer ->
  [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] ->
  [String] -> [Int] -> [[Integer]] -> String
bignumWalletProofRequestDigest protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
  cIn1 cIn2 cOut1 cOut2 nf1 nf2 acceptedRoots acceptedRootDepths spentNullifiers =
    let rootLengthsOk =
          if length acceptedRoots == length acceptedRootDepths
            then ()
            else error "acceptedRoots and acceptedRootDepths must have the same length"
        acceptedRootPairs = zip acceptedRoots acceptedRootDepths
        contextDigest =
          bignumTransactionContextDigest
            protocolVersion networkId assetId ledgerEpoch rt rootDepth publicFee
            cIn1 cIn2 cOut1 cOut2 nf1 nf2
     in rootLengthsOk `seq`
        requireCanonicalAcceptedRootSet "acceptedRoots" acceptedRootPairs `seq`
        requireSortedUnique "spentNullifiers" spentNullifiers `seq`
        if (rt, rootDepth) `notElem` acceptedRootPairs
          then error "context.root must be inside acceptedRoots"
          else
            if nf1 == nf2
              then error "context nullifiers must be distinct"
              else
                if nf1 `elem` spentNullifiers || nf2 `elem` spentNullifiers
                  then error "context nullifiers must be absent from spentNullifiers"
                  else
                    bignumDigest
                      (bignumTransactionTaggedPreimage
                        3
                        (encodeTransactionDigest "contextDigest" contextDigest ++
                         encodeAcceptedRootVectorBytes "acceptedRoots" acceptedRootPairs ++
                         encodeBignumMatrixBytes "spentNullifiers" spentNullifiers))

requireNonnegativePublicFee :: Integer -> Bool
requireNonnegativePublicFee = (>= 0)

bignumBalanceCommitment :: BigCbParams -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer]
bignumBalanceCommitment params cIn1 cIn2 cOut1 cOut2 =
    bigVecMod
        (bigVecAdd
            (bigVecAdd cIn1 cIn2)
            (bigScalarMult (-1) (bigVecAdd cOut1 cOut2)))
        (bigCbQ params)

bignumPublicAmountCommitment :: BigCbParams -> [[Integer]] -> Integer -> [Integer]
bignumPublicAmountCommitment params ck publicFee =
    if requireNonnegativePublicFee publicFee
      then bigCommit params ck (BigOpening [publicFee] (replicate (bigCbN2 params) 0))
      else error "publicFee must be non-negative"

bignumFeeBalanceCommitment ::
  BigCbParams -> [[Integer]] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> Integer -> [Integer]
bignumFeeBalanceCommitment params ck cIn1 cIn2 cOut1 cOut2 publicFee =
    bigVecMod
        (bigVecAdd
            (bignumBalanceCommitment params cIn1 cIn2 cOut1 cOut2)
            (bigScalarMult (-1) (bignumPublicAmountCommitment params ck publicFee)))
        (bigCbQ params)

bignumVerifyMerkleWithFee ::
  BigCbParams -> Integer -> Int -> [[Integer]] -> [[Integer]] -> [[Integer]] ->
  String -> Int -> [[Integer]] -> Integer ->
  [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] -> [Integer] ->
  BigMerkleTransactionProof -> Bool
bignumVerifyMerkleWithFee params gamma k ck nk ledger rootDigest rootDepth spent publicFee
  cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
    let proofDigestForced = length (bignumMerkleProofDigest proof) == 64
        in1Member = bigTxIn1Member proof
        in2Member = bigTxIn2Member proof
        in1Depth = length (ConfidentialMerkle.merkle_siblings in1Member)
        in2Depth = length (ConfidentialMerkle.merkle_siblings in2Member)
        balanceTarget =
          bignumFeeBalanceCommitment params ck cIn1 cIn2 cOut1 cOut2 publicFee
     in proofDigestForced &&
        requireNonnegativePublicFee publicFee &&
        validBigCommitKey params ck &&
        validBigCommitKey params nk &&
        bignumMerkleRoot ledger == rootDigest &&
        in1Depth == rootDepth &&
        in2Depth == rootDepth &&
        bignumMerkleMembershipVerify cIn1 in1Member &&
        bignumMerkleMembershipVerify cIn2 in2Member &&
        ConfidentialMerkle.merkle_root in1Member == rootDigest &&
        ConfidentialMerkle.merkle_root in2Member == rootDigest &&
        ConfidentialMerkle.merkle_index in1Member /= ConfidentialMerkle.merkle_index in2Member &&
        nf1 `notElem` spent &&
        nf2 `notElem` spent &&
        nf1 /= nf2 &&
        bigNfFsVerify params gamma ck nk cIn1 nf1 (bigTxIn1Nullifier proof) &&
        bigNfFsVerify params gamma ck nk cIn2 nf2 (bigTxIn2Nullifier proof) &&
        bigFsVerify params gamma ck balanceTarget (bigTxBalance proof) &&
        bigCrFsVerify params gamma k ck cOut1 (bigTxOut1Range proof) &&
        bigCrFsVerify params gamma k ck cOut2 (bigTxOut2Range proof)

bignumHex :: [Int] -> String
bignumHex = concatMap bignumHexByte

parseStringList :: String -> Maybe [String]
parseStringList = readMaybe

jsonString :: String -> String
jsonString = show

jsonBool :: Bool -> String
jsonBool True = "true"
jsonBool False = "false"

jsonBoolList :: [Bool] -> String
jsonBoolList = ("[" ++) . (++ "]") . intercalate "," . map jsonBool

jsonStringList :: [String] -> String
jsonStringList = ("[" ++) . (++ "]") . intercalate "," . map jsonString

jsonVec :: [Int] -> String
jsonVec = ("[" ++) . (++ "]") . intercalate "," . map show

jsonMat :: [[Int]] -> String
jsonMat = ("[" ++) . (++ "]") . intercalate "," . map jsonVec

jsonInteger :: Integer -> String
jsonInteger = jsonString . show

jsonIntegerVec :: [Integer] -> String
jsonIntegerVec = ("[" ++) . (++ "]") . intercalate "," . map jsonInteger

jsonIntegerMat :: [[Integer]] -> String
jsonIntegerMat = ("[" ++) . (++ "]") . intercalate "," . map jsonIntegerVec

jsonIntegerCube :: [[[Integer]]] -> String
jsonIntegerCube = ("[" ++) . (++ "]") . intercalate "," . map jsonIntegerMat

jsonCube :: [[[Int]]] -> String
jsonCube = ("[" ++) . (++ "]") . intercalate "," . map jsonMat

jsonObject :: [(String, String)] -> String
jsonObject fields =
    "{" ++ intercalate "," [jsonString key ++ ":" ++ value | (key, value) <- fields] ++ "}"

jsonMerkleMembershipProof :: ConfidentialMerkle.MerkleMembershipProof -> String
jsonMerkleMembershipProof proof =
    jsonObject
        [ ("index", show (ConfidentialMerkle.merkle_index proof))
        , ("root", jsonString (ConfidentialMerkle.merkle_root proof))
        , ("siblings", jsonStringList (ConfidentialMerkle.merkle_siblings proof))
        , ("directions", jsonBoolList (ConfidentialMerkle.merkle_directions proof))
        ]

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

scaffoldCompatEnabled :: IO Bool
scaffoldCompatEnabled = do
    value <- lookupEnv "ISABELLA_ENABLE_SCAFFOLD_COMPAT"
    pure (value == Just "1" || value == Just "true")

runScaffoldCompat :: OutputFormat -> IO () -> IO ()
runScaffoldCompat format action = do
    enabled <- scaffoldCompatEnabled
    if enabled
        then action
        else outputError format "Scaffold compatibility commands require ISABELLA_ENABLE_SCAFFOLD_COMPAT=1 and are excluded from launch builds"

outputUsage :: OutputFormat -> String -> IO ()
outputUsage Human msg = putStrLn msg
outputUsage Json msg = putStrLn $ "{\"error\":" ++ jsonString msg ++ "}"

outputIntResult :: OutputFormat -> String -> Int -> IO ()
outputIntResult Human label result = putStrLn $ label ++ show result
outputIntResult Json _ result = putStrLn $ "{\"result\":" ++ show result ++ "}"

outputBoolResult :: OutputFormat -> String -> Bool -> IO ()
outputBoolResult Human label result = putStrLn $ label ++ show result
outputBoolResult Json _ result = putStrLn $ "{\"result\":" ++ jsonBool result ++ "}"

outputStringResult :: OutputFormat -> String -> String -> IO ()
outputStringResult Human label result = putStrLn $ label ++ result
outputStringResult Json _ result = putStrLn $ "{\"result\":" ++ jsonString result ++ "}"

outputVecResult :: OutputFormat -> String -> [Int] -> IO ()
outputVecResult Human label result = putStrLn $ label ++ show result
outputVecResult Json _ result = putStrLn $ "{\"result\":" ++ jsonVec result ++ "}"

outputMatResult :: OutputFormat -> String -> [[Int]] -> IO ()
outputMatResult Human label result = putStrLn $ label ++ show result
outputMatResult Json _ result = putStrLn $ "{\"result\":" ++ jsonMat result ++ "}"

jsonOpening :: Commit.CommitOpening -> String
jsonOpening opening =
    jsonObject
        [ ("msg", jsonVec (Commit.open_msg opening))
        , ("rand", jsonVec (Commit.open_rand opening))
        ]

jsonOpenings :: [Commit.CommitOpening] -> String
jsonOpenings = ("[" ++) . (++ "]") . intercalate "," . map jsonOpening

outputOpeningResult :: OutputFormat -> String -> Commit.CommitOpening -> IO ()
outputOpeningResult Human label result = putStrLn $ label ++ jsonOpening result
outputOpeningResult Json _ result = putStrLn $ "{\"result\":" ++ jsonOpening result ++ "}"

outputOpeningsResult :: OutputFormat -> String -> [Commit.CommitOpening] -> IO ()
outputOpeningsResult Human label result = putStrLn $ label ++ jsonOpenings result
outputOpeningsResult Json _ result = putStrLn $ "{\"result\":" ++ jsonOpenings result ++ "}"

handleSampleError :: OutputFormat -> SomeException -> IO ()
handleSampleError format error_ = outputError format (show error_)

outputSampleResult :: OutputFormat -> (a -> IO ()) -> IO a -> IO ()
outputSampleResult format output action =
    (action >>= output) `catch` handleSampleError format

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

data BigCbParams = BigCbParams
  { bigCbN1 :: Int
  , bigCbN2 :: Int
  , bigCbM :: Int
  , bigCbQ :: Integer
  , bigCbBeta :: Integer
  }

data BigCbProof = BigCbProof
  { bigCbAs :: [[Integer]]
  , bigCbZs :: [[Integer]]
  }

data BigOpening = BigOpening
  { bigOpenMsg :: [Integer]
  , bigOpenRand :: [Integer]
  }

data BigCrProof = BigCrProof
  { bigCrBits :: [[Integer]]
  , bigCrComps :: [[Integer]]
  , bigCrAmountAs :: [[Integer]]
  , bigCrAmountZs :: [[Integer]]
  , bigCrPairAss :: [[[Integer]]]
  , bigCrPairZss :: [[[Integer]]]
  }

data BigNfProof = BigNfProof
  { bigNfACommits :: [[Integer]]
  , bigNfANullifiers :: [[Integer]]
  , bigNfZMsgs :: [[Integer]]
  , bigNfZRands :: [[Integer]]
  }

data BigMerkleTransactionProof = BigMerkleTransactionProof
  { bigTxIn1Member :: ConfidentialMerkle.MerkleMembershipProof
  , bigTxIn2Member :: ConfidentialMerkle.MerkleMembershipProof
  , bigTxIn1Nullifier :: BigNfProof
  , bigTxIn2Nullifier :: BigNfProof
  , bigTxBalance :: BigCbProof
  , bigTxOut1Range :: BigCrProof
  , bigTxOut2Range :: BigCrProof
  }

jsonBigCbProof :: BigCbProof -> String
jsonBigCbProof proof =
    jsonObject
        [ ("as", jsonIntegerMat (bigCbAs proof))
        , ("zs", jsonIntegerMat (bigCbZs proof))
        ]

jsonBigCrProof :: BigCrProof -> String
jsonBigCrProof proof =
    jsonObject
        [ ("bits", jsonIntegerMat (bigCrBits proof))
        , ("comps", jsonIntegerMat (bigCrComps proof))
        , ("amountAs", jsonIntegerMat (bigCrAmountAs proof))
        , ("amountZs", jsonIntegerMat (bigCrAmountZs proof))
        , ("pairAss", jsonIntegerCube (bigCrPairAss proof))
        , ("pairZss", jsonIntegerCube (bigCrPairZss proof))
        ]

jsonBigNfProof :: BigNfProof -> String
jsonBigNfProof proof =
    jsonObject
        [ ("aCommits", jsonIntegerMat (bigNfACommits proof))
        , ("aNullifiers", jsonIntegerMat (bigNfANullifiers proof))
        , ("zMsgs", jsonIntegerMat (bigNfZMsgs proof))
        , ("zRands", jsonIntegerMat (bigNfZRands proof))
        ]

bigCbFsDomain :: Int
bigCbFsDomain = 1001

bigCrFsDomain :: Int
bigCrFsDomain = 2001

bigNfFsDomain :: Int
bigNfFsDomain = 3001

bigCbFsRounds :: Int
bigCbFsRounds = 128

bigCbTranscriptDst :: String
bigCbTranscriptDst = "ISABELLA-CT-FS-v1"

parseBigCbParams :: String -> String -> String -> String -> Maybe BigCbParams
parseBigCbParams mStr n2Str qStr betaStr =
    case (parseCanonicalInt mStr, parseCanonicalInt n2Str, parseCanonicalInteger qStr, parseCanonicalInteger betaStr) of
        (Just m, Just n2, Just q, Just beta) ->
            Just (BigCbParams 1 n2 m q beta)
        _ -> Nothing

validBigCbParams :: BigCbParams -> Bool
validBigCbParams params =
    bigCbN1 params == 1 &&
    bigCbN2 params > 0 &&
    bigCbM params > 0 &&
    bigCbQ params > 1 &&
    bigCbBeta params > 0

validBigVec :: Int -> [Integer] -> Bool
validBigVec expected xs = length xs == expected

validBigCommitKey :: BigCbParams -> [[Integer]] -> Bool
validBigCommitKey params ck =
    validBigCbParams params &&
    length ck == bigCbM params &&
    all (validBigVec (bigCbN1 params + bigCbN2 params)) ck

bigRandCommitKey :: BigCbParams -> [[Integer]] -> [[Integer]]
bigRandCommitKey params = map (drop (bigCbN1 params))

bigMod :: Integer -> Integer -> Integer
bigMod value modulus =
    let reduced = value `mod` modulus
     in if reduced < 0 then reduced + modulus else reduced

bigVecMod :: [Integer] -> Integer -> [Integer]
bigVecMod xs modulus = map (`bigMod` modulus) xs

bigVecAdd :: [Integer] -> [Integer] -> [Integer]
bigVecAdd = zipWith (+)

bigScalarMult :: Integer -> [Integer] -> [Integer]
bigScalarMult scalar = map (scalar *)

bigMatVecMult :: [[Integer]] -> [Integer] -> [Integer]
bigMatVecMult matrix vector =
    [sum (zipWith (*) row vector) | row <- matrix]

bigMatVecMultMod :: [[Integer]] -> [Integer] -> Integer -> [Integer]
bigMatVecMultMod matrix vector modulus =
    bigVecMod (bigMatVecMult matrix vector) modulus

bigRandCommit :: BigCbParams -> [[Integer]] -> [Integer] -> [Integer]
bigRandCommit params ck r =
    bigMatVecMultMod (bigRandCommitKey params ck) r (bigCbQ params)

bigAllBounded :: [Integer] -> Integer -> Bool
bigAllBounded xs bound = bound >= 0 && all ((<= bound) . abs) xs

validBigWitness :: BigCbParams -> [Integer] -> Bool
validBigWitness params r =
    validBigCbParams params &&
    validBigVec (bigCbN2 params) r &&
    bigAllBounded r (4 * bigCbBeta params)

validBigMask :: BigCbParams -> Integer -> [Integer] -> Bool
validBigMask params gamma y =
    validBigCbParams params &&
    validBigVec (bigCbN2 params) y &&
    bigAllBounded y gamma

validBigResponse :: BigCbParams -> Integer -> Int -> [Integer] -> Bool
validBigResponse params gamma challenge z =
    (challenge == 0 || challenge == 1) &&
    validBigCbParams params &&
    validBigVec (bigCbN2 params) z &&
    bigAllBounded z (gamma + toInteger challenge * 4 * bigCbBeta params)

bigBalanceRelation :: BigCbParams -> [[Integer]] -> [Integer] -> [Integer] -> Bool
bigBalanceRelation params ck c r =
    validBigCommitKey params ck &&
    validBigVec (bigCbM params) c &&
    validBigWitness params r &&
    bigRandCommit params ck r == c

bigSigmaRespond :: [Integer] -> [Integer] -> Int -> [Integer]
bigSigmaRespond r y challenge =
    bigVecAdd y (bigScalarMult (toInteger challenge) r)

bigFsTranscriptBytes :: Int -> Int -> [Integer] -> [Int]
bigFsTranscriptBytes domain roundIndex fields =
    map ord bigCbTranscriptDst ++
    bignumLengthLeBytes domain ++
    bignumLengthLeBytes roundIndex ++
    bignumLengthLeBytes (length fields) ++
    concatMap encodeBignumInteger fields

bigBinaryFsChallenge :: Int -> [Integer] -> Int -> Int
bigBinaryFsChallenge domain fields roundIndex =
    case RepeatedFS.sha3_256 (map fromIntegral (bigFsTranscriptBytes domain roundIndex fields)) of
        firstByte : _ -> fromIntegral (firstByte .&. 1)
        [] -> error "sha3_256 produced no output"

bigFsFields :: [[Integer]] -> [Integer] -> [[Integer]] -> [Integer]
bigFsFields ck c as_ =
    [sum (concat ck), sum c, sum (concat as_)]

bigFsChallenges :: [[Integer]] -> [Integer] -> [[Integer]] -> Int -> [Int]
bigFsChallenges ck c as_ rounds =
    let fields = bigFsFields ck c as_
     in [bigBinaryFsChallenge bigCbFsDomain fields roundIndex | roundIndex <- [0 .. rounds - 1]]

bigSigmaVerify :: BigCbParams -> Integer -> [[Integer]] -> [Integer] -> [Integer] -> Int -> [Integer] -> Bool
bigSigmaVerify params gamma ck c a challenge z =
    validBigCommitKey params ck &&
    validBigVec (bigCbM params) c &&
    validBigVec (bigCbM params) a &&
    validBigResponse params gamma challenge z &&
    bigRandCommit params ck z ==
        bigVecMod (bigVecAdd a (bigScalarMult (toInteger challenge) c)) (bigCbQ params)

bigFsProve :: BigCbParams -> Integer -> [[Integer]] -> [Integer] -> [Integer] -> [[Integer]] -> Maybe BigCbProof
bigFsProve params gamma ck c r ys =
    let as_ = map (bigRandCommit params ck) ys
        challenges = bigFsChallenges ck c as_ bigCbFsRounds
        zs = zipWith (bigSigmaRespond r) ys challenges
     in if length ys == bigCbFsRounds &&
           bigBalanceRelation params ck c r &&
           all (validBigMask params gamma) ys &&
           and (zipWith (validBigResponse params gamma) challenges zs)
        then Just (BigCbProof as_ zs)
        else Nothing

bigFsVerify :: BigCbParams -> Integer -> [[Integer]] -> [Integer] -> BigCbProof -> Bool
bigFsVerify params gamma ck c proof =
    let as_ = bigCbAs proof
        zs = bigCbZs proof
        challenges = bigFsChallenges ck c as_ bigCbFsRounds
     in validBigCbParams params &&
        validBigCommitKey params ck &&
        length as_ == bigCbFsRounds &&
        length zs == bigCbFsRounds &&
        and (zipWith3 (bigSigmaVerify params gamma ck c) as_ challenges zs)

bigOpening :: [Integer] -> [Integer] -> BigOpening
bigOpening = BigOpening

validBigOpening :: BigCbParams -> BigOpening -> Bool
validBigOpening params opening =
    validBigOpeningShape params opening &&
    bigAllBounded (bigOpenMsg opening) (bigCbBeta params) &&
    bigAllBounded (bigOpenRand opening) (bigCbBeta params)

validBigOpeningShape :: BigCbParams -> BigOpening -> Bool
validBigOpeningShape params opening =
    validBigCbParams params &&
    validBigVec (bigCbN1 params) (bigOpenMsg opening) &&
    validBigVec (bigCbN2 params) (bigOpenRand opening)

validBigBitOpening :: BigCbParams -> BigOpening -> Bool
validBigBitOpening params opening =
    validBigOpening params opening &&
    bigAllBounded (bigOpenMsg opening) 1

bigCommit :: BigCbParams -> [[Integer]] -> BigOpening -> [Integer]
bigCommit params ck opening =
    bigMatVecMultMod ck (bigOpenMsg opening ++ bigOpenRand opening) (bigCbQ params)

bigZeroOpening :: BigCbParams -> BigOpening
bigZeroOpening params =
    BigOpening (replicate (bigCbN1 params) 0) (replicate (bigCbN2 params) 0)

bigOneOpening :: BigCbParams -> BigOpening
bigOneOpening params =
    BigOpening [1] (replicate (bigCbN2 params) 0)

bigOpeningAdd :: BigOpening -> BigOpening -> BigOpening
bigOpeningAdd left right =
    BigOpening
        (bigVecAdd (bigOpenMsg left) (bigOpenMsg right))
        (bigVecAdd (bigOpenRand left) (bigOpenRand right))

bigOpeningSub :: BigOpening -> BigOpening -> BigOpening
bigOpeningSub left right =
    BigOpening
        (bigVecAdd (bigOpenMsg left) (bigScalarMult (-1) (bigOpenMsg right)))
        (bigVecAdd (bigOpenRand left) (bigScalarMult (-1) (bigOpenRand right)))

bigOpeningScale :: Integer -> BigOpening -> BigOpening
bigOpeningScale scalar opening =
    BigOpening
        (bigScalarMult scalar (bigOpenMsg opening))
        (bigScalarMult scalar (bigOpenRand opening))

bigWeightedOpening :: BigCbParams -> Integer -> [BigOpening] -> BigOpening
bigWeightedOpening params base =
    foldr (\opening acc -> bigOpeningAdd opening (bigOpeningScale base acc)) (bigZeroOpening params)

bigWeightedCommitment :: BigCbParams -> [[Integer]] -> Integer -> [[Integer]] -> [Integer]
bigWeightedCommitment params ck base =
    foldr
        (\row acc -> bigVecMod (bigVecAdd row (bigScalarMult base acc)) (bigCbQ params))
        (bigRandCommit params ck (replicate (bigCbN2 params) 0))

bigAmountOfOpening :: BigOpening -> Integer
bigAmountOfOpening opening =
    case bigOpenMsg opening of
        value : _ -> value
        [] -> 0

bigBitPairRelation :: BigCbParams -> BigOpening -> BigOpening -> Bool
bigBitPairRelation params bitOpening compOpening =
    validBigBitOpening params bitOpening &&
    validBigBitOpening params compOpening &&
    bigAmountOfOpening bitOpening + bigAmountOfOpening compOpening == 1

bigRecomposeBits :: [BigOpening] -> Integer
bigRecomposeBits openings =
    sum [bigAmountOfOpening opening * (2 ^ index) | (opening, index) <- zip openings [0 :: Int ..]]

bigCrAmountCommitment :: BigCbParams -> [[Integer]] -> [Integer] -> [[Integer]] -> [Integer]
bigCrAmountCommitment params ck cAmount cBits =
    bigVecMod
        (bigVecAdd cAmount (bigScalarMult (-1) (bigWeightedCommitment params ck 2 cBits)))
        (bigCbQ params)

bigCrPairCommitment :: BigCbParams -> [[Integer]] -> [Integer] -> [Integer] -> [Integer]
bigCrPairCommitment params ck cBit cComp =
    bigVecMod
        (bigVecAdd
            (bigVecAdd cBit cComp)
            (bigScalarMult (-1) (bigCommit params ck (bigOneOpening params))))
        (bigCbQ params)

bigCrPairCommitments :: BigCbParams -> [[Integer]] -> [[Integer]] -> [[Integer]] -> [[Integer]]
bigCrPairCommitments params ck cBits cComps =
    zipWith (bigCrPairCommitment params ck) cBits cComps

bigCrAmountOpening :: BigCbParams -> BigOpening -> [BigOpening] -> BigOpening
bigCrAmountOpening params amountOpening bitOpenings =
    bigOpeningSub amountOpening (bigWeightedOpening params 2 bitOpenings)

bigCrPairOpening :: BigCbParams -> BigOpening -> BigOpening -> BigOpening
bigCrPairOpening params bitOpening compOpening =
    bigOpeningSub (bigOpeningAdd bitOpening compOpening) (bigOneOpening params)

bigCrPairOpenings :: BigCbParams -> [BigOpening] -> [BigOpening] -> [BigOpening]
bigCrPairOpenings params =
    zipWith (bigCrPairOpening params)

bigCrAmountWitnessBound :: BigCbParams -> Int -> Integer
bigCrAmountWitnessBound params k =
    (2 ^ k) * bigCbBeta params

bigCrPairWitnessBound :: BigCbParams -> Integer
bigCrPairWitnessBound params =
    2 * bigCbBeta params

validBigCrAmountWitness :: BigCbParams -> Int -> [Integer] -> Bool
validBigCrAmountWitness params k r =
    k >= 0 &&
    validBigVec (bigCbN2 params) r &&
    bigAllBounded r (bigCrAmountWitnessBound params k)

validBigCrPairWitness :: BigCbParams -> [Integer] -> Bool
validBigCrPairWitness params r =
    validBigVec (bigCbN2 params) r &&
    bigAllBounded r (bigCrPairWitnessBound params)

bigCrAmountResponseBound :: BigCbParams -> Integer -> Int -> Int -> Integer
bigCrAmountResponseBound params gamma k challenge =
    gamma + toInteger challenge * bigCrAmountWitnessBound params k

bigCrPairResponseBound :: BigCbParams -> Integer -> Int -> Integer
bigCrPairResponseBound params gamma challenge =
    gamma + toInteger challenge * bigCrPairWitnessBound params

validBigCrAmountResponse :: BigCbParams -> Integer -> Int -> Int -> [Integer] -> Bool
validBigCrAmountResponse params gamma k challenge z =
    (challenge == 0 || challenge == 1) &&
    validBigVec (bigCbN2 params) z &&
    bigAllBounded z (bigCrAmountResponseBound params gamma k challenge)

validBigCrPairResponse :: BigCbParams -> Integer -> Int -> [Integer] -> Bool
validBigCrPairResponse params gamma challenge z =
    (challenge == 0 || challenge == 1) &&
    validBigVec (bigCbN2 params) z &&
    bigAllBounded z (bigCrPairResponseBound params gamma challenge)

bigCrRelation :: BigCbParams -> [[Integer]] -> [Integer] -> BigOpening -> [BigOpening] -> [BigOpening] -> Bool
bigCrRelation params ck cAmount amountOpening bitOpenings compOpenings =
    validBigCbParams params &&
    validBigCommitKey params ck &&
    validBigVec (bigCbM params) cAmount &&
    length bitOpenings == length compOpenings &&
    bigCommit params ck amountOpening == cAmount &&
    and (zipWith (bigBitPairRelation params) bitOpenings compOpenings) &&
    bigAmountOfOpening amountOpening == bigRecomposeBits bitOpenings

bigCrFsFields :: [[Integer]] -> [Integer] -> [[Integer]] -> [[Integer]] -> [[Integer]] -> [[[Integer]]] -> [Integer]
bigCrFsFields ck cAmount cBits cComps aAmounts aPairss =
    [ sum (concat ck)
    , sum cAmount
    , sum (concat cBits)
    , sum (concat cComps)
    , sum (concat aAmounts)
    , sum (concat (concat aPairss))
    ]

bigCrFsChallenges :: [[Integer]] -> [Integer] -> [[Integer]] -> [[Integer]] -> [[Integer]] -> [[[Integer]]] -> Int -> [Int]
bigCrFsChallenges ck cAmount cBits cComps aAmounts aPairss rounds =
    let fields = bigCrFsFields ck cAmount cBits cComps aAmounts aPairss
     in [bigBinaryFsChallenge bigCrFsDomain fields roundIndex | roundIndex <- [0 .. rounds - 1]]

bigCrSigmaVerify :: BigCbParams -> [[Integer]] -> [Integer] -> [Integer] -> Int -> [Integer] -> (Int -> [Integer] -> Bool) -> Bool
bigCrSigmaVerify params ck c a challenge z validResponse =
    validBigCommitKey params ck &&
    validBigVec (bigCbM params) c &&
    validBigVec (bigCbM params) a &&
    validResponse challenge z &&
    bigRandCommit params ck z ==
        bigVecMod (bigVecAdd a (bigScalarMult (toInteger challenge) c)) (bigCbQ params)

bigCrFsProve ::
  BigCbParams ->
  Integer ->
  Int ->
  [[Integer]] ->
  [Integer] ->
  BigOpening ->
  [BigOpening] ->
  [BigOpening] ->
  [[Integer]] ->
  [[[Integer]]] ->
  Maybe BigCrProof
bigCrFsProve params gamma k ck cAmount amountOpening bitOpenings compOpenings yAmounts yPairss =
    let bits = map (bigCommit params ck) bitOpenings
        comps = map (bigCommit params ck) compOpenings
        amountWitness = bigOpenRand (bigCrAmountOpening params amountOpening bitOpenings)
        pairWitnesses = map bigOpenRand (bigCrPairOpenings params bitOpenings compOpenings)
        amountAs = map (bigRandCommit params ck) yAmounts
        pairAss = map (map (bigRandCommit params ck)) yPairss
        challenges = bigCrFsChallenges ck cAmount bits comps amountAs pairAss bigCbFsRounds
        amountZs = zipWith (bigSigmaRespond amountWitness) yAmounts challenges
        pairZss =
            zipWith
                (\roundMasks challenge ->
                    zipWith (\mask witness -> bigSigmaRespond witness mask challenge) roundMasks pairWitnesses)
                yPairss
                challenges
     in if k >= 0 &&
           length bitOpenings == k &&
           length compOpenings == k &&
           length yAmounts == bigCbFsRounds &&
           length yPairss == bigCbFsRounds &&
           all ((== k) . length) yPairss &&
           bigCrRelation params ck cAmount amountOpening bitOpenings compOpenings &&
           all (validBigMask params gamma) yAmounts &&
           all (all (validBigMask params gamma)) yPairss &&
           validBigCrAmountWitness params k amountWitness &&
           all (validBigCrPairWitness params) pairWitnesses &&
           and (zipWith (validBigCrAmountResponse params gamma k) challenges amountZs) &&
           and
             [ all (validBigCrPairResponse params gamma challenge) responses
             | (challenge, responses) <- zip challenges pairZss
             ]
        then Just (BigCrProof bits comps amountAs amountZs pairAss pairZss)
        else Nothing

bigCrFsVerify :: BigCbParams -> Integer -> Int -> [[Integer]] -> [Integer] -> BigCrProof -> Bool
bigCrFsVerify params gamma k ck cAmount proof =
    let bits = bigCrBits proof
        comps = bigCrComps proof
        amountAs = bigCrAmountAs proof
        amountZs = bigCrAmountZs proof
        pairAss = bigCrPairAss proof
        pairZss = bigCrPairZss proof
        amountCommit = bigCrAmountCommitment params ck cAmount bits
        pairs = bigCrPairCommitments params ck bits comps
        challenges = bigCrFsChallenges ck cAmount bits comps amountAs pairAss bigCbFsRounds
     in k >= 0 &&
        validBigCbParams params &&
        validBigCommitKey params ck &&
        validBigVec (bigCbM params) cAmount &&
        length bits == k &&
        length comps == k &&
        length amountAs == bigCbFsRounds &&
        length amountZs == bigCbFsRounds &&
        length pairAss == bigCbFsRounds &&
        length pairZss == bigCbFsRounds &&
        all ((== k) . length) pairAss &&
        all ((== k) . length) pairZss &&
        and
          [ bigCrSigmaVerify params ck amountCommit a challenge z
              (validBigCrAmountResponse params gamma k)
          | (a, challenge, z) <- zip3 amountAs challenges amountZs
          ] &&
        and
          [ bigCrSigmaVerify params ck (pairs !! bitIndex) a challenge z
              (validBigCrPairResponse params gamma)
          | (roundAss, challenge, roundZss) <- zip3 pairAss challenges pairZss
          , (bitIndex, a, z) <- zip3 [0 :: Int ..] roundAss roundZss
          ]

validBigNfMask :: BigCbParams -> Integer -> BigOpening -> Bool
validBigNfMask params gamma opening =
    validBigOpeningShape params opening &&
    bigAllBounded (bigOpenMsg opening) gamma &&
    bigAllBounded (bigOpenRand opening) gamma

bigNfResponseBound :: BigCbParams -> Integer -> Int -> Integer
bigNfResponseBound params gamma challenge =
    gamma + toInteger challenge * bigCbBeta params

validBigNfResponse :: BigCbParams -> Integer -> Int -> BigOpening -> Bool
validBigNfResponse params gamma challenge opening =
    (challenge == 0 || challenge == 1) &&
    validBigOpeningShape params opening &&
    bigAllBounded (bigOpenMsg opening) (bigNfResponseBound params gamma challenge) &&
    bigAllBounded (bigOpenRand opening) (bigNfResponseBound params gamma challenge)

bigNfSigmaRespond :: BigOpening -> BigOpening -> Int -> BigOpening
bigNfSigmaRespond opening mask challenge =
    BigOpening
        (bigSigmaRespond (bigOpenMsg opening) (bigOpenMsg mask) challenge)
        (bigSigmaRespond (bigOpenRand opening) (bigOpenRand mask) challenge)

bigNfRelation :: BigCbParams -> [[Integer]] -> [[Integer]] -> [Integer] -> [Integer] -> BigOpening -> Bool
bigNfRelation params ck nk c nf opening =
    validBigCbParams params &&
    validBigCommitKey params ck &&
    validBigCommitKey params nk &&
    validBigVec (bigCbM params) c &&
    validBigVec (bigCbM params) nf &&
    validBigOpening params opening &&
    bigCommit params ck opening == c &&
    bigCommit params nk opening == nf

bigNfFsFields :: [[Integer]] -> [[Integer]] -> [Integer] -> [Integer] -> [[Integer]] -> [[Integer]] -> [Integer]
bigNfFsFields ck nk c nf aCommits aNullifiers =
    [ sum (concat ck)
    , sum (concat nk)
    , sum c
    , sum nf
    , sum (concat aCommits)
    , sum (concat aNullifiers)
    ]

bigNfFsChallenges :: [[Integer]] -> [[Integer]] -> [Integer] -> [Integer] -> [[Integer]] -> [[Integer]] -> Int -> [Int]
bigNfFsChallenges ck nk c nf aCommits aNullifiers rounds =
    let fields = bigNfFsFields ck nk c nf aCommits aNullifiers
     in [bigBinaryFsChallenge bigNfFsDomain fields roundIndex | roundIndex <- [0 .. rounds - 1]]

bigNfSigmaVerify :: BigCbParams -> Integer -> [[Integer]] -> [Integer] -> [Integer] -> Int -> BigOpening -> Bool
bigNfSigmaVerify params gamma key target announcement challenge response =
    validBigCommitKey params key &&
    validBigVec (bigCbM params) target &&
    validBigVec (bigCbM params) announcement &&
    validBigNfResponse params gamma challenge response &&
    bigCommit params key response ==
        bigVecMod (bigVecAdd announcement (bigScalarMult (toInteger challenge) target)) (bigCbQ params)

bigNfFsProve :: BigCbParams -> Integer -> [[Integer]] -> [[Integer]] -> [Integer] -> [Integer] -> BigOpening -> [BigOpening] -> Maybe BigNfProof
bigNfFsProve params gamma ck nk c nf opening masks =
    let aCommits = map (bigCommit params ck) masks
        aNullifiers = map (bigCommit params nk) masks
        challenges = bigNfFsChallenges ck nk c nf aCommits aNullifiers bigCbFsRounds
        responses = zipWith (bigNfSigmaRespond opening) masks challenges
     in if length masks == bigCbFsRounds &&
           bigNfRelation params ck nk c nf opening &&
           all (validBigNfMask params gamma) masks &&
           and (zipWith (validBigNfResponse params gamma) challenges responses)
        then Just (BigNfProof aCommits aNullifiers (map bigOpenMsg responses) (map bigOpenRand responses))
        else Nothing

bigNfFsVerify :: BigCbParams -> Integer -> [[Integer]] -> [[Integer]] -> [Integer] -> [Integer] -> BigNfProof -> Bool
bigNfFsVerify params gamma ck nk c nf proof =
    let aCommits = bigNfACommits proof
        aNullifiers = bigNfANullifiers proof
        zMsgs = bigNfZMsgs proof
        zRands = bigNfZRands proof
        challenges = bigNfFsChallenges ck nk c nf aCommits aNullifiers bigCbFsRounds
        responses = zipWith BigOpening zMsgs zRands
     in validBigCbParams params &&
        validBigCommitKey params ck &&
        validBigCommitKey params nk &&
        validBigVec (bigCbM params) c &&
        validBigVec (bigCbM params) nf &&
        length aCommits == bigCbFsRounds &&
        length aNullifiers == bigCbFsRounds &&
        length zMsgs == bigCbFsRounds &&
        length zRands == bigCbFsRounds &&
        and
          [ bigNfSigmaVerify params gamma ck c aCommit challenge response &&
            bigNfSigmaVerify params gamma nk nf aNullifier challenge response
          | (aCommit, aNullifier, challenge, response) <- zip4 aCommits aNullifiers challenges responses
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

jsonCtMerkleTransactionProof :: ConfidentialTransaction.MerkleTransactionProof -> String
jsonCtMerkleTransactionProof proof =
    jsonObject
        [ ("in1Member", jsonMerkleMembershipProof (ConfidentialTransaction.tx_merkle_in1_member proof))
        , ("in2Member", jsonMerkleMembershipProof (ConfidentialTransaction.tx_merkle_in2_member proof))
        , ("in1Nullifier", jsonCtNullifierProof (ConfidentialTransaction.tx_merkle_in1_nullifier proof))
        , ("in2Nullifier", jsonCtNullifierProof (ConfidentialTransaction.tx_merkle_in2_nullifier proof))
        , ("balance", jsonCbProof (ConfidentialTransaction.tx_merkle_balance proof))
        , ("out1Range", jsonCrProof (ConfidentialTransaction.tx_merkle_out1_range proof))
        , ("out2Range", jsonCrProof (ConfidentialTransaction.tx_merkle_out2_range proof))
        ]

parseCtMerkleMembershipProof :: String -> String -> String -> String -> Maybe ConfidentialTransaction.MerkleMembershipProof
parseCtMerkleMembershipProof indexStr rootDigest siblingsStr directionsStr =
    case (parseCanonicalInt indexStr, parseStringList siblingsStr, parseCanonicalBoolVec01 directionsStr) of
        (Just index, Just siblings, Just directions) ->
            Just (ConfidentialTransaction.makeMerkleMembershipProof index rootDigest siblings directions)
        _ -> Nothing

ctMerkleProofDigestUsage :: String
ctMerkleProofDigestUsage =
    "Usage: ct-merkle-proof-digest IN1_INDEX IN1_ROOT IN1_SIBLINGS IN1_DIRECTIONS IN2_INDEX IN2_ROOT IN2_SIBLINGS IN2_DIRECTIONS IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

ctMerkleProofArgsUsage :: String
ctMerkleProofArgsUsage = drop (length ("Usage: ct-merkle-proof-digest " :: String)) ctMerkleProofDigestUsage

parseCtMerkleProofDigestArgs :: [String] -> Either String ConfidentialTransaction.MerkleTransactionProof
parseCtMerkleProofDigestArgs
    [ in1IndexStr, in1Root, in1SiblingsStr, in1DirectionsStr
    , in2IndexStr, in2Root, in2SiblingsStr, in2DirectionsStr
    , in1ACommitsStr, in1ANullifiersStr, in1ZMsgsStr, in1ZRandsStr
    , in2ACommitsStr, in2ANullifiersStr, in2ZMsgsStr, in2ZRandsStr
    , balanceAStr, balanceZsStr
    , out1BitsStr, out1CompsStr, out1AmountAStr, out1AmountZStr
    , out1PairAsStr, out1PairZsStr
    , out2BitsStr, out2CompsStr, out2AmountAStr, out2AmountZStr
    , out2PairAsStr, out2PairZsStr
    ] =
        case
            ( parseCtMerkleMembershipProof in1IndexStr in1Root in1SiblingsStr in1DirectionsStr
            , parseCtMerkleMembershipProof in2IndexStr in2Root in2SiblingsStr in2DirectionsStr
            , parseCanonicalMat in1ACommitsStr
            , parseCanonicalMat in1ANullifiersStr
            , parseCanonicalMat in1ZMsgsStr
            , parseCanonicalMat in1ZRandsStr
            , parseCanonicalMat in2ACommitsStr
            , parseCanonicalMat in2ANullifiersStr
            , parseCanonicalMat in2ZMsgsStr
            , parseCanonicalMat in2ZRandsStr
            , parseCanonicalMat balanceAStr
            , parseCanonicalMat balanceZsStr
            , parseCanonicalMat out1BitsStr
            , parseCanonicalMat out1CompsStr
            , parseCanonicalMat out1AmountAStr
            , parseCanonicalMat out1AmountZStr
            , parseCanonicalCube out1PairAsStr
            , parseCanonicalCube out1PairZsStr
            , parseCanonicalMat out2BitsStr
            , parseCanonicalMat out2CompsStr
            , parseCanonicalMat out2AmountAStr
            , parseCanonicalMat out2AmountZStr
            , parseCanonicalCube out2PairAsStr
            , parseCanonicalCube out2PairZsStr
            )
        of
            ( Just in1Member
              , Just in2Member
              , Just in1ACommits
              , Just in1ANullifiers
              , Just in1ZMsgs
              , Just in1ZRands
              , Just in2ACommits
              , Just in2ANullifiers
              , Just in2ZMsgs
              , Just in2ZRands
              , Just balanceAs
              , Just balanceZs
              , Just out1Bits
              , Just out1Comps
              , Just out1AmountA
              , Just out1AmountZ
              , Just out1PairAs
              , Just out1PairZs
              , Just out2Bits
              , Just out2Comps
              , Just out2AmountA
              , Just out2AmountZ
              , Just out2PairAs
              , Just out2PairZs
              ) ->
                Right $
                    ConfidentialTransaction.makeMerkleTransactionProof
                        in1Member
                        in2Member
                        (ConfidentialTransaction.makeNullifierProof in1ACommits in1ANullifiers in1ZMsgs in1ZRands)
                        (ConfidentialTransaction.makeNullifierProof in2ACommits in2ANullifiers in2ZMsgs in2ZRands)
                        (ConfidentialBalance.makeBalanceProof balanceAs balanceZs)
                        (ConfidentialRange.makeRangeProof out1Bits out1Comps out1AmountA out1AmountZ out1PairAs out1PairZs)
                        (ConfidentialRange.makeRangeProof out2Bits out2Comps out2AmountA out2AmountZ out2PairAs out2PairZs)
            _ -> Left "Expected Merkle membership and transaction-proof fields"
parseCtMerkleProofDigestArgs _ =
    Left ctMerkleProofDigestUsage

ctBignumMerkleProofDigestUsage :: String
ctBignumMerkleProofDigestUsage =
    "Usage: ct-bignum-merkle-proof-digest IN1_INDEX IN1_ROOT IN1_SIBLINGS IN1_DIRECTIONS IN2_INDEX IN2_ROOT IN2_SIBLINGS IN2_DIRECTIONS IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

ctBignumMerkleProofArgsUsage :: String
ctBignumMerkleProofArgsUsage =
    drop (length ("Usage: ct-bignum-merkle-proof-digest " :: String)) ctBignumMerkleProofDigestUsage

parseCtBignumMerkleProofDigestArgs :: [String] -> Either String BigMerkleTransactionProof
parseCtBignumMerkleProofDigestArgs
    [ in1IndexStr
      , in1Root
      , in1SiblingsStr
      , in1DirectionsStr
      , in2IndexStr
      , in2Root
      , in2SiblingsStr
      , in2DirectionsStr
      , in1ACommitsStr
      , in1ANullifiersStr
      , in1ZMsgsStr
      , in1ZRandsStr
      , in2ACommitsStr
      , in2ANullifiersStr
      , in2ZMsgsStr
      , in2ZRandsStr
      , balanceAsStr
      , balanceZsStr
      , out1BitsStr
      , out1CompsStr
      , out1AmountAsStr
      , out1AmountZsStr
      , out1PairAssStr
      , out1PairZssStr
      , out2BitsStr
      , out2CompsStr
      , out2AmountAsStr
      , out2AmountZsStr
      , out2PairAssStr
      , out2PairZssStr
      ] =
        case
            ( parseCtMerkleMembershipProof in1IndexStr in1Root in1SiblingsStr in1DirectionsStr
            , parseCtMerkleMembershipProof in2IndexStr in2Root in2SiblingsStr in2DirectionsStr
            , parseCanonicalIntegerMat in1ACommitsStr
            , parseCanonicalIntegerMat in1ANullifiersStr
            , parseCanonicalIntegerMat in1ZMsgsStr
            , parseCanonicalIntegerMat in1ZRandsStr
            , parseCanonicalIntegerMat in2ACommitsStr
            , parseCanonicalIntegerMat in2ANullifiersStr
            , parseCanonicalIntegerMat in2ZMsgsStr
            , parseCanonicalIntegerMat in2ZRandsStr
            , parseCanonicalIntegerMat balanceAsStr
            , parseCanonicalIntegerMat balanceZsStr
            , parseCanonicalIntegerMat out1BitsStr
            , parseCanonicalIntegerMat out1CompsStr
            , parseCanonicalIntegerMat out1AmountAsStr
            , parseCanonicalIntegerMat out1AmountZsStr
            , parseCanonicalIntegerCube out1PairAssStr
            , parseCanonicalIntegerCube out1PairZssStr
            , parseCanonicalIntegerMat out2BitsStr
            , parseCanonicalIntegerMat out2CompsStr
            , parseCanonicalIntegerMat out2AmountAsStr
            , parseCanonicalIntegerMat out2AmountZsStr
            , parseCanonicalIntegerCube out2PairAssStr
            , parseCanonicalIntegerCube out2PairZssStr
            )
        of
            ( Just in1Member
              , Just in2Member
              , Just in1ACommits
              , Just in1ANullifiers
              , Just in1ZMsgs
              , Just in1ZRands
              , Just in2ACommits
              , Just in2ANullifiers
              , Just in2ZMsgs
              , Just in2ZRands
              , Just balanceAs
              , Just balanceZs
              , Just out1Bits
              , Just out1Comps
              , Just out1AmountAs
              , Just out1AmountZs
              , Just out1PairAss
              , Just out1PairZss
              , Just out2Bits
              , Just out2Comps
              , Just out2AmountAs
              , Just out2AmountZs
              , Just out2PairAss
              , Just out2PairZss
              ) ->
                Right
                    BigMerkleTransactionProof
                        { bigTxIn1Member = in1Member
                        , bigTxIn2Member = in2Member
                        , bigTxIn1Nullifier =
                            BigNfProof in1ACommits in1ANullifiers in1ZMsgs in1ZRands
                        , bigTxIn2Nullifier =
                            BigNfProof in2ACommits in2ANullifiers in2ZMsgs in2ZRands
                        , bigTxBalance = BigCbProof balanceAs balanceZs
                        , bigTxOut1Range =
                            BigCrProof out1Bits out1Comps out1AmountAs out1AmountZs out1PairAss out1PairZss
                        , bigTxOut2Range =
                            BigCrProof out2Bits out2Comps out2AmountAs out2AmountZs out2PairAss out2PairZss
                        }
            _ -> Left "Expected bignum Merkle membership and transaction-proof fields"
parseCtBignumMerkleProofDigestArgs _ =
    Left ctBignumMerkleProofDigestUsage

parseCbParams :: String -> String -> String -> String -> Maybe Commit.CommitParams
parseCbParams mStr n2Str qStr betaStr =
    case (parseInt mStr, parseInt n2Str, parseInt qStr, parseInt betaStr) of
        (Just m, Just n2, Just q, Just beta) ->
            Just (ConfidentialBalance.makeScalarCommitParams m n2 q beta)
        _ -> Nothing

parseCanonicalCbParams :: String -> String -> String -> String -> Maybe Commit.CommitParams
parseCanonicalCbParams mStr n2Str qStr betaStr =
    case (parseCanonicalInt mStr, parseCanonicalInt n2Str, parseCanonicalInt qStr, parseCanonicalInt betaStr) of
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

ctVerifyUsage :: String -> String
ctVerifyUsage command =
    "Usage: " ++ command ++ " M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

ctProveUsage :: String -> String
ctProveUsage command =
    "Usage: " ++ command ++ " M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS"

ctVerifyBenchUsage :: String -> String
ctVerifyBenchUsage command =
    "Usage: " ++ command ++ " ITERATIONS WARMUP M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

prepareCtVerifyWithUsage :: String -> [String] -> Either String (() -> Bool)
prepareCtVerifyWithUsage command [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, ledgerStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1ACommitsStr, in1ANullifiersStr, in1ZMsgsStr, in1ZRandsStr, in2ACommitsStr, in2ANullifiersStr, in2ZMsgsStr, in2ZRandsStr, balanceAStr, balanceZsStr, out1BitsStr, out1CompsStr, out1AmountAStr, out1AmountZStr, out1PairAsStr, out1PairZsStr, out2BitsStr, out2CompsStr, out2AmountAStr, out2AmountZStr, out2PairAsStr, out2PairZsStr] =
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
prepareCtVerifyWithUsage command _ =
    Left (ctVerifyUsage command)

prepareCtVerifyScaffold :: [String] -> Either String (() -> Bool)
prepareCtVerifyScaffold = prepareCtVerifyWithUsage "ct-verify-scaffold"

prepareCtVerifyMerkleWithRoot :: Maybe String -> Maybe Int -> Maybe Int -> [String] -> Either String (() -> Bool)
prepareCtVerifyMerkleWithRoot rootOverride publicFeeOverride rootDepthOverride
    ( mStr : n2Str : qStr : betaStr : gammaStr : kStr : ckStr : nkStr
      : ledgerStr : spentStr : cIn1Str : cIn2Str : cOut1Str : cOut2Str
      : nf1Str : nf2Str : proofArgs
    ) =
    case
        ( parseCanonicalCbParams mStr n2Str qStr betaStr
        , parseCanonicalInt gammaStr
        , parseCanonicalInt kStr
        , parseCanonicalMat ckStr
        , parseCanonicalMat nkStr
        , parseCanonicalMat ledgerStr
        , parseCanonicalMat spentStr
        , parseCanonicalVec cIn1Str
        , parseCanonicalVec cIn2Str
        , parseCanonicalVec cOut1Str
        , parseCanonicalVec cOut2Str
        , parseCanonicalVec nf1Str
        , parseCanonicalVec nf2Str
        , parseCtMerkleProofDigestArgs proofArgs
        ) of
        ( Just params
          , Just gamma
          , Just k
          , Just ck
          , Just nk
          , Just ledger
          , Just spent
          , Just cIn1
          , Just cIn2
          , Just cOut1
          , Just cOut2
          , Just nf1
          , Just nf2
          , Right proof
          ) ->
            let root = maybe (ConfidentialTransaction.merkleLedgerRoot ledger) id rootOverride
                in1Depth =
                    length (ConfidentialTransaction.merkleMemberSiblings (ConfidentialTransaction.tx_merkle_in1_member proof))
                in2Depth =
                    length (ConfidentialTransaction.merkleMemberSiblings (ConfidentialTransaction.tx_merkle_in2_member proof))
                depthOk =
                    maybe
                        True
                        (\rootDepth -> in1Depth == rootDepth && in2Depth == rootDepth)
                        rootDepthOverride
             in Right
                    (\() ->
                        depthOk
                            && case publicFeeOverride of
                                Nothing ->
                                    ConfidentialTransaction.transactionFsVerifyMerkle
                                        params gamma k ck nk root spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof
                                Just publicFee ->
                                    ConfidentialTransaction.transactionFsVerifyMerkleFee
                                        params gamma k ck nk root spent publicFee cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof)
        _ -> Left "Expected params, keys, ledger, commitments, nullifiers, and transaction-proof fields"
prepareCtVerifyMerkleWithRoot _ _ _ _ =
    Left ("Usage: ct-verify-merkle M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 " ++ ctMerkleProofArgsUsage)

prepareCtVerifyMerkle :: [String] -> Either String (() -> Bool)
prepareCtVerifyMerkle = prepareCtVerifyMerkleWithRoot Nothing Nothing Nothing

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

cmdCbSampleMask :: OutputFormat -> [String] -> IO ()
cmdCbSampleMask format [mStr, n2Str, qStr, betaStr, gammaStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr) of
        (Just params, Just gamma) ->
            outputSampleResult format
                (outputVecResult format "sample_balance_mask = ")
                (ConfidentialBalance.sampleMask params gamma)
        _ -> outputError format "Expected params (M N2 Q BETA) and gamma"
cmdCbSampleMask format _ = outputUsage format "Usage: cb-sample-mask M N2 Q BETA GAMMA"

cmdCbSampleMasks :: OutputFormat -> [String] -> IO ()
cmdCbSampleMasks format [mStr, n2Str, qStr, betaStr, gammaStr, roundsStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr, parseInt roundsStr) of
        (Just params, Just gamma, Just rounds) ->
            outputSampleResult format
                (outputMatResult format "sample_balance_masks = ")
                (ConfidentialBalance.sampleMasks params gamma rounds)
        _ -> outputError format "Expected params (M N2 Q BETA), gamma, and rounds"
cmdCbSampleMasks format _ = outputUsage format "Usage: cb-sample-masks M N2 Q BETA GAMMA ROUNDS"

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

cmdCtBalanceBigintRandCommit :: OutputFormat -> [String] -> IO ()
cmdCtBalanceBigintRandCommit format [mStr, n2Str, qStr, betaStr, ckStr, rStr] =
    case (parseBigCbParams mStr n2Str qStr betaStr, parseCanonicalIntegerMat ckStr, parseCanonicalIntegerVec rStr) of
        (Just params, Just ck, Just r)
            | validBigCommitKey params ck && validBigVec (bigCbN2 params) r ->
                case format of
                    Human -> putStrLn $ "ct_balance_bigint_rand_commit = " ++ show (bigRandCommit params ck r)
                    Json -> putStrLn $ "{\"result\":" ++ jsonIntegerVec (bigRandCommit params ck r) ++ "}"
        _ -> outputError format "Expected params (M N2 Q BETA), BigInt commitment key matrix, and witness vector"
cmdCtBalanceBigintRandCommit format _ =
    outputUsage format "Usage: ct-balance-bigint-rand-commit M N2 Q BETA \"[[row1],[row2]]\" \"[r]\""

cmdCtBalanceBigintFsFields :: OutputFormat -> [String] -> IO ()
cmdCtBalanceBigintFsFields format [ckStr, cStr, asStr] =
    case (parseCanonicalIntegerMat ckStr, parseCanonicalIntegerVec cStr, parseCanonicalIntegerMat asStr) of
        (Just ck, Just c, Just as_) ->
            case format of
                Human -> putStrLn $ "ct_balance_bigint_fs_fields = " ++ show (bigFsFields ck c as_)
                Json -> putStrLn $ "{\"result\":" ++ jsonIntegerVec (bigFsFields ck c as_) ++ "}"
        _ -> outputError format "Expected BigInt commitment key matrix, commitment vector, and announcement matrix"
cmdCtBalanceBigintFsFields format _ =
    outputUsage format "Usage: ct-balance-bigint-fs-fields \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\""

cmdCtBalanceBigintFsChallenges :: OutputFormat -> [String] -> IO ()
cmdCtBalanceBigintFsChallenges format [mStr, n2Str, qStr, betaStr, ckStr, cStr, asStr, roundsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerMat asStr
        , parseCanonicalInt roundsStr
        )
    of
        (Just params, Just ck, Just c, Just as_, Just rounds)
            | validBigCbParams params && validBigCommitKey params ck && validBigVec (bigCbM params) c && rounds >= 0 ->
                outputVecResult format "ct_balance_bigint_fs_challenges = "
                    (bigFsChallenges ck c as_ rounds)
        _ -> outputError format "Expected params, BigInt commitment key matrix, commitment vector, announcement matrix, and round count"
cmdCtBalanceBigintFsChallenges format _ =
    outputUsage format "Usage: ct-balance-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\" ROUNDS"

cmdCtBalanceBigintProve :: OutputFormat -> [String] -> IO ()
cmdCtBalanceBigintProve format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, cStr, rStr, ysStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerVec rStr
        , parseCanonicalIntegerMat ysStr
        )
    of
        (Just params, Just gamma, Just ck, Just c, Just r, Just ys) ->
            case bigFsProve params gamma ck c r ys of
                Just proof ->
                    case format of
                        Human -> putStrLn $ "ct_balance_bigint_proof = " ++ show (bigCbAs proof, bigCbZs proof)
                        Json -> putStrLn $ "{\"result\":" ++ jsonBigCbProof proof ++ "}"
                Nothing ->
                    case format of
                        Human -> putStrLn "ct_balance_bigint_proof = null"
                        Json -> putStrLn "{\"result\":null}"
        _ -> outputError format "Expected params, gamma, BigInt commitment key matrix, commitment vector, witness vector, and mask matrix"
cmdCtBalanceBigintProve format _ =
    outputUsage format "Usage: ct-balance-bigint-prove M N2 Q BETA GAMMA \"[[ck]]\" \"[c]\" \"[r]\" \"[[y1],[y2],...]\""

cmdCtBalanceBigintVerify :: OutputFormat -> [String] -> IO ()
cmdCtBalanceBigintVerify format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, cStr, asStr, zsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerMat asStr
        , parseCanonicalIntegerMat zsStr
        )
    of
        (Just params, Just gamma, Just ck, Just c, Just as_, Just zs) ->
            outputBoolResult format "ct_balance_bigint_verify = "
                (bigFsVerify params gamma ck c (BigCbProof as_ zs))
        _ -> outputError format "Expected params, gamma, BigInt commitment key matrix, commitment vector, announcement matrix, and response matrix"
cmdCtBalanceBigintVerify format _ =
    outputUsage format "Usage: ct-balance-bigint-verify M N2 Q BETA GAMMA \"[[ck]]\" \"[c]\" \"[[a1],[a2],...]\" \"[[z1],[z2],...]\""

makeBigScalarOpenings :: [Integer] -> [[Integer]] -> Maybe [BigOpening]
makeBigScalarOpenings values rands
  | length values == length rands = Just (zipWith (\value rand -> bigOpening [value] rand) values rands)
  | otherwise = Nothing

cmdCtRangeBigintFsFields :: OutputFormat -> [String] -> IO ()
cmdCtRangeBigintFsFields format [ckStr, cAmountStr, bitsStr, compsStr, amountAsStr, pairAssStr] =
    case
        ( parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cAmountStr
        , parseCanonicalIntegerMat bitsStr
        , parseCanonicalIntegerMat compsStr
        , parseCanonicalIntegerMat amountAsStr
        , parseCanonicalIntegerCube pairAssStr
        )
    of
        (Just ck, Just cAmount, Just bits, Just comps, Just amountAs, Just pairAss) ->
            case format of
                Human -> putStrLn $ "ct_range_bigint_fs_fields = " ++ show (bigCrFsFields ck cAmount bits comps amountAs pairAss)
                Json -> putStrLn $ "{\"result\":" ++ jsonIntegerVec (bigCrFsFields ck cAmount bits comps amountAs pairAss) ++ "}"
        _ -> outputError format "Expected BigInt commitment key, amount commitment, bit commitments, complement commitments, amount announcements, and pair announcements"
cmdCtRangeBigintFsFields format _ =
    outputUsage format "Usage: ct-range-bigint-fs-fields \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[[pairAss]]]\""

cmdCtRangeBigintFsChallenges :: OutputFormat -> [String] -> IO ()
cmdCtRangeBigintFsChallenges format [mStr, n2Str, qStr, betaStr, ckStr, cAmountStr, bitsStr, compsStr, amountAsStr, pairAssStr, roundsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cAmountStr
        , parseCanonicalIntegerMat bitsStr
        , parseCanonicalIntegerMat compsStr
        , parseCanonicalIntegerMat amountAsStr
        , parseCanonicalIntegerCube pairAssStr
        , parseCanonicalInt roundsStr
        )
    of
        (Just params, Just ck, Just cAmount, Just bits, Just comps, Just amountAs, Just pairAss, Just rounds)
            | validBigCbParams params && validBigCommitKey params ck && validBigVec (bigCbM params) cAmount && rounds >= 0 ->
                outputVecResult format "ct_range_bigint_fs_challenges = "
                    (bigCrFsChallenges ck cAmount bits comps amountAs pairAss rounds)
        _ -> outputError format "Expected params, BigInt range transcript fields, and round count"
cmdCtRangeBigintFsChallenges format _ =
    outputUsage format "Usage: ct-range-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[[pairAss]]]\" ROUNDS"

cmdCtRangeBigintProve :: OutputFormat -> [String] -> IO ()
cmdCtRangeBigintProve format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, cAmountStr, amountStr, amountRandStr, bitsStr, bitRandsStr, compsStr, compRandsStr, yAmountsStr, yPairssStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalInt kStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cAmountStr
        , parseCanonicalInteger amountStr
        , parseCanonicalIntegerVec amountRandStr
        , parseCanonicalIntegerVec bitsStr
        , parseCanonicalIntegerMat bitRandsStr
        , parseCanonicalIntegerVec compsStr
        , parseCanonicalIntegerMat compRandsStr
        , parseCanonicalIntegerMat yAmountsStr
        , parseCanonicalIntegerCube yPairssStr
        )
    of
        (Just params, Just gamma, Just k, Just ck, Just cAmount, Just amount, Just amountRand, Just bits, Just bitRands, Just comps, Just compRands, Just yAmounts, Just yPairss) ->
            case (makeBigScalarOpenings bits bitRands, makeBigScalarOpenings comps compRands) of
                (Just bitOpenings, Just compOpenings) ->
                    case bigCrFsProve params gamma k ck cAmount (bigOpening [amount] amountRand) bitOpenings compOpenings yAmounts yPairss of
                        Just proof ->
                            case format of
                                Human -> putStrLn $ "ct_range_bigint_proof = " ++ jsonBigCrProof proof
                                Json -> putStrLn $ "{\"result\":" ++ jsonBigCrProof proof ++ "}"
                        Nothing ->
                            case format of
                                Human -> putStrLn "ct_range_bigint_proof = null"
                                Json -> putStrLn "{\"result\":null}"
                _ -> outputError format "Bit/complement counts must match their randomness matrices"
        _ -> outputError format "Expected params, gamma, BigInt commitment key, amount opening, bit openings, complement openings, and masks"
cmdCtRangeBigintProve format _ =
    outputUsage format "Usage: ct-range-bigint-prove M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" AMOUNT \"[amountRand]\" \"[bits]\" \"[[bitRands]]\" \"[comps]\" \"[[compRands]]\" \"[[yAmounts]]\" \"[[[yPairss]]]\""

cmdCtRangeBigintVerify :: OutputFormat -> [String] -> IO ()
cmdCtRangeBigintVerify format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, cAmountStr, bitsStr, compsStr, amountAsStr, amountZsStr, pairAssStr, pairZssStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalInt kStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerVec cAmountStr
        , parseCanonicalIntegerMat bitsStr
        , parseCanonicalIntegerMat compsStr
        , parseCanonicalIntegerMat amountAsStr
        , parseCanonicalIntegerMat amountZsStr
        , parseCanonicalIntegerCube pairAssStr
        , parseCanonicalIntegerCube pairZssStr
        )
    of
        (Just params, Just gamma, Just k, Just ck, Just cAmount, Just bits, Just comps, Just amountAs, Just amountZs, Just pairAss, Just pairZss) ->
            outputBoolResult format "ct_range_bigint_verify = "
                (bigCrFsVerify params gamma k ck cAmount (BigCrProof bits comps amountAs amountZs pairAss pairZss))
        _ -> outputError format "Expected params, gamma, BigInt commitment key, amount commitment, and proof fields"
cmdCtRangeBigintVerify format _ =
    outputUsage format "Usage: ct-range-bigint-verify M N2 Q BETA GAMMA K \"[[ck]]\" \"[cAmount]\" \"[[bits]]\" \"[[comps]]\" \"[[amountAs]]\" \"[[amountZs]]\" \"[[[pairAss]]]\" \"[[[pairZss]]]\""

cmdCtNullifierBigint :: OutputFormat -> [String] -> IO ()
cmdCtNullifierBigint format [mStr, n2Str, qStr, betaStr, nkStr, amountStr, randStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalIntegerMat nkStr
        , parseCanonicalInteger amountStr
        , parseCanonicalIntegerVec randStr
        )
    of
        (Just params, Just nk, Just amount, Just rand)
            | validBigCommitKey params nk && validBigOpening params (bigOpening [amount] rand) ->
                let result = bigCommit params nk (bigOpening [amount] rand)
                 in case format of
                        Human -> putStrLn $ "ct_nullifier_bigint = " ++ show result
                        Json -> putStrLn $ "{\"result\":" ++ jsonIntegerVec result ++ "}"
        _ -> outputError format "Expected params, BigInt nullifier key, scalar amount, and randomness vector"
cmdCtNullifierBigint format _ =
    outputUsage format "Usage: ct-nullifier-bigint M N2 Q BETA \"[[nk]]\" AMOUNT \"[rand]\""

cmdCtNullifierBigintFsFields :: OutputFormat -> [String] -> IO ()
cmdCtNullifierBigintFsFields format [ckStr, nkStr, cStr, nfStr, aCommitsStr, aNullifiersStr] =
    case
        ( parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerMat nkStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerVec nfStr
        , parseCanonicalIntegerMat aCommitsStr
        , parseCanonicalIntegerMat aNullifiersStr
        )
    of
        (Just ck, Just nk, Just c, Just nf, Just aCommits, Just aNullifiers) ->
            case format of
                Human -> putStrLn $ "ct_nullifier_bigint_fs_fields = " ++ show (bigNfFsFields ck nk c nf aCommits aNullifiers)
                Json -> putStrLn $ "{\"result\":" ++ jsonIntegerVec (bigNfFsFields ck nk c nf aCommits aNullifiers) ++ "}"
        _ -> outputError format "Expected BigInt keys, commitment, nullifier, commitment announcements, and nullifier announcements"
cmdCtNullifierBigintFsFields format _ =
    outputUsage format "Usage: ct-nullifier-bigint-fs-fields \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\""

cmdCtNullifierBigintFsChallenges :: OutputFormat -> [String] -> IO ()
cmdCtNullifierBigintFsChallenges format [mStr, n2Str, qStr, betaStr, ckStr, nkStr, cStr, nfStr, aCommitsStr, aNullifiersStr, roundsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerMat nkStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerVec nfStr
        , parseCanonicalIntegerMat aCommitsStr
        , parseCanonicalIntegerMat aNullifiersStr
        , parseCanonicalInt roundsStr
        )
    of
        (Just params, Just ck, Just nk, Just c, Just nf, Just aCommits, Just aNullifiers, Just rounds)
            | validBigCbParams params &&
              validBigCommitKey params ck &&
              validBigCommitKey params nk &&
              validBigVec (bigCbM params) c &&
              validBigVec (bigCbM params) nf &&
              rounds >= 0 ->
                outputVecResult format "ct_nullifier_bigint_fs_challenges = "
                    (bigNfFsChallenges ck nk c nf aCommits aNullifiers rounds)
        _ -> outputError format "Expected params, BigInt nullifier transcript fields, and round count"
cmdCtNullifierBigintFsChallenges format _ =
    outputUsage format "Usage: ct-nullifier-bigint-fs-challenges M N2 Q BETA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" ROUNDS"

cmdCtNullifierBigintProve :: OutputFormat -> [String] -> IO ()
cmdCtNullifierBigintProve format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, nkStr, cStr, nfStr, amountStr, randStr, yMsgsStr, yRandsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerMat nkStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerVec nfStr
        , parseCanonicalInteger amountStr
        , parseCanonicalIntegerVec randStr
        , parseCanonicalIntegerVec yMsgsStr
        , parseCanonicalIntegerMat yRandsStr
        )
    of
        (Just params, Just gamma, Just ck, Just nk, Just c, Just nf, Just amount, Just rand, Just yMsgs, Just yRands) ->
            case makeBigScalarOpenings yMsgs yRands of
                Just masks ->
                    case bigNfFsProve params gamma ck nk c nf (bigOpening [amount] rand) masks of
                        Just proof ->
                            case format of
                                Human -> putStrLn $ "ct_nullifier_bigint_proof = " ++ jsonBigNfProof proof
                                Json -> putStrLn $ "{\"result\":" ++ jsonBigNfProof proof ++ "}"
                        Nothing ->
                            case format of
                                Human -> putStrLn "ct_nullifier_bigint_proof = null"
                                Json -> putStrLn "{\"result\":null}"
                Nothing -> outputError format "Nullifier-mask counts must match their randomness matrices"
        _ -> outputError format "Expected params, gamma, BigInt keys, commitment, nullifier, opening, and masks"
cmdCtNullifierBigintProve format _ =
    outputUsage format "Usage: ct-nullifier-bigint-prove M N2 Q BETA GAMMA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" AMOUNT \"[rand]\" \"[yMsgs]\" \"[[yRands]]\""

cmdCtNullifierBigintVerify :: OutputFormat -> [String] -> IO ()
cmdCtNullifierBigintVerify format [mStr, n2Str, qStr, betaStr, gammaStr, ckStr, nkStr, cStr, nfStr, aCommitsStr, aNullifiersStr, zMsgsStr, zRandsStr] =
    case
        ( parseBigCbParams mStr n2Str qStr betaStr
        , parseCanonicalInteger gammaStr
        , parseCanonicalIntegerMat ckStr
        , parseCanonicalIntegerMat nkStr
        , parseCanonicalIntegerVec cStr
        , parseCanonicalIntegerVec nfStr
        , parseCanonicalIntegerMat aCommitsStr
        , parseCanonicalIntegerMat aNullifiersStr
        , parseCanonicalIntegerMat zMsgsStr
        , parseCanonicalIntegerMat zRandsStr
        )
    of
        (Just params, Just gamma, Just ck, Just nk, Just c, Just nf, Just aCommits, Just aNullifiers, Just zMsgs, Just zRands) ->
            outputBoolResult format "ct_nullifier_bigint_verify = "
                (bigNfFsVerify params gamma ck nk c nf (BigNfProof aCommits aNullifiers zMsgs zRands))
        _ -> outputError format "Expected params, gamma, BigInt keys, commitment, nullifier, and proof fields"
cmdCtNullifierBigintVerify format _ =
    outputUsage format "Usage: ct-nullifier-bigint-verify M N2 Q BETA GAMMA \"[[ck]]\" \"[[nk]]\" \"[c]\" \"[nf]\" \"[[aCommits]]\" \"[[aNullifiers]]\" \"[[zMsgs]]\" \"[[zRands]]\""

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

cmdCtMerkleLeaf :: OutputFormat -> [String] -> IO ()
cmdCtMerkleLeaf format [commitmentStr] =
    case parseVec commitmentStr of
        Just commitment -> outputStringResult format "ct_merkle_leaf = " (ConfidentialMerkle.leaf commitment)
        Nothing -> outputError format "Expected commitment vector"
cmdCtMerkleLeaf format _ =
    outputUsage format "Usage: ct-merkle-leaf \"[commitment]\""

cmdCtMerkleEmpty :: OutputFormat -> [String] -> IO ()
cmdCtMerkleEmpty format [widthStr] =
    case parseInt widthStr of
        Just width
            | width >= 0 -> outputStringResult format "ct_merkle_empty = " (ConfidentialMerkle.empty width)
        _ -> outputError format "Expected non-negative width"
cmdCtMerkleEmpty format _ =
    outputUsage format "Usage: ct-merkle-empty WIDTH"

cmdCtMerkleNode :: OutputFormat -> [String] -> IO ()
cmdCtMerkleNode format [left, right] =
    outputStringResult format "ct_merkle_node = " (ConfidentialMerkle.node left right)
cmdCtMerkleNode format _ =
    outputUsage format "Usage: ct-merkle-node LEFT_DIGEST RIGHT_DIGEST"

cmdCtMerkleRoot :: OutputFormat -> [String] -> IO ()
cmdCtMerkleRoot format [ledgerStr] =
    case parseMat ledgerStr of
        Just ledger -> outputStringResult format "ct_merkle_root = " (ConfidentialMerkle.root ledger)
        Nothing -> outputError format "Expected ledger matrix"
cmdCtMerkleRoot format _ =
    outputUsage format "Usage: ct-merkle-root \"[[commitment],...]\""

cmdCtMerkleMemberProve :: OutputFormat -> [String] -> IO ()
cmdCtMerkleMemberProve format [ledgerStr, commitmentStr] =
    case (parseMat ledgerStr, parseVec commitmentStr) of
        (Just ledger, Just commitment) ->
            case ConfidentialMerkle.membershipProve ledger commitment of
                Just proof ->
                    case format of
                        Human -> putStrLn $ "ct_merkle_membership_proof = " ++ show proof
                        Json -> putStrLn $ jsonMerkleMembershipProof proof
                Nothing ->
                    case format of
                        Human -> putStrLn "ct_merkle_membership_proof = null"
                        Json -> putStrLn "null"
        _ -> outputError format "Expected ledger matrix and commitment vector"
cmdCtMerkleMemberProve format _ =
    outputUsage format "Usage: ct-merkle-member-prove \"[[commitment],...]\" \"[commitment]\""

cmdCtMerkleMemberVerify :: OutputFormat -> [String] -> IO ()
cmdCtMerkleMemberVerify format [ledgerStr, commitmentStr] =
    case (parseMat ledgerStr, parseVec commitmentStr) of
        (Just ledger, Just commitment) ->
            outputBoolResult format "ct_merkle_membership_verify = "
                (case ConfidentialMerkle.membershipProve ledger commitment of
                    Just proof -> ConfidentialMerkle.membershipVerify commitment proof
                    Nothing -> False)
        _ -> outputError format "Expected ledger matrix and commitment vector"
cmdCtMerkleMemberVerify format _ =
    outputUsage format "Usage: ct-merkle-member-verify \"[[commitment],...]\" \"[commitment]\""

cmdCtBignumEncode :: OutputFormat -> [String] -> IO ()
cmdCtBignumEncode format [valueStr] =
    case parseCanonicalInteger valueStr of
        Just value ->
            outputStringResult format "ct_bignum_encode = " $
                bignumHex (encodeBignumInteger value)
        Nothing -> outputError format "Expected canonical decimal integer"
cmdCtBignumEncode format _ =
    outputUsage format "Usage: ct-bignum-encode INTEGER"

cmdCtBignumVectorEncode :: OutputFormat -> [String] -> IO ()
cmdCtBignumVectorEncode format valueStrs =
    case traverse parseCanonicalInteger valueStrs of
        Just values ->
            outputStringResult format "ct_bignum_vector_encode = " $
                bignumHex (encodeBignumIntegerVector values)
        Nothing -> outputError format "Expected canonical decimal integers"

cmdCtBignumMerkleLeaf :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleLeaf format [commitmentStr] =
    case parseCanonicalIntegerVec commitmentStr of
        Just commitment ->
            let digest = bignumMerkleLeaf commitment
             in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_leaf = ")
                    `catch` handleSampleError format
        Nothing -> outputError format "Expected canonical bignum commitment vector"
cmdCtBignumMerkleLeaf format _ =
    outputUsage format "Usage: ct-bignum-merkle-leaf \"[commitment]\""

cmdCtBignumMerkleEmpty :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleEmpty format [widthStr] =
    case parseCanonicalInt widthStr of
        Just width ->
            let digest = bignumMerkleEmpty width
             in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_empty = ")
                    `catch` handleSampleError format
        Nothing -> outputError format "Expected non-negative width"
cmdCtBignumMerkleEmpty format _ =
    outputUsage format "Usage: ct-bignum-merkle-empty WIDTH"

cmdCtBignumMerkleNode :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleNode format [left, right] =
    let digest = bignumMerkleNode left right
     in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_node = ")
            `catch` handleSampleError format
cmdCtBignumMerkleNode format _ =
    outputUsage format "Usage: ct-bignum-merkle-node LEFT_DIGEST RIGHT_DIGEST"

cmdCtBignumMerkleRoot :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleRoot format [ledgerStr] =
    case parseCanonicalIntegerMat ledgerStr of
        Just ledger ->
            let digest = bignumMerkleRoot ledger
             in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_root = ")
                    `catch` handleSampleError format
        Nothing -> outputError format "Expected canonical bignum ledger matrix"
cmdCtBignumMerkleRoot format _ =
    outputUsage format "Usage: ct-bignum-merkle-root \"[[commitment],...]\""

cmdCtBignumMerkleMemberProve :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleMemberProve format [ledgerStr, commitmentStr] =
    case (parseCanonicalIntegerMat ledgerStr, parseCanonicalIntegerVec commitmentStr) of
        (Just ledger, Just commitment) ->
            let proof = bignumMerkleMembershipProve ledger commitment
             in case proof of
                  Just value ->
                    case format of
                      Human -> putStrLn $ "ct_bignum_merkle_membership_proof = " ++ jsonMerkleMembershipProof value
                      Json -> putStrLn $ jsonMerkleMembershipProof value
                  Nothing ->
                    case format of
                      Human -> putStrLn "ct_bignum_merkle_membership_proof = null"
                      Json -> putStrLn "null"
        _ -> outputError format "Expected canonical bignum ledger matrix and commitment vector"
cmdCtBignumMerkleMemberProve format _ =
    outputUsage format "Usage: ct-bignum-merkle-member-prove \"[[commitment],...]\" \"[commitment]\""

cmdCtBignumMerkleMemberVerify :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleMemberVerify format [ledgerStr, commitmentStr] =
    case (parseCanonicalIntegerMat ledgerStr, parseCanonicalIntegerVec commitmentStr) of
        (Just ledger, Just commitment) ->
            outputBoolResult format "ct_bignum_merkle_membership_verify = " $
              case bignumMerkleMembershipProve ledger commitment of
                Just proof -> bignumMerkleMembershipVerify commitment proof
                Nothing -> False
        _ -> outputError format "Expected canonical bignum ledger matrix and commitment vector"
cmdCtBignumMerkleMemberVerify format _ =
    outputUsage format "Usage: ct-bignum-merkle-member-verify \"[[commitment],...]\" \"[commitment]\""

cmdCtBignumTransactionContext :: OutputFormat -> [String] -> IO ()
cmdCtBignumTransactionContext format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootDigest
    , rootDepthStr
    , publicFeeStr
    , cIn1Str
    , cIn2Str
    , cOut1Str
    , cOut2Str
    , nf1Str
    , nf2Str
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseCanonicalInt rootDepthStr
        , parseCanonicalInteger publicFeeStr
        , parseCanonicalIntegerVec cIn1Str
        , parseCanonicalIntegerVec cIn2Str
        , parseCanonicalIntegerVec cOut1Str
        , parseCanonicalIntegerVec cOut2Str
        , parseCanonicalIntegerVec nf1Str
        , parseCanonicalIntegerVec nf2Str
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just rootDepth
          , Just publicFee
          , Just cIn1
          , Just cIn2
          , Just cOut1
          , Just cOut2
          , Just nf1
          , Just nf2
          ) ->
            let digest =
                  bignumTransactionContextDigest
                    protocolVersion networkId assetId ledgerEpoch rootDigest rootDepth publicFee
                    cIn1 cIn2 cOut1 cOut2 nf1 nf2
             in (evaluate digest >>= outputStringResult format "ct_bignum_transaction_context = ")
                    `catch` handleSampleError format
        _ -> outputError format "Expected bignum transaction context fields"
cmdCtBignumTransactionContext format _ =
    outputUsage format "Usage: ct-bignum-transaction-context VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2"

cmdCtBignumMerkleProofDigest :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleProofDigest format args =
    case parseCtBignumMerkleProofDigestArgs args of
        Right proof ->
            let digest = bignumMerkleProofDigest proof
             in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_proof_digest = ")
                    `catch` handleSampleError format
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCtBignumMerkleEnvelopeDigest :: OutputFormat -> [String] -> IO ()
cmdCtBignumMerkleEnvelopeDigest format
    ( contextDigest : protocolVersionStr : networkId : assetIdStr : ledgerEpochStr
      : rootDigest : rootDepthStr : publicFeeStr : cIn1Str : cIn2Str : cOut1Str : cOut2Str
      : nf1Str : nf2Str : proofArgs
    ) =
        case
            ( parseCanonicalInt protocolVersionStr
            , parseCanonicalInt assetIdStr
            , parseCanonicalInt ledgerEpochStr
            , parseCanonicalInt rootDepthStr
            , parseCanonicalInteger publicFeeStr
            , parseCanonicalIntegerVec cIn1Str
            , parseCanonicalIntegerVec cIn2Str
            , parseCanonicalIntegerVec cOut1Str
            , parseCanonicalIntegerVec cOut2Str
            , parseCanonicalIntegerVec nf1Str
            , parseCanonicalIntegerVec nf2Str
            , parseCtBignumMerkleProofDigestArgs proofArgs
            )
        of
            ( Just protocolVersion
              , Just assetId
              , Just ledgerEpoch
              , Just rootDepth
              , Just publicFee
              , Just cIn1
              , Just cIn2
              , Just cOut1
              , Just cOut2
              , Just nf1
              , Just nf2
              , Right proof
              ) ->
                let digest =
                      bignumEnvelopeDigest
                        contextDigest protocolVersion networkId assetId ledgerEpoch rootDigest rootDepth publicFee
                        cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof
                 in (evaluate digest >>= outputStringResult format "ct_bignum_merkle_envelope_digest = ")
                        `catch` handleSampleError format
            _ -> outputError format "Expected context digest, bignum context fields, and bignum Merkle proof fields"
cmdCtBignumMerkleEnvelopeDigest format _ =
    outputUsage format ("Usage: ct-bignum-merkle-envelope-digest CONTEXT_DIGEST VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 " ++ ctBignumMerkleProofArgsUsage)

cmdCtBignumVerifyMerkleEnvelope :: OutputFormat -> [String] -> IO ()
cmdCtBignumVerifyMerkleEnvelope format
    ( mStr : n2Str : qStr : betaStr : gammaStr : kStr : ckStr : nkStr
      : ledgerStr : spentStr : expectedVersionStr : expectedNetworkId
      : expectedAssetIdStr : expectedLedgerEpochStr : expectedRoot
      : expectedRootDepthStr : expectedPublicFeeStr : contextDigest : protocolVersionStr : networkId
      : assetIdStr : ledgerEpochStr : rootDigest : rootDepthStr : publicFeeStr : cIn1Str
      : cIn2Str : cOut1Str : cOut2Str : nf1Str : nf2Str : proofArgs
    ) =
        case
            ( parseBigCbParams mStr n2Str qStr betaStr
            , parseCanonicalInteger gammaStr
            , parseCanonicalInt kStr
            , parseCanonicalIntegerMat ckStr
            , parseCanonicalIntegerMat nkStr
            , parseCanonicalIntegerMat ledgerStr
            , parseCanonicalIntegerMat spentStr
            , parseCanonicalInt expectedVersionStr
            , parseCanonicalInt expectedAssetIdStr
            , parseCanonicalInt expectedLedgerEpochStr
            , parseCanonicalInt expectedRootDepthStr
            , parseCanonicalInteger expectedPublicFeeStr
            , parseCanonicalInt protocolVersionStr
            , parseCanonicalInt assetIdStr
            , parseCanonicalInt ledgerEpochStr
            , parseCanonicalInt rootDepthStr
            , parseCanonicalInteger publicFeeStr
            , parseCanonicalIntegerVec cIn1Str
            , parseCanonicalIntegerVec cIn2Str
            , parseCanonicalIntegerVec cOut1Str
            , parseCanonicalIntegerVec cOut2Str
            , parseCanonicalIntegerVec nf1Str
            , parseCanonicalIntegerVec nf2Str
            , parseCtBignumMerkleProofDigestArgs proofArgs
            )
        of
            ( Just params
              , Just gamma
              , Just k
              , Just ck
              , Just nk
              , Just ledger
              , Just spent
              , Just expectedVersion
              , Just expectedAssetId
              , Just expectedLedgerEpoch
              , Just expectedRootDepth
              , Just expectedPublicFee
              , Just protocolVersion
              , Just assetId
              , Just ledgerEpoch
              , Just rootDepth
              , Just publicFee
              , Just cIn1
              , Just cIn2
              , Just cOut1
              , Just cOut2
              , Just nf1
              , Just nf2
              , Right proof
              ) -> do
                let computedDigest =
                        bignumTransactionContextDigest
                            protocolVersion networkId assetId ledgerEpoch rootDigest rootDepth publicFee
                            cIn1 cIn2 cOut1 cOut2 nf1 nf2
                    policyOk =
                        expectedPublicFee == publicFee
                            && protocolVersion == expectedVersion
                            && networkId == expectedNetworkId
                            && assetId == expectedAssetId
                            && ledgerEpoch == expectedLedgerEpoch
                            && rootDigest == expectedRoot
                            && rootDepth == expectedRootDepth
                            && contextDigest == computedDigest
                    result =
                        policyOk &&
                        bignumVerifyMerkleWithFee
                            params gamma k ck nk ledger rootDigest rootDepth spent publicFee
                            cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof
                (evaluate result >>= outputBoolResult format "ct_bignum_verify_merkle_envelope = ")
                    `catch` handleSampleError format
            _ -> outputError format "Expected bignum envelope policy, context, and proof fields"
cmdCtBignumVerifyMerkleEnvelope format _ =
    outputUsage format ("Usage: ct-bignum-verify-merkle-envelope M N2 Q BETA G K CK NK LEDGER SPENT EXPECTED_VERSION EXPECTED_NETWORK EXPECTED_ASSET EXPECTED_EPOCH EXPECTED_ROOT EXPECTED_ROOT_DEPTH EXPECTED_FEE CONTEXT_DIGEST VERSION NETWORK ASSET EPOCH ROOT ROOT_DEPTH FEE C1 C2 C3 C4 NF1 NF2 " ++ ctBignumMerkleProofArgsUsage)

cmdCtBignumWalletProofRequestDigest :: OutputFormat -> [String] -> IO ()
cmdCtBignumWalletProofRequestDigest
    format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootDigest
    , rootDepthStr
    , publicFeeStr
    , cIn1Str
    , cIn2Str
    , cOut1Str
    , cOut2Str
    , nf1Str
    , nf2Str
    , acceptedRootsStr
    , acceptedRootDepthsStr
    , spentNullifiersStr
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseCanonicalInt rootDepthStr
        , parseCanonicalInteger publicFeeStr
        , parseCanonicalIntegerVec cIn1Str
        , parseCanonicalIntegerVec cIn2Str
        , parseCanonicalIntegerVec cOut1Str
        , parseCanonicalIntegerVec cOut2Str
        , parseCanonicalIntegerVec nf1Str
        , parseCanonicalIntegerVec nf2Str
        , parseStringList acceptedRootsStr
        , parseCanonicalVec acceptedRootDepthsStr
        , parseCanonicalIntegerMat spentNullifiersStr
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just rootDepth
          , Just publicFee
          , Just cIn1
          , Just cIn2
          , Just cOut1
          , Just cOut2
          , Just nf1
          , Just nf2
          , Just acceptedRoots
          , Just acceptedRootDepths
          , Just spentNullifiers
          ) ->
            let digest =
                  bignumWalletProofRequestDigest
                    protocolVersion networkId assetId ledgerEpoch rootDigest rootDepth publicFee
                    cIn1 cIn2 cOut1 cOut2 nf1 nf2 acceptedRoots acceptedRootDepths spentNullifiers
             in (evaluate digest >>= outputStringResult format "ct_bignum_wallet_proof_request_digest = ")
                    `catch` handleSampleError format
        _ -> outputError format "Expected bignum wallet proof request context, accepted roots, and spent nullifiers"
cmdCtBignumWalletProofRequestDigest format _ =
    outputUsage format "Usage: ct-bignum-wallet-proof-request-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 ACCEPTED_ROOTS ACCEPTED_ROOT_DEPTHS SPENT_NULLIFIERS"

cmdCtBignumAcceptedRootWindowDigest :: OutputFormat -> [String] -> IO ()
cmdCtBignumAcceptedRootWindowDigest
    format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootsStr
    , rootDepthsStr
    , validFromEpochsStr
    , expiresAtEpochsStr
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseStringList rootsStr
        , parseCanonicalVec rootDepthsStr
        , parseCanonicalVec validFromEpochsStr
        , parseCanonicalVec expiresAtEpochsStr
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just roots
          , Just rootDepths
          , Just validFromEpochs
          , Just expiresAtEpochs
          ) ->
            let digest =
                  bignumAcceptedRootWindowDigest
                    protocolVersion networkId assetId ledgerEpoch roots rootDepths validFromEpochs expiresAtEpochs
             in (evaluate digest >>= outputStringResult format "ct_bignum_accepted_root_window_digest = ")
                    `catch` handleSampleError format
        _ -> outputError format "Expected bignum accepted-root window fields"
cmdCtBignumAcceptedRootWindowDigest format _ =
    outputUsage format "Usage: ct-bignum-accepted-root-window-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOTS ROOT_DEPTHS VALID_FROM_EPOCHS EXPIRES_AT_EPOCHS"

cmdCtTransactionContext :: OutputFormat -> [String] -> IO ()
cmdCtTransactionContext format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootDigest
    , rootDepthStr
    , publicFeeStr
    , cIn1Str
    , cIn2Str
    , cOut1Str
    , cOut2Str
    , nf1Str
    , nf2Str
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseCanonicalInt rootDepthStr
        , parseCanonicalInt publicFeeStr
        , parseCanonicalVec cIn1Str
        , parseCanonicalVec cIn2Str
        , parseCanonicalVec cOut1Str
        , parseCanonicalVec cOut2Str
        , parseCanonicalVec nf1Str
        , parseCanonicalVec nf2Str
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just rootDepth
          , Just publicFee
          , Just cIn1
          , Just cIn2
          , Just cOut1
          , Just cOut2
          , Just nf1
          , Just nf2
          ) ->
            outputStringResult format "ct_transaction_context = " $
                ConfidentialTransaction.transactionContextDigest
                    protocolVersion
                    networkId
                    assetId
                    ledgerEpoch
                    rootDigest
                    rootDepth
                    publicFee
                    cIn1
                    cIn2
                    cOut1
                    cOut2
                    nf1
                    nf2
        _ -> outputError format "Expected transaction context fields"
cmdCtTransactionContext format _ =
    outputUsage format "Usage: ct-transaction-context VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2"

cmdCtMerkleProofDigest :: OutputFormat -> [String] -> IO ()
cmdCtMerkleProofDigest format args =
    case parseCtMerkleProofDigestArgs args of
        Right proof ->
            outputStringResult format "ct_merkle_proof_digest = " $
                ConfidentialTransaction.transactionMerkleProofDigest proof
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCtMerkleEnvelopeDigest :: OutputFormat -> [String] -> IO ()
cmdCtMerkleEnvelopeDigest format
    ( contextDigest : protocolVersionStr : networkId : assetIdStr : ledgerEpochStr
      : rootDigest : rootDepthStr : publicFeeStr : cIn1Str : cIn2Str : cOut1Str : cOut2Str
      : nf1Str : nf2Str : proofArgs
    ) =
        case
            ( parseCanonicalInt protocolVersionStr
            , parseCanonicalInt assetIdStr
            , parseCanonicalInt ledgerEpochStr
            , parseCanonicalInt rootDepthStr
            , parseCanonicalInt publicFeeStr
            , parseCanonicalVec cIn1Str
            , parseCanonicalVec cIn2Str
            , parseCanonicalVec cOut1Str
            , parseCanonicalVec cOut2Str
            , parseCanonicalVec nf1Str
            , parseCanonicalVec nf2Str
            , parseCtMerkleProofDigestArgs proofArgs
            )
        of
            ( Just protocolVersion
              , Just assetId
              , Just ledgerEpoch
              , Just rootDepth
              , Just publicFee
              , Just cIn1
              , Just cIn2
              , Just cOut1
              , Just cOut2
              , Just nf1
              , Just nf2
              , Right proof
              ) ->
                outputStringResult format "ct_merkle_envelope_digest = " $
                    ConfidentialTransaction.transactionEnvelopeDigest
                        contextDigest
                        protocolVersion
                        networkId
                        assetId
                        ledgerEpoch
                        rootDigest
                        rootDepth
                        publicFee
                        cIn1
                        cIn2
                        cOut1
                        cOut2
                        nf1
                        nf2
                        proof
            _ -> outputError format "Expected context digest, context fields, and Merkle proof fields"
cmdCtMerkleEnvelopeDigest format _ =
    outputUsage format "Usage: ct-merkle-envelope-digest CONTEXT_DIGEST VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 ..."

cmdCtWalletProofRequestDigest :: OutputFormat -> [String] -> IO ()
cmdCtWalletProofRequestDigest
    format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootDigest
    , rootDepthStr
    , publicFeeStr
    , cIn1Str
    , cIn2Str
    , cOut1Str
    , cOut2Str
    , nf1Str
    , nf2Str
    , acceptedRootsStr
    , acceptedRootDepthsStr
    , spentNullifiersStr
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseCanonicalInt rootDepthStr
        , parseCanonicalInt publicFeeStr
        , parseCanonicalVec cIn1Str
        , parseCanonicalVec cIn2Str
        , parseCanonicalVec cOut1Str
        , parseCanonicalVec cOut2Str
        , parseCanonicalVec nf1Str
        , parseCanonicalVec nf2Str
        , parseStringList acceptedRootsStr
        , parseCanonicalVec acceptedRootDepthsStr
        , parseCanonicalMat spentNullifiersStr
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just rootDepth
          , Just publicFee
          , Just cIn1
          , Just cIn2
          , Just cOut1
          , Just cOut2
          , Just nf1
          , Just nf2
          , Just acceptedRoots
          , Just acceptedRootDepths
          , Just spentNullifiers
          ) ->
            let digest =
                    ConfidentialTransaction.transactionWalletProofRequestDigest
                        protocolVersion
                        networkId
                        assetId
                        ledgerEpoch
                        rootDigest
                        rootDepth
                        publicFee
                        cIn1
                        cIn2
                        cOut1
                        cOut2
                        nf1
                        nf2
                        acceptedRoots
                        acceptedRootDepths
                        spentNullifiers
             in (evaluate digest >>= outputStringResult format "ct_wallet_proof_request_digest = ")
                    `catch` handleSampleError format
        _ -> outputError format "Expected wallet proof request context, accepted roots, and spent nullifiers"
cmdCtWalletProofRequestDigest format _ =
    outputUsage format "Usage: ct-wallet-proof-request-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOT ROOT_DEPTH PUBLIC_FEE C_IN1 C_IN2 C_OUT1 C_OUT2 NF1 NF2 ACCEPTED_ROOTS ACCEPTED_ROOT_DEPTHS SPENT_NULLIFIERS"

cmdCtAcceptedRootWindowDigest :: OutputFormat -> [String] -> IO ()
cmdCtAcceptedRootWindowDigest
    format
    [ protocolVersionStr
    , networkId
    , assetIdStr
    , ledgerEpochStr
    , rootsStr
    , rootDepthsStr
    , validFromEpochsStr
    , expiresAtEpochsStr
    ] =
    case
        ( parseCanonicalInt protocolVersionStr
        , parseCanonicalInt assetIdStr
        , parseCanonicalInt ledgerEpochStr
        , parseStringList rootsStr
        , parseCanonicalVec rootDepthsStr
        , parseCanonicalVec validFromEpochsStr
        , parseCanonicalVec expiresAtEpochsStr
        )
    of
        ( Just protocolVersion
          , Just assetId
          , Just ledgerEpoch
          , Just roots
          , Just rootDepths
          , Just validFromEpochs
          , Just expiresAtEpochs
          ) ->
            let digest =
                    ConfidentialTransaction.transactionAcceptedRootWindowDigest
                        protocolVersion
                        networkId
                        assetId
                        ledgerEpoch
                        roots
                        rootDepths
                        validFromEpochs
                        expiresAtEpochs
             in (evaluate digest >>= outputStringResult format "ct_accepted_root_window_digest = ")
                    `catch` handleSampleError format
        _ -> outputError format "Expected accepted-root window fields"
cmdCtAcceptedRootWindowDigest format _ =
    outputUsage format "Usage: ct-accepted-root-window-digest VERSION NETWORK_ID ASSET_ID LEDGER_EPOCH ROOTS ROOT_DEPTHS VALID_FROM_EPOCHS EXPIRES_AT_EPOCHS"

cmdCtSampleOpening :: OutputFormat -> [String] -> IO ()
cmdCtSampleOpening format [msgLenStr, randLenStr, boundStr] =
    case (parseInt msgLenStr, parseInt randLenStr, parseInt boundStr) of
        (Just msgLen, Just randLen, Just bound) ->
            outputSampleResult format
                (outputOpeningResult format "sample_opening = ")
                (ConfidentialSampling.sampleOpening msgLen randLen bound)
        _ -> outputError format "Expected message length, randomness length, and bound"
cmdCtSampleOpening format _ =
    outputUsage format "Usage: ct-sample-opening MSG_LEN RAND_LEN BOUND"

cmdCtSampleOpenings :: OutputFormat -> [String] -> IO ()
cmdCtSampleOpenings format [countStr, msgLenStr, randLenStr, boundStr] =
    case (parseInt countStr, parseInt msgLenStr, parseInt randLenStr, parseInt boundStr) of
        (Just count, Just msgLen, Just randLen, Just bound) ->
            outputSampleResult format
                (outputOpeningsResult format "sample_openings = ")
                (ConfidentialSampling.sampleOpenings count msgLen randLen bound)
        _ -> outputError format "Expected count, message length, randomness length, and bound"
cmdCtSampleOpenings format _ =
    outputUsage format "Usage: ct-sample-openings COUNT MSG_LEN RAND_LEN BOUND"

cmdCtNullifier :: OutputFormat -> [String] -> IO ()
cmdCtNullifier format [mStr, n2Str, qStr, betaStr, nkStr, amountStr, randStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseMat nkStr, parseInt amountStr, parseVec randStr) of
        (Just params, Just nk, Just amount, Just randVec) ->
            outputVecResult format "nullifier = "
                (ConfidentialTransaction.nullifier params nk (makeScalarOpening amount randVec))
        _ -> outputError format "Expected params, nullifier key, scalar amount, and randomness vector"
cmdCtNullifier format _ =
    outputUsage format "Usage: ct-nullifier M N2 Q BETA \"[[nk]]\" AMOUNT \"[rand]\""

cmdCtSampleNullifierMask :: OutputFormat -> [String] -> IO ()
cmdCtSampleNullifierMask format [mStr, n2Str, qStr, betaStr, gammaStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr) of
        (Just params, Just gamma) ->
            outputSampleResult format
                (outputOpeningResult format "sample_nullifier_mask = ")
                (ConfidentialTransaction.sampleNullifierMask params gamma)
        _ -> outputError format "Expected params (M N2 Q BETA) and gamma"
cmdCtSampleNullifierMask format _ =
    outputUsage format "Usage: ct-sample-nullifier-mask M N2 Q BETA GAMMA"

cmdCtSampleNullifierMasks :: OutputFormat -> [String] -> IO ()
cmdCtSampleNullifierMasks format [mStr, n2Str, qStr, betaStr, gammaStr, roundsStr] =
    case (parseCbParams mStr n2Str qStr betaStr, parseInt gammaStr, parseInt roundsStr) of
        (Just params, Just gamma, Just rounds) ->
            outputSampleResult format
                (outputOpeningsResult format "sample_nullifier_masks = ")
                (ConfidentialTransaction.sampleNullifierMasks params gamma rounds)
        _ -> outputError format "Expected params (M N2 Q BETA), gamma, and rounds"
cmdCtSampleNullifierMasks format _ =
    outputUsage format "Usage: ct-sample-nullifier-masks M N2 Q BETA GAMMA ROUNDS"

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

cmdCtLedgerStepVerifyScaffold :: OutputFormat -> [String] -> IO ()
cmdCtLedgerStepVerifyScaffold format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, noteCommitmentsStr, noteBitsStr, noteCompsStr, noteAmountAsStr, noteAmountZsStr, notePairAsStr, notePairZsStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1ACommitsStr, in1ANullifiersStr, in1ZMsgsStr, in1ZRandsStr, in2ACommitsStr, in2ANullifiersStr, in2ZMsgsStr, in2ZRandsStr, balanceAStr, balanceZsStr, out1BitsStr, out1CompsStr, out1AmountAStr, out1AmountZStr, out1PairAsStr, out1PairZsStr, out2BitsStr, out2CompsStr, out2AmountAStr, out2AmountZStr, out2PairAsStr, out2PairZsStr] =
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
                     in outputBoolResult format "ledger_step_valid_scaffold = "
                            (ConfidentialTransaction.ledgerStepValidScaffold
                                params gamma k ck nk notes spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof)
                _ -> outputError format "Expected consistent verified-note inputs and membership proofs for both input commitments"
        _ -> outputError format "Expected params, keys, verified-note ledger fields, nullifiers, and transaction-proof fields"
cmdCtLedgerStepVerifyScaffold format _ =
    outputUsage format "Usage: ct-ledger-step-verify-scaffold M N2 Q BETA G K CK NK NOTE_COMMITMENTS NOTE_BITS NOTE_COMPS NOTE_AMOUNT_AS NOTE_AMOUNT_ZS NOTE_PAIR_AS NOTE_PAIR_ZS SPENT C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_A OUT1_AMOUNT_Z OUT1_PAIR_AS OUT1_PAIR_ZS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_A OUT2_AMOUNT_Z OUT2_PAIR_AS OUT2_PAIR_ZS"

cmdCtProveWithUsage :: String -> OutputFormat -> [String] -> IO ()
cmdCtProveWithUsage command format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, ledgerStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1AmountStr, in1RandStr, in2AmountStr, in2RandStr, out1AmountStr, out1RandStr, out2AmountStr, out2RandStr, out1BitsStr, out1BitRandsStr, out1CompsStr, out1CompRandsStr, out2BitsStr, out2BitRandsStr, out2CompsStr, out2CompRandsStr, yIn1MsgsStr, yIn1RandsStr, yIn2MsgsStr, yIn2RandsStr, yBalanceStr, yOut1AmountsStr, yOut1PairssStr, yOut2AmountsStr, yOut2PairssStr] =
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
cmdCtProveWithUsage command format _ =
    outputUsage format (ctProveUsage command)

cmdCtProveScaffold :: OutputFormat -> [String] -> IO ()
cmdCtProveScaffold = cmdCtProveWithUsage "ct-prove-scaffold"

cmdCtProveMerkle :: OutputFormat -> [String] -> IO ()
cmdCtProveMerkle format [mStr, n2Str, qStr, betaStr, gammaStr, kStr, ckStr, nkStr, ledgerStr, spentStr, cIn1Str, cIn2Str, cOut1Str, cOut2Str, nf1Str, nf2Str, in1AmountStr, in1RandStr, in2AmountStr, in2RandStr, out1AmountStr, out1RandStr, out2AmountStr, out2RandStr, out1BitsStr, out1BitRandsStr, out1CompsStr, out1CompRandsStr, out2BitsStr, out2BitRandsStr, out2CompsStr, out2CompRandsStr, yIn1MsgsStr, yIn1RandsStr, yIn2MsgsStr, yIn2RandsStr, yBalanceStr, yOut1AmountsStr, yOut1PairssStr, yOut2AmountsStr, yOut2PairssStr] =
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
                    case ConfidentialTransaction.transactionFsProveMerkle
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
                                Human -> putStrLn $ "transaction_fs_merkle_proof = " ++ show proof
                                Json -> putStrLn $ jsonCtMerkleTransactionProof proof
                        Nothing ->
                            case format of
                                Human -> putStrLn "transaction_fs_merkle_proof = null"
                                Json -> putStrLn "null"
                _ -> outputError format "Bit/complement counts must match their randomness matrices"
        _ -> outputError format "Expected params, keys, ledger, commitments, openings, bit decompositions, and mask vectors"
cmdCtProveMerkle format _ =
    outputUsage format "Usage: ct-prove-merkle M N2 Q BETA G K CK NK LEDGER SPENT C1 C2 C3 C4 NF1 NF2 IN1_AMOUNT IN1_RAND IN2_AMOUNT IN2_RAND OUT1_AMOUNT OUT1_RAND OUT2_AMOUNT OUT2_RAND OUT1_BITS OUT1_BIT_RANDS OUT1_COMPS OUT1_COMP_RANDS OUT2_BITS OUT2_BIT_RANDS OUT2_COMPS OUT2_COMP_RANDS Y1_MSGS Y1_RANDS Y2_MSGS Y2_RANDS YBALS YOUT1_AMOUNTS YOUT1_PAIRSS YOUT2_AMOUNTS YOUT2_PAIRSS"

cmdCtVerifyScaffold :: OutputFormat -> [String] -> IO ()
cmdCtVerifyScaffold format args =
    case prepareCtVerifyScaffold args of
        Right verify -> outputBoolResult format "transaction_fs_verify = " (verify ())
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCtVerifyMerkle :: OutputFormat -> [String] -> IO ()
cmdCtVerifyMerkle format args =
    case prepareCtVerifyMerkle args of
        Right verify -> outputBoolResult format "transaction_fs_verify_merkle = " (verify ())
        Left err
            | take 5 err == "Usage" -> outputUsage format err
            | otherwise -> outputError format err

cmdCtVerifyMerkleEnvelope :: OutputFormat -> [String] -> IO ()
cmdCtVerifyMerkleEnvelope format
    ( mStr : n2Str : qStr : betaStr : gammaStr : kStr : ckStr : nkStr
      : ledgerStr : spentStr : expectedVersionStr : expectedNetworkId
      : expectedAssetIdStr : expectedLedgerEpochStr : expectedRoot
      : expectedRootDepthStr : expectedPublicFeeStr : contextDigest : protocolVersionStr : networkId
      : assetIdStr : ledgerEpochStr : rootDigest : rootDepthStr : publicFeeStr : cIn1Str
      : cIn2Str : cOut1Str : cOut2Str : nf1Str : nf2Str : proofArgs
    ) =
        case
            ( parseCanonicalInt expectedVersionStr
            , parseCanonicalInt expectedAssetIdStr
            , parseCanonicalInt expectedLedgerEpochStr
            , parseCanonicalInt expectedRootDepthStr
            , parseCanonicalInt expectedPublicFeeStr
            , parseCanonicalInt protocolVersionStr
            , parseCanonicalInt assetIdStr
            , parseCanonicalInt ledgerEpochStr
            , parseCanonicalInt rootDepthStr
            , parseCanonicalInt publicFeeStr
            , parseCanonicalVec cIn1Str
            , parseCanonicalVec cIn2Str
            , parseCanonicalVec cOut1Str
            , parseCanonicalVec cOut2Str
            , parseCanonicalVec nf1Str
            , parseCanonicalVec nf2Str
            )
        of
            ( Just expectedVersion
              , Just expectedAssetId
              , Just expectedLedgerEpoch
              , Just expectedRootDepth
              , Just expectedPublicFee
              , Just protocolVersion
              , Just assetId
              , Just ledgerEpoch
              , Just rootDepth
              , Just publicFee
              , Just cIn1
              , Just cIn2
              , Just cOut1
              , Just cOut2
              , Just nf1
              , Just nf2
              ) -> do
                let computedDigest =
                        ConfidentialTransaction.transactionContextDigest
                            protocolVersion
                            networkId
                            assetId
                            ledgerEpoch
                            rootDigest
                            rootDepth
                            publicFee
                            cIn1
                            cIn2
                            cOut1
                            cOut2
                            nf1
                            nf2
                    policyOk =
                        expectedPublicFee == publicFee
                            && protocolVersion == expectedVersion
                            && networkId == expectedNetworkId
                            && assetId == expectedAssetId
                            && ledgerEpoch == expectedLedgerEpoch
                            && rootDigest == expectedRoot
                            && rootDepth == expectedRootDepth
                            && contextDigest == computedDigest
                    merkleArgs =
                        [ mStr
                        , n2Str
                        , qStr
                        , betaStr
                        , gammaStr
                        , kStr
                        , ckStr
                        , nkStr
                        , ledgerStr
                        , spentStr
                        , cIn1Str
                        , cIn2Str
                        , cOut1Str
                        , cOut2Str
                        , nf1Str
                        , nf2Str
                        ]
                            ++ proofArgs
                if not policyOk
                    then outputBoolResult format "transaction_fs_verify_merkle_envelope = " False
                    else case prepareCtVerifyMerkleWithRoot (Just rootDigest) (Just publicFee) (Just rootDepth) merkleArgs of
                        Right verify ->
                            outputBoolResult format "transaction_fs_verify_merkle_envelope = " (verify ())
                        Left err
                            | take 5 err == "Usage" -> outputUsage format err
                            | otherwise -> outputError format err
            _ -> outputError format "Expected envelope policy, context, and proof fields"
cmdCtVerifyMerkleEnvelope format _ =
    outputUsage format "Usage: ct-verify-merkle-envelope M N2 Q BETA G K CK NK LEDGER SPENT EXPECTED_VERSION EXPECTED_NETWORK EXPECTED_ASSET EXPECTED_EPOCH EXPECTED_ROOT EXPECTED_ROOT_DEPTH EXPECTED_FEE CONTEXT_DIGEST VERSION NETWORK ASSET EPOCH ROOT ROOT_DEPTH FEE C1 C2 C3 C4 NF1 NF2 IN1_A_COMMITS IN1_A_NULLIFIERS IN1_Z_MSGS IN1_Z_RANDS IN2_A_COMMITS IN2_A_NULLIFIERS IN2_Z_MSGS IN2_Z_RANDS BAL_AS BAL_ZS OUT1_BITS OUT1_COMPS OUT1_AMOUNT_AS OUT1_AMOUNT_ZS OUT1_PAIR_ASS OUT1_PAIR_ZSS OUT2_BITS OUT2_COMPS OUT2_AMOUNT_AS OUT2_AMOUNT_ZS OUT2_PAIR_ASS OUT2_PAIR_ZSS"

cmdCtVerifyBenchWithUsage :: String -> ([String] -> Either String (() -> Bool)) -> OutputFormat -> [String] -> IO ()
cmdCtVerifyBenchWithUsage command prepare format (iterationsStr:warmupStr:rest) =
    case (parseInt iterationsStr, parseInt warmupStr) of
        (Just iterations, Just warmup)
            | iterations > 0 && warmup >= 0 ->
                case prepare rest of
                    Right verify ->
                        benchmarkBool warmup iterations verify >>= outputBenchStats format "transaction_fs_verify_bench"
                    Left err
                        | take 5 err == "Usage" -> outputUsage format (ctVerifyBenchUsage command)
                        | otherwise -> outputError format err
        _ -> outputError format "Expected positive ITERATIONS and non-negative WARMUP"
cmdCtVerifyBenchWithUsage command _ format _ =
    outputUsage format (ctVerifyBenchUsage command)

cmdCtVerifyBenchScaffold :: OutputFormat -> [String] -> IO ()
cmdCtVerifyBenchScaffold = cmdCtVerifyBenchWithUsage "ct-verify-bench-scaffold" prepareCtVerifyScaffold
