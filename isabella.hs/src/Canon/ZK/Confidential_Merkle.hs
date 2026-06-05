-- | Cryptographic Merkle helpers for confidential note commitments.
--
-- This module is the Haskell runtime companion to
-- Canon/ZK/Authenticated_Merkle. It remains separate from
-- Confidential_Transaction while that verifier still uses the algebraic ledger
-- scaffold.
module Canon.ZK.Confidential_Merkle
  ( MerkleMembershipProof(..)
  , merkleDst
  , merkleLeafTag
  , merkleNodeTag
  , merkleEmptyTag
  , encodeLeaf
  , encodeEmpty
  , encodeNode
  , leaf
  , empty
  , node
  , root
  , pathRoot
  , membershipProve
  , membershipVerify
  ) where

import Data.Bits (shiftL, shiftR, (.&.), (.|.))
import Data.Char (ord)
import Data.List (findIndex)
import Data.Word (Word64, Word8)
import qualified Canon.ZK.Internal.RepeatedFS as RepeatedFS

data MerkleMembershipProof = MerkleMembershipProof
  { merkle_index :: Int
  , merkle_root :: String
  , merkle_siblings :: [String]
  , merkle_directions :: [Bool]
  }
  deriving (Eq, Show)

merkleDst :: String
merkleDst = "ISABELLA-CT-MERKLE-v1"

merkleLeafTag :: Int
merkleLeafTag = 0

merkleNodeTag :: Int
merkleNodeTag = 1

merkleEmptyTag :: Int
merkleEmptyTag = 2

word64LeBytes :: Word64 -> [Word8]
word64LeBytes value =
  [ fromIntegral ((value `shiftR` (8 * i)) .&. 0xff)
  | i <- [0 .. 7]
  ]

int64LeBytes :: Int -> [Word8]
int64LeBytes value =
  word64LeBytes (fromIntegral value :: Word64)

encodeIntVec :: [Int] -> [Word8]
encodeIntVec values =
  int64LeBytes (length values) ++ concatMap int64LeBytes values

preimage :: Int -> [Word8] -> [Word8]
preimage tag body =
  map (fromIntegral . ord) merkleDst ++ int64LeBytes tag ++ body

hexByte :: Word8 -> String
hexByte byte =
  let alphabet = "0123456789abcdef"
      hi = fromIntegral ((byte `shiftR` 4) .&. 0x0f)
      lo = fromIntegral (byte .&. 0x0f)
   in [alphabet !! hi, alphabet !! lo]

digestHex :: [Word8] -> String
digestHex =
  concatMap hexByte

digest :: [Word8] -> String
digest =
  digestHex . RepeatedFS.sha3_256

hexValue :: Char -> Maybe Word8
hexValue c
  | c >= '0' && c <= '9' = Just (fromIntegral (ord c - ord '0'))
  | c >= 'a' && c <= 'f' = Just (fromIntegral (10 + ord c - ord 'a'))
  | otherwise = Nothing

hexToBytes :: String -> Maybe [Word8]
hexToBytes hex
  | length hex /= 64 = Nothing
  | otherwise = go hex
 where
  go [] = Just []
  go (hi:lo:rest) = do
    hiValue <- hexValue hi
    loValue <- hexValue lo
    tailBytes <- go rest
    pure (((hiValue `shiftL` 4) .|. loValue) : tailBytes)
  go _ = Nothing

digestBytesToInts :: [Word8] -> [Int]
digestBytesToInts =
  map fromIntegral

encodeLeaf :: [Int] -> String
encodeLeaf commitment =
  digestHex (preimage merkleLeafTag (encodeIntVec commitment))

encodeEmpty :: Int -> String
encodeEmpty width
  | width < 0 = error "empty width must be non-negative"
  | otherwise = digestHex (preimage merkleEmptyTag (int64LeBytes width))

encodeNode :: String -> String -> String
encodeNode left right =
  case (hexToBytes left, hexToBytes right) of
    (Just leftBytes, Just rightBytes) ->
      digestHex
        (preimage
          merkleNodeTag
          (encodeIntVec (digestBytesToInts leftBytes) ++
           encodeIntVec (digestBytesToInts rightBytes)))
    _ -> error "Merkle node inputs must be canonical lowercase SHA3-256 hex digests"

leaf :: [Int] -> String
leaf commitment =
  digest (preimage merkleLeafTag (encodeIntVec commitment))

empty :: Int -> String
empty width
  | width < 0 = error "empty width must be non-negative"
  | otherwise = digest (preimage merkleEmptyTag (int64LeBytes width))

nodeMaybe :: String -> String -> Maybe String
nodeMaybe left right =
  case (hexToBytes left, hexToBytes right) of
    (Just leftBytes, Just rightBytes) ->
      Just
        (digest
          (preimage
            merkleNodeTag
            (encodeIntVec (digestBytesToInts leftBytes) ++
             encodeIntVec (digestBytesToInts rightBytes))))
    _ -> Nothing

node :: String -> String -> String
node left right =
  case nodeMaybe left right of
    Just value -> value
    Nothing -> error "Merkle node inputs must be canonical lowercase SHA3-256 hex digests"

sameWidth :: [[Int]] -> Int -> Bool
sameWidth commitments width =
  all ((== width) . length) commitments

compressLevel :: Int -> [String] -> [String]
compressLevel _ [] = []
compressLevel _ [x] = [x]
compressLevel width xs =
  go xs
 where
  go [] = []
  go [left] = [node left (empty width)]
  go (left:right:rest) = node left right : go rest

root :: [[Int]] -> String
root commitments =
  let width = case commitments of
        [] -> 0
        first:_ -> length first
   in if not (sameWidth commitments width)
        then error "Merkle commitments must all have the same width"
        else case commitments of
          [] -> empty 0
          _ -> go (map leaf commitments)
            where
              go [] = empty width
              go [x] = x
              go xs = go (compressLevel width xs)

indexDirections :: Int -> Int -> [Bool]
indexDirections depth index
  | depth <= 0 = []
  | otherwise = odd index : indexDirections (depth - 1) (index `div` 2)

pathRoot :: [Int] -> [String] -> [Bool] -> Maybe String
pathRoot commitment siblings directions =
  go (leaf commitment) siblings directions
 where
  go acc [] [] = Just acc
  go acc (sibling:restSiblings) (False:restDirections) = do
    parent <- nodeMaybe acc sibling
    go parent restSiblings restDirections
  go acc (sibling:restSiblings) (True:restDirections) = do
    parent <- nodeMaybe sibling acc
    go parent restSiblings restDirections
  go _ _ _ = Nothing

membershipProve :: [[Int]] -> [Int] -> Maybe MerkleMembershipProof
membershipProve ledger commitment = do
  index <- findIndex (== commitment) ledger
  let width = case ledger of
        [] -> length commitment
        first:_ -> length first
  if not (sameWidth ledger width)
    then Nothing
    else go index width index (map leaf ledger) [] []
 where
  go _ _ _ [] _ _ = Nothing
  go originalIndex _ _ [rt] siblings directions =
    Just
      MerkleMembershipProof
        { merkle_index = originalIndex
        , merkle_root = rt
        , merkle_siblings = reverse siblings
        , merkle_directions = reverse directions
        }
  go originalIndex width current level siblings directions =
    let isRight = odd current
        sibling =
          if isRight
            then level !! (current - 1)
            else if current + 1 < length level
              then level !! (current + 1)
              else empty width
     in go
          originalIndex
          width
          (current `div` 2)
          (compressLevel width level)
          (sibling : siblings)
          (isRight : directions)

membershipVerify :: [Int] -> MerkleMembershipProof -> Bool
membershipVerify commitment proof =
  merkle_directions proof == indexDirections (length (merkle_siblings proof)) (merkle_index proof) &&
  case (hexToBytes (merkle_root proof), pathRoot commitment (merkle_siblings proof) (merkle_directions proof)) of
    (Just _, Just rt) -> rt == merkle_root proof
    _ -> False
