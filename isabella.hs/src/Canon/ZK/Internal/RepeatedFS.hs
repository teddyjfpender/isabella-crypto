module Canon.ZK.Internal.RepeatedFS
  ( fixedFsRounds
  , sha3_256
  , binaryFsChallenge
  , binaryFsChallenges
  , boolFsChallenges
  , sigmaResponseRounds
  ) where

import Data.Bits (complement, rotateL, shiftL, shiftR, xor, (.&.))
import Data.Char (ord)
import Data.List (foldl')
import Data.Word (Word64, Word8)

fixedFsRounds :: Int
fixedFsRounds = 128

transcriptDst :: String
transcriptDst = "ISABELLA-CT-FS-v1"

keccakRoundConstants :: [Word64]
keccakRoundConstants =
  [ 0x0000000000000001, 0x0000000000008082, 0x800000000000808a
  , 0x8000000080008000, 0x000000000000808b, 0x0000000080000001
  , 0x8000000080008081, 0x8000000000008009, 0x000000000000008a
  , 0x0000000000000088, 0x0000000080008009, 0x000000008000000a
  , 0x000000008000808b, 0x800000000000008b, 0x8000000000008089
  , 0x8000000000008003, 0x8000000000008002, 0x8000000000000080
  , 0x000000000000800a, 0x800000008000000a, 0x8000000080008081
  , 0x8000000000008080, 0x0000000080000001, 0x8000000080008008
  ]

keccakRotationOffsets :: [Int]
keccakRotationOffsets =
  [ 0, 1, 62, 28, 27
  , 36, 44, 6, 55, 20
  , 3, 10, 43, 25, 39
  , 41, 45, 15, 21, 8
  , 18, 2, 61, 56, 14
  ]

at :: [a] -> Int -> a
at xs i = xs !! i

setAt :: Int -> a -> [a] -> [a]
setAt i value xs =
  take i xs ++ [value] ++ drop (i + 1) xs

xorAt :: Int -> Word64 -> [Word64] -> [Word64]
xorAt i value xs =
  setAt i ((xs `at` i) `xor` value) xs

theta :: [Word64] -> [Word64]
theta state =
  let c x = foldl1 xor [state `at` (x + 5 * y) | y <- [0 .. 4]]
      d x = c ((x + 4) `mod` 5) `xor` rotateL (c ((x + 1) `mod` 5)) 1
   in [ (state `at` (x + 5 * y)) `xor` d x
      | y <- [0 .. 4], x <- [0 .. 4]
      ]

rhoPi :: [Word64] -> [Word64]
rhoPi state =
  foldl'
    (\acc (x, y) ->
      let idx = x + 5 * y
          dst = y + 5 * ((2 * x + 3 * y) `mod` 5)
          value = rotateL (state `at` idx) (keccakRotationOffsets `at` idx)
       in setAt dst value acc)
    (replicate 25 0)
    [(x, y) | y <- [0 .. 4], x <- [0 .. 4]]

chi :: [Word64] -> [Word64]
chi b =
  [ (b `at` idx) `xor`
      ((complement (b `at` (((x + 1) `mod` 5) + 5 * y))) .&.
       (b `at` (((x + 2) `mod` 5) + 5 * y)))
  | y <- [0 .. 4]
  , x <- [0 .. 4]
  , let idx = x + 5 * y
  ]

keccakRound :: [Word64] -> Word64 -> [Word64]
keccakRound state rc =
  xorAt 0 rc (chi (rhoPi (theta state)))

keccakF1600 :: [Word64] -> [Word64]
keccakF1600 state =
  foldl' keccakRound state keccakRoundConstants

word64LeBytes :: Word64 -> [Word8]
word64LeBytes value =
  [ fromIntegral ((value `shiftR` (8 * i)) .&. 0xff)
  | i <- [0 .. 7]
  ]

int64LeBytes :: Int -> [Word8]
int64LeBytes value =
  word64LeBytes (fromIntegral value :: Word64)

transcriptBytes :: Int -> Int -> [Int] -> [Word8]
transcriptBytes domain roundIndex fields =
  map (fromIntegral . ord) transcriptDst ++
  int64LeBytes domain ++
  int64LeBytes roundIndex ++
  int64LeBytes (length fields) ++
  concatMap int64LeBytes fields

absorbBlock :: [Word64] -> [Word8] -> [Word64]
absorbBlock state block =
  keccakF1600 $
    foldl'
      (\acc (i, byte) ->
        let lane = i `div` 8
            shift = 8 * (i `mod` 8)
            word = (fromIntegral byte :: Word64) `shiftL` shift
         in xorAt lane word acc)
      state
      (zip [0 ..] block)

chunksOf :: Int -> [a] -> [[a]]
chunksOf _ [] = []
chunksOf n xs =
  let (headChunk, rest) = splitAt n xs
   in headChunk : chunksOf n rest

xorByteAt :: Int -> Word8 -> [Word8] -> [Word8]
xorByteAt i value xs =
  setAt i ((xs `at` i) `xor` value) xs

sha3_256 :: [Word8] -> [Word8]
sha3_256 bytes =
  let rate = 136
      fullBlockCount = length bytes `div` rate
      fullBlocks = take fullBlockCount (chunksOf rate bytes)
      tailBlock = drop (fullBlockCount * rate) bytes
      stateAfterFull = foldl' absorbBlock (replicate 25 0) fullBlocks
      emptyPadded = tailBlock ++ replicate (rate - length tailBlock) 0
      padded = xorByteAt (rate - 1) 0x80 (xorByteAt (length tailBlock) 0x06 emptyPadded)
      state = absorbBlock stateAfterFull padded
   in take 32 (concatMap word64LeBytes state)

binaryFsChallenge :: Int -> [Int] -> Int -> Int
binaryFsChallenge domain fields roundIndex =
  fromIntegral ((head (sha3_256 (transcriptBytes domain roundIndex fields))) .&. 1)

binaryFsChallenges :: Int -> [Int] -> [Int]
binaryFsChallenges domain fields =
  [binaryFsChallenge domain fields i | i <- [0 .. fixedFsRounds - 1]]

boolFsChallenges :: Int -> [Int]
boolFsChallenges base =
  binaryFsChallenges 1 [base]

sigmaResponseRounds :: (w -> m -> Int -> z) -> w -> [m] -> [Int] -> [z]
sigmaResponseRounds respond witness masks challenges =
  map (uncurry (respond witness)) (zip masks challenges)
