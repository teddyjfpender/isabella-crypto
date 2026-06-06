-- | CSPRNG-backed helpers for confidential-transfer masks.
module Canon.Confidential_sampling
  ( maxArrayLength
  , maxSamplingBound
  , sampleBoundedInt
  , sampleIntVector
  , sampleIntVectors
  , sampleOpening
  , sampleOpenings
  ) where

import Control.Monad (replicateM)
import qualified Canon.Commit_sis as Commit
import Data.Bits ((.&.), (.|.), shiftL)
import Data.Char (ord)
import Data.Word (Word64)
import System.IO (Handle, IOMode(ReadMode), hGetChar, hSetBinaryMode, withBinaryFile)

maxArrayLength :: Int
maxArrayLength = 1000000

maxSamplingBound :: Int
maxSamplingBound = 2 ^ (52 :: Int) - 1

randomSource :: FilePath
randomSource = "/dev/urandom"

validateLength :: Int -> IO ()
validateLength length_
    | length_ < 0 || length_ > maxArrayLength =
        ioError (userError "confidential sampler length out of range")
    | otherwise = pure ()

validateBound :: Int -> IO ()
validateBound bound
    | bound < 0 || bound > maxSamplingBound =
        ioError (userError "confidential sampler bound out of range")
    | otherwise = pure ()

validateAllocation :: Int -> Int -> IO ()
validateAllocation count width = do
    validateLength count
    validateLength width
    if count > 0 && width > maxArrayLength `div` count
        then ioError (userError "confidential sampler allocation out of range")
        else pure ()

random53From :: Handle -> IO Integer
random53From handle = do
    bytes <- replicateM 7 (fromIntegral . ord <$> hGetChar handle :: IO Word64)
    let raw = foldr (.|.) 0 (zipWith shiftByte bytes [0, 8 .. 48])
    pure $ toInteger (raw .&. ((1 `shiftL` 53) - 1))
  where
    shiftByte byte shift = byte `shiftL` shift

sampleBoundedIntFrom :: Handle -> Int -> IO Int
sampleBoundedIntFrom handle bound = do
    validateBound bound
    let boundInteger = toInteger bound
        range = 2 * boundInteger + 1
        sampleSpace = (1 :: Integer) `shiftL` (53 :: Int)
        limit = sampleSpace - (sampleSpace `mod` range)
        draw = do
            sample <- random53From handle
            if sample >= limit
                then draw
                else pure $ fromInteger ((sample `mod` range) - boundInteger)
    draw

sampleBoundedInt :: Int -> IO Int
sampleBoundedInt bound =
    withBinaryFile randomSource ReadMode $ \handle -> do
        hSetBinaryMode handle True
        sampleBoundedIntFrom handle bound

sampleIntVector :: Int -> Int -> IO [Int]
sampleIntVector length_ bound = do
    validateLength length_
    withBinaryFile randomSource ReadMode $ \handle -> do
        hSetBinaryMode handle True
        replicateM length_ (sampleBoundedIntFrom handle bound)

sampleIntVectors :: Int -> Int -> Int -> IO [[Int]]
sampleIntVectors count length_ bound = do
    validateAllocation count length_
    withBinaryFile randomSource ReadMode $ \handle -> do
        hSetBinaryMode handle True
        replicateM count (replicateM length_ (sampleBoundedIntFrom handle bound))

sampleOpeningFrom :: Handle -> Int -> Int -> Int -> IO Commit.CommitOpening
sampleOpeningFrom handle msgLength randLength bound = do
    validateLength msgLength
    validateLength randLength
    validateAllocation 1 (msgLength + randLength)
    msg <- replicateM msgLength (sampleBoundedIntFrom handle bound)
    rand <- replicateM randLength (sampleBoundedIntFrom handle bound)
    pure $ Commit.makeOpening msg rand

sampleOpening :: Int -> Int -> Int -> IO Commit.CommitOpening
sampleOpening msgLength randLength bound =
    withBinaryFile randomSource ReadMode $ \handle -> do
        hSetBinaryMode handle True
        sampleOpeningFrom handle msgLength randLength bound

sampleOpenings :: Int -> Int -> Int -> Int -> IO [Commit.CommitOpening]
sampleOpenings count msgLength randLength bound = do
    validateAllocation count (msgLength + randLength)
    withBinaryFile randomSource ReadMode $ \handle -> do
        hSetBinaryMode handle True
        replicateM count (sampleOpeningFrom handle msgLength randLength bound)
