module Canon.ZK.Internal.RepeatedFS
  ( fixedFsRounds
  , binaryFsChallenge
  , binaryFsChallenges
  , boolFsChallenges
  , sigmaResponseRounds
  ) where

fixedFsRounds :: Int
fixedFsRounds = 128

euclideanMod :: Int -> Int -> Int
euclideanMod x q =
  let r = mod x q
   in if r < 0 then r + q else r

fsChallengeCardinality :: Int
fsChallengeCardinality = 2

transcriptMix :: [Int] -> Int
transcriptMix =
  foldl
    (\acc x -> euclideanMod (acc * 257 + euclideanMod x 2097143 + 65537) 2097143)
    104729

binaryFsChallenge :: Int -> [Int] -> Int -> Int
binaryFsChallenge domain fields roundIndex =
  euclideanMod (transcriptMix (domain : roundIndex : fields)) fsChallengeCardinality

binaryFsChallenges :: Int -> [Int] -> [Int]
binaryFsChallenges domain fields =
  [binaryFsChallenge domain fields i | i <- [0 .. fixedFsRounds - 1]]

boolFsChallenges :: Int -> [Int]
boolFsChallenges base =
  binaryFsChallenges 1 [base]

sigmaResponseRounds :: (w -> m -> Int -> z) -> w -> [m] -> [Int] -> [z]
sigmaResponseRounds respond witness masks challenges =
  map (uncurry (respond witness)) (zip masks challenges)
