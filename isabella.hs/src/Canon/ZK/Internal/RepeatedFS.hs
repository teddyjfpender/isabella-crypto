module Canon.ZK.Internal.RepeatedFS
  ( fixedFsRounds
  , boolFsChallenges
  , sigmaResponseRounds
  ) where

fixedFsRounds :: Int
fixedFsRounds = 8

boolFsChallenges :: Int -> [Int]
boolFsChallenges base =
  [mod (base + i) 2 | i <- [0 .. fixedFsRounds - 1]]

sigmaResponseRounds :: (w -> m -> Int -> z) -> w -> [m] -> [Int] -> [z]
sigmaResponseRounds respond witness masks challenges =
  map (uncurry (respond witness)) (zip masks challenges)
