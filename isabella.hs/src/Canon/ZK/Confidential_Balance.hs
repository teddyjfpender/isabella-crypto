-- | Canon.ZK.Confidential_Balance: native Haskell facade for the
-- confidential-balance proof slice exported from Canon.
module Canon.ZK.Confidential_Balance
  ( BalanceProof(..)
  , makeBalanceProof
  , balanceFsRounds
  , makeScalarCommitParams
  , validScalarCommitParams
  , validConfidentialCommitKey
  , randCommitKey
  , randCommit
  , amountOfOpening
  , balanceCommitment
  , aggregateRandomness
  , validBalanceWitness
  , validBalanceMask
  , balanceResponseBound
  , validBalanceChallenge
  , validBalanceResponse
  , balanceRelation
  , balanceSigmaCommit
  , balanceSigmaRespond
  , canonicalBalanceChallenge
  , balanceSigmaVerify
  , balanceFsChallenges
  , balanceSigmaResponds
  , balanceFsProve
  , balanceFsVerify
  ) where

import qualified Canon.Commit_sis as Commit
import qualified Canon.Listvec as Listvec
import qualified Canon.Norms as Norms
import qualified Canon.ZK.Internal.RepeatedFS as RepeatedFS
import qualified Canon.Zq as Zq

data BalanceProof = BalanceProof
  { balance_as :: [[Int]]
  , balance_zs :: [[Int]]
  }
  deriving (Eq, Show)

makeBalanceProof :: [[Int]] -> [[Int]] -> BalanceProof
makeBalanceProof = BalanceProof

balanceFsRounds :: Int
balanceFsRounds = RepeatedFS.fixedFsRounds

makeScalarCommitParams :: Int -> Int -> Int -> Int -> Commit.CommitParams
makeScalarCommitParams m n2 q beta = Commit.makeCommitParams 1 n2 m q beta

validScalarCommitParams :: Commit.CommitParams -> Bool
validScalarCommitParams p = Commit.validCommitParams p && Commit.cp_n1 p == 1

validConfidentialCommitKey :: Commit.CommitParams -> [[Int]] -> Bool
validConfidentialCommitKey = Commit.separating_commit_key

randCommitKey :: Commit.CommitParams -> [[Int]] -> [[Int]]
randCommitKey p = map (drop (Commit.cp_n1 p))

randCommit :: Commit.CommitParams -> [[Int]] -> [Int] -> [Int]
randCommit p ck r =
  Zq.vec_mod (Listvec.mat_vec_mult (randCommitKey p ck) r) (Commit.cp_q p)

amountOfOpening :: Commit.CommitOpening -> Int
amountOfOpening op =
  case Commit.open_msg op of
    x : _ -> x
    [] -> 0

openingAdd :: Commit.CommitOpening -> Commit.CommitOpening -> Commit.CommitOpening
openingAdd op1 op2 =
  Commit.makeOpening
    (Listvec.vec_add (Commit.open_msg op1) (Commit.open_msg op2))
    (Listvec.vec_add (Commit.open_rand op1) (Commit.open_rand op2))

openingSub :: Commit.CommitOpening -> Commit.CommitOpening -> Commit.CommitOpening
openingSub op1 op2 =
  Commit.makeOpening
    (Listvec.vec_sub (Commit.open_msg op1) (Commit.open_msg op2))
    (Listvec.vec_sub (Commit.open_rand op1) (Commit.open_rand op2))

aggregateOpening ::
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening
aggregateOpening opIn1 opIn2 opOut1 opOut2 =
  openingSub (openingAdd opIn1 opIn2) (openingAdd opOut1 opOut2)

aggregateRandomness ::
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  [Int]
aggregateRandomness opIn1 opIn2 opOut1 opOut2 =
  Commit.open_rand (aggregateOpening opIn1 opIn2 opOut1 opOut2)

balanceCommitment :: [Int] -> [Int] -> [Int] -> [Int] -> Int -> [Int]
balanceCommitment cIn1 cIn2 cOut1 cOut2 q =
  Zq.vec_mod
    (Listvec.vec_sub (Listvec.vec_add cIn1 cIn2) (Listvec.vec_add cOut1 cOut2))
    q

validBalanceWitness :: Commit.CommitParams -> [Int] -> Bool
validBalanceWitness p r =
  Listvec.valid_vec (Commit.cp_n2 p) r &&
  Norms.all_bounded r (4 * Commit.cp_beta p)

validBalanceMask :: Commit.CommitParams -> Int -> [Int] -> Bool
validBalanceMask p gamma y =
  Listvec.valid_vec (Commit.cp_n2 p) y &&
  Norms.all_bounded y gamma

balanceResponseBound :: Commit.CommitParams -> Int -> Int -> Int
balanceResponseBound p gamma challenge =
  gamma + abs challenge * (4 * Commit.cp_beta p)

validBalanceChallenge :: Commit.CommitParams -> Int -> Bool
validBalanceChallenge p challenge =
  validScalarCommitParams p &&
  (challenge == 0 || challenge == 1)

validBalanceResponse :: Commit.CommitParams -> Int -> Int -> [Int] -> Bool
validBalanceResponse p gamma challenge z =
  Listvec.valid_vec (Commit.cp_n2 p) z &&
  Norms.all_bounded z (balanceResponseBound p gamma challenge)

balanceRelation :: Commit.CommitParams -> [[Int]] -> [Int] -> [Int] -> Bool
balanceRelation p ck c r =
  validScalarCommitParams p &&
  validConfidentialCommitKey p ck &&
  validBalanceWitness p r &&
  randCommit p ck r == c

balanceSigmaCommit :: Commit.CommitParams -> [[Int]] -> [Int] -> [Int]
balanceSigmaCommit = randCommit

balanceSigmaRespond :: [Int] -> [Int] -> Int -> [Int]
balanceSigmaRespond r y challenge =
  Listvec.vec_add y (Listvec.scalar_mult challenge r)

canonicalBalanceChallenge :: Commit.CommitParams -> [[Int]] -> [Int] -> [Int] -> Int
canonicalBalanceChallenge p ck c a =
  mod (sum (concat ck) + sum c + sum a) 2

balanceSigmaVerify ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Int ->
  [Int] ->
  Bool
balanceSigmaVerify p gamma ck c a challenge z =
  validScalarCommitParams p &&
  validConfidentialCommitKey p ck &&
  Listvec.valid_vec (Commit.cp_m p) a &&
  validBalanceChallenge p challenge &&
  validBalanceResponse p gamma challenge z &&
  randCommit p ck z ==
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) (Commit.cp_q p)

balanceFsChallenges :: Commit.CommitParams -> [[Int]] -> [Int] -> [[Int]] -> [Int]
balanceFsChallenges _ ck c as =
  RepeatedFS.boolFsChallenges (sum (concat ck) + sum c + sum (concat as))

balanceSigmaResponds :: [Int] -> [[Int]] -> [Int] -> [[Int]]
balanceSigmaResponds r ys es =
  RepeatedFS.sigmaResponseRounds balanceSigmaRespond r ys es

balanceFsProve ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [[Int]] ->
  Maybe BalanceProof
balanceFsProve p gamma ck c r ys =
  let as = map (balanceSigmaCommit p ck) ys
      es = balanceFsChallenges p ck c as
      zs = balanceSigmaResponds r ys es
      validMasks = length ys == balanceFsRounds &&
        and [validBalanceMask p gamma (ys !! i) | i <- [0 .. balanceFsRounds - 1]]
      validResponses = length zs == balanceFsRounds &&
        and [validBalanceResponse p gamma (es !! i) (zs !! i) | i <- [0 .. balanceFsRounds - 1]]
   in if balanceRelation p ck c r &&
         validMasks &&
         validResponses
        then Just (BalanceProof as zs)
        else Nothing

balanceFsVerify ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [Int] ->
  BalanceProof ->
  Bool
balanceFsVerify p gamma ck c proof =
  let as = balance_as proof
      es = balanceFsChallenges p ck c as
      zs = balance_zs proof
   in length as == balanceFsRounds &&
      length zs == balanceFsRounds &&
      and
        [ balanceSigmaVerify p gamma ck c (as !! i) (es !! i) (zs !! i)
        | i <- [0 .. balanceFsRounds - 1]
        ]
