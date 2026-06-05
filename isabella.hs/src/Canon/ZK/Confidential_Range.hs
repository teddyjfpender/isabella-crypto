-- | Canon.ZK.Confidential_Range: native Haskell facade for the
-- confidential-range proof slice exported from Canon.
module Canon.ZK.Confidential_Range
  ( RangeProof(..)
  , makeRangeProof
  , oneOpening
  , openingScale
  , validBitOpening
  , bitPairRelation
  , weightedOpening
  , weightedCommitment
  , rangeAmountOpening
  , rangeAmountRandomness
  , rangePairOpening
  , rangePairRandomness
  , rangePairRandomnesses
  , oneCommitment
  , rangeAmountCommitment
  , rangePairCommitment
  , rangePairCommitments
  , rangeRelation
  , rangeAmountWitnessBound
  , rangePairWitnessBound
  , validRangeAmountWitness
  , validRangePairWitness
  , validRangeMask
  , rangeAmountResponseBound
  , rangePairResponseBound
  , validRangeChallenge
  , validRangeAmountResponse
  , validRangePairResponse
  , rangeFsRounds
  , rangeFsChallenges
  , rangeAmountSigmaAnnouncements
  , rangeAmountSigmaResponses
  , rangePairSigmaAnnouncementRounds
  , rangePairSigmaResponseRounds
  , rangeSigmaAnnouncements
  , rangeSigmaResponses
  , canonicalRangeChallenge
  , rangeAmountSigmaVerify
  , rangePairSigmaVerify
  , rangeSigmaVerifyPairs
  , rangeFsProve
  , rangeFsVerify
  ) where

import qualified Canon.Commit_sis as Commit
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Decomp as Decomp
import qualified Canon.Listvec as Listvec
import qualified Canon.Norms as Norms
import qualified Canon.ZK.Internal.RepeatedFS as RepeatedFS
import qualified Canon.Zq as Zq

data RangeProof = RangeProof
  { range_bits :: [[Int]]
  , range_comps :: [[Int]]
  , range_amount_as :: [[Int]]
  , range_amount_zs :: [[Int]]
  , range_pair_ass :: [[[Int]]]
  , range_pair_zss :: [[[Int]]]
  }
  deriving (Eq, Show)

makeRangeProof :: [[Int]] -> [[Int]] -> [[Int]] -> [[Int]] -> [[[Int]]] -> [[[Int]]] -> RangeProof
makeRangeProof = RangeProof

oneOpening :: Commit.CommitParams -> Commit.CommitOpening
oneOpening p = Commit.makeOpening [1] (replicate (Commit.cp_n2 p) 0)

openingScale :: Int -> Commit.CommitOpening -> Commit.CommitOpening
openingScale k op =
  Commit.makeOpening
    (Listvec.scalar_mult k (Commit.open_msg op))
    (Listvec.scalar_mult k (Commit.open_rand op))

-- Keep the exported relation logic explicit rather than clever.
validBitOpening :: Commit.CommitParams -> Commit.CommitOpening -> Bool
validBitOpening p op =
  ConfidentialBalance.validScalarCommitParams p &&
  Commit.validOpening p op &&
  Norms.all_bounded (Commit.open_msg op) 1

bitPairRelation :: Commit.CommitParams -> Commit.CommitOpening -> Commit.CommitOpening -> Bool
bitPairRelation p opBit opComp =
  validBitOpening p opBit &&
  validBitOpening p opComp &&
  ConfidentialBalance.amountOfOpening opBit + ConfidentialBalance.amountOfOpening opComp == 1

allBitPairs :: Commit.CommitParams -> [Commit.CommitOpening] -> [Commit.CommitOpening] -> Bool
allBitPairs _ [] [] = True
allBitPairs p (opBit : opsBits) (opComp : opsComps) =
  bitPairRelation p opBit opComp && allBitPairs p opsBits opsComps
allBitPairs _ _ _ = False

weightedOpening :: Commit.CommitParams -> Int -> [Commit.CommitOpening] -> Commit.CommitOpening
weightedOpening p _ [] = Commit.makeOpening [0] (replicate (Commit.cp_n2 p) 0)
weightedOpening p b (op : ops) =
  let rest = weightedOpening p b ops
   in Commit.makeOpening
        (Listvec.vec_add (Commit.open_msg op) (Listvec.scalar_mult b (Commit.open_msg rest)))
        (Listvec.vec_add (Commit.open_rand op) (Listvec.scalar_mult b (Commit.open_rand rest)))

weightedCommitment :: Commit.CommitParams -> [[Int]] -> Int -> [[Int]] -> [Int]
weightedCommitment p ck _ [] =
  ConfidentialBalance.randCommit p ck (replicate (Commit.cp_n2 p) 0)
weightedCommitment p ck b (c : cs) =
  Zq.vec_mod
    (Listvec.vec_add c (Listvec.scalar_mult b (weightedCommitment p ck b cs)))
    (Commit.cp_q p)

rangeAmountOpening :: Commit.CommitParams -> Commit.CommitOpening -> [Commit.CommitOpening] -> Commit.CommitOpening
rangeAmountOpening p opAmount opsBits =
  Commit.makeOpening
    (Listvec.vec_sub (Commit.open_msg opAmount) (Commit.open_msg (weightedOpening p 2 opsBits)))
    (Listvec.vec_sub (Commit.open_rand opAmount) (Commit.open_rand (weightedOpening p 2 opsBits)))

rangeAmountRandomness :: Commit.CommitParams -> Commit.CommitOpening -> [Commit.CommitOpening] -> [Int]
rangeAmountRandomness p opAmount opsBits = Commit.open_rand (rangeAmountOpening p opAmount opsBits)

rangePairOpening :: Commit.CommitParams -> Commit.CommitOpening -> Commit.CommitOpening -> Commit.CommitOpening
rangePairOpening p opBit opComp =
  let one = oneOpening p
      sumMsg = Listvec.vec_add (Commit.open_msg opBit) (Commit.open_msg opComp)
      sumRand = Listvec.vec_add (Commit.open_rand opBit) (Commit.open_rand opComp)
   in Commit.makeOpening
        (Listvec.vec_sub sumMsg (Commit.open_msg one))
        (Listvec.vec_sub sumRand (Commit.open_rand one))

rangePairRandomness :: Commit.CommitParams -> Commit.CommitOpening -> Commit.CommitOpening -> [Int]
rangePairRandomness p opBit opComp = Commit.open_rand (rangePairOpening p opBit opComp)

rangePairRandomnesses :: Commit.CommitParams -> [Commit.CommitOpening] -> [Commit.CommitOpening] -> [[Int]]
rangePairRandomnesses _ [] [] = []
rangePairRandomnesses p (opBit : opsBits) (opComp : opsComps) =
  rangePairRandomness p opBit opComp : rangePairRandomnesses p opsBits opsComps
rangePairRandomnesses _ _ _ = []

oneCommitment :: Commit.CommitParams -> [[Int]] -> [Int]
oneCommitment p ck = Commit.commit ck (oneOpening p) (Commit.cp_q p)

rangeAmountCommitment :: Commit.CommitParams -> [[Int]] -> [Int] -> [[Int]] -> [Int]
rangeAmountCommitment p ck cAmount cBits =
  Zq.vec_mod
    (Listvec.vec_sub cAmount (weightedCommitment p ck 2 cBits))
    (Commit.cp_q p)

rangePairCommitment :: Commit.CommitParams -> [[Int]] -> [Int] -> [Int] -> [Int]
rangePairCommitment p ck cBit cComp =
  Zq.vec_mod
    (Listvec.vec_sub (Listvec.vec_add cBit cComp) (oneCommitment p ck))
    (Commit.cp_q p)

rangePairCommitments :: Commit.CommitParams -> [[Int]] -> [[Int]] -> [[Int]] -> [[Int]]
rangePairCommitments _ _ [] [] = []
rangePairCommitments p ck (cBit : cBits) (cComp : cComps) =
  rangePairCommitment p ck cBit cComp : rangePairCommitments p ck cBits cComps
rangePairCommitments _ _ _ _ = []

rangeRelation ::
  Commit.CommitParams ->
  [[Int]] ->
  [Int] ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  Bool
rangeRelation p ck cAmount opAmount opsBits opsComps =
  ConfidentialBalance.validScalarCommitParams p &&
  ConfidentialBalance.validConfidentialCommitKey p ck &&
  Commit.validOpening p opAmount &&
  Commit.verify_opening ck opAmount cAmount (Commit.cp_q p) &&
  allBitPairs p opsBits opsComps &&
  ConfidentialBalance.amountOfOpening opAmount ==
    Decomp.recompose 2 (map ConfidentialBalance.amountOfOpening opsBits)

rangeAmountWitnessBound :: Commit.CommitParams -> Int -> Int
rangeAmountWitnessBound p k = (2 ^ k) * Commit.cp_beta p

rangePairWitnessBound :: Commit.CommitParams -> Int
rangePairWitnessBound p = 2 * Commit.cp_beta p

validRangeAmountWitness :: Commit.CommitParams -> Int -> [Int] -> Bool
validRangeAmountWitness p k r =
  Listvec.valid_vec (Commit.cp_n2 p) r &&
  Norms.all_bounded r (rangeAmountWitnessBound p k)

validRangePairWitness :: Commit.CommitParams -> [Int] -> Bool
validRangePairWitness p r =
  Listvec.valid_vec (Commit.cp_n2 p) r &&
  Norms.all_bounded r (rangePairWitnessBound p)

validRangeMask :: Commit.CommitParams -> Int -> [Int] -> Bool
validRangeMask p gamma y =
  Listvec.valid_vec (Commit.cp_n2 p) y &&
  Norms.all_bounded y gamma

rangeAmountResponseBound :: Commit.CommitParams -> Int -> Int -> Int -> Int
rangeAmountResponseBound p gamma k challenge =
  gamma + abs challenge * rangeAmountWitnessBound p k

rangePairResponseBound :: Commit.CommitParams -> Int -> Int -> Int
rangePairResponseBound p gamma challenge =
  gamma + abs challenge * rangePairWitnessBound p

validRangeChallenge :: Commit.CommitParams -> Int -> Bool
validRangeChallenge = ConfidentialBalance.validBalanceChallenge

validRangeAmountResponse :: Commit.CommitParams -> Int -> Int -> Int -> [Int] -> Bool
validRangeAmountResponse p gamma k challenge z =
  Listvec.valid_vec (Commit.cp_n2 p) z &&
  Norms.all_bounded z (rangeAmountResponseBound p gamma k challenge)

validRangePairResponse :: Commit.CommitParams -> Int -> Int -> [Int] -> Bool
validRangePairResponse p gamma challenge z =
  Listvec.valid_vec (Commit.cp_n2 p) z &&
  Norms.all_bounded z (rangePairResponseBound p gamma challenge)

validRangeMasks :: Commit.CommitParams -> Int -> [[Int]] -> Bool
validRangeMasks p gamma = all (validRangeMask p gamma)

validRangePairResponses :: Commit.CommitParams -> Int -> Int -> [[Int]] -> Bool
validRangePairResponses p gamma challenge = all (validRangePairResponse p gamma challenge)

rangeFsRounds :: Int
rangeFsRounds = ConfidentialBalance.balanceFsRounds

rangeFsChallenges ::
  Commit.CommitParams ->
  [[Int]] ->
  [Int] ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [[[Int]]] ->
  [Int]
rangeFsChallenges _p ck cAmount cBits cComps aAmounts aPairss =
  let challengeBase =
        sum (concat ck) +
        sum cAmount +
        sum (concat cBits) +
        sum (concat cComps) +
        sum (concat aAmounts) +
        sum (concat (concat aPairss))
   in RepeatedFS.boolFsChallenges challengeBase

rangeAmountSigmaAnnouncements :: Commit.CommitParams -> [[Int]] -> [[Int]] -> [[Int]]
rangeAmountSigmaAnnouncements p ck = map (ConfidentialBalance.randCommit p ck)

rangeAmountSigmaResponses :: [Int] -> [[Int]] -> [Int] -> [[Int]]
rangeAmountSigmaResponses rAmount yAmounts challenges =
  zipWith (ConfidentialBalance.balanceSigmaRespond rAmount) yAmounts challenges

rangePairSigmaAnnouncementRounds ::
  Commit.CommitParams ->
  [[Int]] ->
  [[[Int]]] ->
  [[[Int]]]
rangePairSigmaAnnouncementRounds p ck = map (rangeSigmaAnnouncements p ck)

rangePairSigmaResponseRounds ::
  [[Int]] ->
  [[[Int]]] ->
  [Int] ->
  [[[Int]]]
rangePairSigmaResponseRounds rs yPairss challenges =
  RepeatedFS.sigmaResponseRounds rangeSigmaResponses rs yPairss challenges

rangeSigmaAnnouncements :: Commit.CommitParams -> [[Int]] -> [[Int]] -> [[Int]]
rangeSigmaAnnouncements p ck = map (ConfidentialBalance.randCommit p ck)

rangeSigmaResponses :: [[Int]] -> [[Int]] -> Int -> [[Int]]
rangeSigmaResponses [] [] _ = []
rangeSigmaResponses (r : rs) (y : ys) challenge =
  ConfidentialBalance.balanceSigmaRespond r y challenge : rangeSigmaResponses rs ys challenge
rangeSigmaResponses _ _ _ = []

canonicalRangeChallenge ::
  Commit.CommitParams ->
  [[Int]] ->
  [Int] ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [[[Int]]] ->
  Int
canonicalRangeChallenge p ck cAmount cBits cComps aAmounts aPairss =
  mod
    ( sum (concat ck)
    + sum cAmount
    + sum (concat cBits)
    + sum (concat cComps)
    + sum (concat aAmounts)
    + sum (concat (concat aPairss))
    )
    2

rangeAmountSigmaVerify ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Int ->
  [Int] ->
  Bool
rangeAmountSigmaVerify p gamma k ck c a challenge z =
  ConfidentialBalance.validScalarCommitParams p &&
  ConfidentialBalance.validConfidentialCommitKey p ck &&
  Listvec.valid_vec (Commit.cp_m p) a &&
  validRangeChallenge p challenge &&
  validRangeAmountResponse p gamma k challenge z &&
  ConfidentialBalance.randCommit p ck z ==
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) (Commit.cp_q p)

rangePairSigmaVerify ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Int ->
  [Int] ->
  Bool
rangePairSigmaVerify p gamma ck c a challenge z =
  ConfidentialBalance.validScalarCommitParams p &&
  ConfidentialBalance.validConfidentialCommitKey p ck &&
  Listvec.valid_vec (Commit.cp_m p) a &&
  validRangeChallenge p challenge &&
  validRangePairResponse p gamma challenge z &&
  ConfidentialBalance.randCommit p ck z ==
    Zq.vec_mod (Listvec.vec_add a (Listvec.scalar_mult challenge c)) (Commit.cp_q p)

rangeSigmaVerifyPairs ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  Int ->
  [[Int]] ->
  Bool
rangeSigmaVerifyPairs _ _ _ [] [] _ [] = True
rangeSigmaVerifyPairs p gamma ck (c : cs) (a : as) challenge (z : zs) =
  rangePairSigmaVerify p gamma ck c a challenge z &&
  rangeSigmaVerifyPairs p gamma ck cs as challenge zs
rangeSigmaVerifyPairs _ _ _ _ _ _ _ = False

rangeFsProve ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [Int] ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [[Int]] ->
  [[[Int]]] ->
  Maybe RangeProof
rangeFsProve p gamma k ck cAmount opAmount opsBits opsComps yAmounts yPairss =
  let cBits = map (\op -> Commit.commit ck op (Commit.cp_q p)) opsBits
      cComps = map (\op -> Commit.commit ck op (Commit.cp_q p)) opsComps
      rAmount = rangeAmountRandomness p opAmount opsBits
      rPairs = rangePairRandomnesses p opsBits opsComps
      aAmounts = rangeAmountSigmaAnnouncements p ck yAmounts
      aPairss = rangePairSigmaAnnouncementRounds p ck yPairss
      challenges = rangeFsChallenges p ck cAmount cBits cComps aAmounts aPairss
      zAmounts = rangeAmountSigmaResponses rAmount yAmounts challenges
      zPairss = rangePairSigmaResponseRounds rPairs yPairss challenges
   in if rangeRelation p ck cAmount opAmount opsBits opsComps &&
         length opsBits == k &&
         length opsComps == k &&
         length yAmounts == rangeFsRounds &&
         length yPairss == rangeFsRounds &&
         and [validRangeMask p gamma (yAmounts !! i) | i <- [0 .. rangeFsRounds - 1]] &&
         and
           [ length (yPairss !! i) == k &&
             validRangeMasks p gamma (yPairss !! i)
           | i <- [0 .. rangeFsRounds - 1]
           ] &&
         and
           [ validRangeAmountResponse p gamma k (challenges !! i) (zAmounts !! i)
           | i <- [0 .. rangeFsRounds - 1]
           ] &&
         and
           [ length (zPairss !! i) == k &&
             validRangePairResponses p gamma (challenges !! i) (zPairss !! i)
           | i <- [0 .. rangeFsRounds - 1]
           ]
        then Just (RangeProof cBits cComps aAmounts zAmounts aPairss zPairss)
        else Nothing

rangeFsVerify :: Commit.CommitParams -> Int -> Int -> [[Int]] -> [Int] -> RangeProof -> Bool
rangeFsVerify p gamma k ck cAmount proof =
  let cBits = range_bits proof
      cComps = range_comps proof
      aAmounts = range_amount_as proof
      aPairss = range_pair_ass proof
      zAmounts = range_amount_zs proof
      zPairss = range_pair_zss proof
      challenges = rangeFsChallenges p ck cAmount cBits cComps aAmounts aPairss
      cAmountRes = rangeAmountCommitment p ck cAmount cBits
      cPairRes = rangePairCommitments p ck cBits cComps
   in Listvec.valid_vec (Commit.cp_m p) cAmount &&
      length cBits == k &&
      length cComps == k &&
      length aAmounts == rangeFsRounds &&
      length aPairss == rangeFsRounds &&
      length zAmounts == rangeFsRounds &&
      length zPairss == rangeFsRounds &&
      and
        [ length (aPairss !! i) == k &&
          length (zPairss !! i) == k &&
          rangeAmountSigmaVerify p gamma k ck cAmountRes (aAmounts !! i) (challenges !! i) (zAmounts !! i) &&
          rangeSigmaVerifyPairs p gamma ck cPairRes (aPairss !! i) (challenges !! i) (zPairss !! i)
        | i <- [0 .. rangeFsRounds - 1]
        ]
