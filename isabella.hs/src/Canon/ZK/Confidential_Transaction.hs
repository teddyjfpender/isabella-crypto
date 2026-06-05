-- | Canon.ZK.Confidential_Transaction: native Haskell facade for the
-- confidential-transaction proof slice exported from Canon.
module Canon.ZK.Confidential_Transaction
  ( NullifierProof(..)
  , makeNullifierProof
  , MembershipProof(..)
  , makeMembershipProof
  , VerifiedNote(..)
  , makeVerifiedNote
  , TransactionProof(..)
  , makeTransactionProof
  , nullifier
  , validNullifierMask
  , validNullifierResponse
  , nullifierRelation
  , nullifierFsRounds
  , nullifierFsChallenges
  , canonicalNullifierChallenge
  , nullifierSigmaVerify
  , nullifierFsProve
  , nullifierFsVerify
  , emptyCommitment
  , ledgerHash
  , ledgerRoot
  , membershipProve
  , membershipVerify
  , commitmentLedger
  , ledgerValid
  , ledgerStepValid
  , semanticStepValid
  , transactionRelation
  , transactionFsProve
  , transactionFsVerify
  , ledgerApplyNotes
  , ledgerApplySpent
  ) where

import Data.List (delete, nub)
import qualified Canon.Commit_sis as Commit
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Listvec as Listvec
import qualified Canon.Norms as Norms
import qualified Canon.ZK.Internal.RepeatedFS as RepeatedFS
import qualified Canon.Zq as Zq

data NullifierProof = NullifierProof
  { nullifier_a_commits :: [[Int]]
  , nullifier_a_nullifiers :: [[Int]]
  , nullifier_z_msgs :: [[Int]]
  , nullifier_z_rands :: [[Int]]
  }
  deriving (Eq, Show)

makeNullifierProof :: [[Int]] -> [[Int]] -> [[Int]] -> [[Int]] -> NullifierProof
makeNullifierProof = NullifierProof

data MembershipProof = MembershipProof
  { member_index :: Int
  , member_root :: [Int]
  , member_siblings :: [[Int]]
  , member_directions :: [Bool]
  }
  deriving (Eq, Show)

makeMembershipProof :: Int -> [Int] -> [[Int]] -> [Bool] -> MembershipProof
makeMembershipProof = MembershipProof

data VerifiedNote = VerifiedNote
  { note_commitment :: [Int]
  , note_range_proof :: ConfidentialRange.RangeProof
  }
  deriving (Eq, Show)

makeVerifiedNote :: [Int] -> ConfidentialRange.RangeProof -> VerifiedNote
makeVerifiedNote = VerifiedNote

data TransactionProof = TransactionProof
  { tx_in1_member :: MembershipProof
  , tx_in2_member :: MembershipProof
  , tx_in1_nullifier :: NullifierProof
  , tx_in2_nullifier :: NullifierProof
  , tx_balance :: ConfidentialBalance.BalanceProof
  , tx_out1_range :: ConfidentialRange.RangeProof
  , tx_out2_range :: ConfidentialRange.RangeProof
  }
  deriving (Eq, Show)

makeTransactionProof ::
  MembershipProof ->
  MembershipProof ->
  NullifierProof ->
  NullifierProof ->
  ConfidentialBalance.BalanceProof ->
  ConfidentialRange.RangeProof ->
  ConfidentialRange.RangeProof ->
  TransactionProof
makeTransactionProof = TransactionProof

validCommitment :: Commit.CommitParams -> [Int] -> Bool
validCommitment p = Listvec.valid_vec (Commit.cp_m p)

openingAdd :: Commit.CommitOpening -> Commit.CommitOpening -> Commit.CommitOpening
openingAdd op1 op2 =
  Commit.makeOpening
    (Listvec.vec_add (Commit.open_msg op1) (Commit.open_msg op2))
    (Listvec.vec_add (Commit.open_rand op1) (Commit.open_rand op2))

nullifierFsRounds :: Int
nullifierFsRounds = ConfidentialBalance.balanceFsRounds

nullifierFsDomain :: Int
nullifierFsDomain = 3001

nullifierFsFields :: [[Int]] -> [[Int]] -> [Int] -> [Int] -> [[Int]] -> [[Int]] -> [Int]
nullifierFsFields ck nk c nf aCommits aNullifiers =
  [ sum (concat ck)
  , sum (concat nk)
  , sum c
  , sum nf
  , sum (concat aCommits)
  , sum (concat aNullifiers)
  ]

nullifierSigmaRespond :: Commit.CommitOpening -> Commit.CommitOpening -> Int -> Commit.CommitOpening
nullifierSigmaRespond op y challenge =
  openingAdd y (ConfidentialRange.openingScale challenge op)

nullifierFsChallenges ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [[Int]] ->
  [[Int]] ->
  [Int]
nullifierFsChallenges _p ck nk c nf aCommits aNullifiers =
  RepeatedFS.binaryFsChallenges
    nullifierFsDomain
    (nullifierFsFields ck nk c nf aCommits aNullifiers)

nullifierZOpenings :: NullifierProof -> [Commit.CommitOpening]
nullifierZOpenings proof =
  zipWith Commit.makeOpening
    (nullifier_z_msgs proof)
    (nullifier_z_rands proof)

nullifier :: Commit.CommitParams -> [[Int]] -> Commit.CommitOpening -> [Int]
nullifier p nk op = Commit.commit nk op (Commit.cp_q p)

validNullifierMask :: Commit.CommitParams -> Int -> Commit.CommitOpening -> Bool
validNullifierMask p gamma y =
  Listvec.valid_vec (Commit.cp_n1 p) (Commit.open_msg y) &&
  Listvec.valid_vec (Commit.cp_n2 p) (Commit.open_rand y) &&
  Norms.all_bounded (Commit.open_msg y) gamma &&
  Norms.all_bounded (Commit.open_rand y) gamma

nullifierResponseBound :: Commit.CommitParams -> Int -> Int -> Int
nullifierResponseBound p gamma challenge =
  gamma + abs challenge * Commit.cp_beta p

validNullifierChallenge :: Commit.CommitParams -> Int -> Bool
validNullifierChallenge = ConfidentialBalance.validBalanceChallenge

validNullifierResponse :: Commit.CommitParams -> Int -> Int -> Commit.CommitOpening -> Bool
validNullifierResponse p gamma challenge z =
  Listvec.valid_vec (Commit.cp_n1 p) (Commit.open_msg z) &&
  Listvec.valid_vec (Commit.cp_n2 p) (Commit.open_rand z) &&
  Norms.all_bounded (Commit.open_msg z) (nullifierResponseBound p gamma challenge) &&
  Norms.all_bounded (Commit.open_rand z) (nullifierResponseBound p gamma challenge)

nullifierRelation ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  Bool
nullifierRelation p ck nk c nf op =
  ConfidentialBalance.validScalarCommitParams p &&
  ConfidentialBalance.validConfidentialCommitKey p ck &&
  ConfidentialBalance.validConfidentialCommitKey p nk &&
  Commit.validOpening p op &&
  Commit.verify_opening ck op c (Commit.cp_q p) &&
  nullifier p nk op == nf

nullifierRelationWellformed ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  Bool
nullifierRelationWellformed p ck nk c nf op =
  ConfidentialBalance.validScalarCommitParams p &&
  Commit.valid_commit_key p ck &&
  Commit.valid_commit_key p nk &&
  Commit.validOpening p op &&
  Commit.verify_opening ck op c (Commit.cp_q p) &&
  nullifier p nk op == nf

canonicalNullifierChallenge ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  Int
canonicalNullifierChallenge _p ck nk c nf aCommit aNullifier =
  RepeatedFS.binaryFsChallenge
    nullifierFsDomain
    (nullifierFsFields ck nk c nf [aCommit] [aNullifier])
    0

nullifierSigmaVerify ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  Int ->
  Commit.CommitOpening ->
  Bool
nullifierSigmaVerify p gamma ck nk c nf aCommit aNullifier challenge z =
  ConfidentialBalance.validScalarCommitParams p &&
  Commit.valid_commit_key p ck &&
  Commit.valid_commit_key p nk &&
  validCommitment p c &&
  validCommitment p nf &&
  validCommitment p aCommit &&
  validCommitment p aNullifier &&
  validNullifierChallenge p challenge &&
  validNullifierResponse p gamma challenge z &&
  Commit.commit ck z (Commit.cp_q p) ==
    Zq.vec_mod (Listvec.vec_add aCommit (Listvec.scalar_mult challenge c)) (Commit.cp_q p) &&
  nullifier p nk z ==
    Zq.vec_mod (Listvec.vec_add aNullifier (Listvec.scalar_mult challenge nf)) (Commit.cp_q p)

nullifierFsProve ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  Maybe NullifierProof
nullifierFsProve p gamma ck nk c nf op ys =
  let aCommits = map (\y -> Commit.commit ck y (Commit.cp_q p)) ys
      aNullifiers = map (nullifier p nk) ys
      challenges = nullifierFsChallenges p ck nk c nf aCommits aNullifiers
      zs = RepeatedFS.sigmaResponseRounds nullifierSigmaRespond op ys challenges
   in if nullifierRelationWellformed p ck nk c nf op &&
         length ys == nullifierFsRounds &&
         all (validNullifierMask p gamma) ys &&
         and (zipWith (validNullifierResponse p gamma) challenges zs)
        then Just
          (NullifierProof
            aCommits
            aNullifiers
            (map Commit.open_msg zs)
            (map Commit.open_rand zs))
        else Nothing

nullifierFsVerify ::
  Commit.CommitParams ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  NullifierProof ->
  Bool
nullifierFsVerify p gamma ck nk c nf proof =
  let aCommits = nullifier_a_commits proof
      aNullifiers = nullifier_a_nullifiers proof
      zMsgs = nullifier_z_msgs proof
      zRands = nullifier_z_rands proof
      challenges = nullifierFsChallenges p ck nk c nf aCommits aNullifiers
      zs = nullifierZOpenings proof
   in length aCommits == nullifierFsRounds &&
      length aNullifiers == nullifierFsRounds &&
      length zMsgs == nullifierFsRounds &&
      length zRands == nullifierFsRounds &&
      and
        [ nullifierSigmaVerify p gamma ck nk c nf
            (aCommits !! i)
            (aNullifiers !! i)
            (challenges !! i)
            (zs !! i)
        | i <- [0 .. nullifierFsRounds - 1]
        ]

membershipIndexOf :: [[Int]] -> [Int] -> Maybe Int
membershipIndexOf [] _ = Nothing
membershipIndexOf (x : xs) c
  | x == c = Just 0
  | otherwise = fmap (+ 1) (membershipIndexOf xs c)

emptyCommitment :: Commit.CommitParams -> [Int]
emptyCommitment p = replicate (Commit.cp_m p) 0

ledgerHash :: Commit.CommitParams -> [Int] -> [Int] -> [Int]
ledgerHash p left right =
  Zq.vec_mod
    (Listvec.vec_add left (Listvec.scalar_mult 2 right))
    (Commit.cp_q p)

compressPairs :: Commit.CommitParams -> [[Int]] -> [[Int]]
compressPairs _ [] = []
compressPairs p [x] = [ledgerHash p x (emptyCommitment p)]
compressPairs p (x : y : xs) = ledgerHash p x y : compressPairs p xs

ledgerRoot :: Commit.CommitParams -> [[Int]] -> [Int]
ledgerRoot p [] = emptyCommitment p
ledgerRoot _ [x] = x
ledgerRoot p xs = ledgerRoot p (compressPairs p xs)

indexDirections :: Int -> Int -> [Bool]
indexDirections depth idx
  | depth <= 0 = []
  | otherwise = odd idx : indexDirections (depth - 1) (idx `div` 2)

authPathRoot :: Commit.CommitParams -> [Int] -> [[Int]] -> [Bool] -> [Int]
authPathRoot _ node [] [] = node
authPathRoot p node (s : ss) (False : ds) =
  authPathRoot p (ledgerHash p node s) ss ds
authPathRoot p node (s : ss) (True : ds) =
  authPathRoot p (ledgerHash p s node) ss ds
authPathRoot p _ _ _ = emptyCommitment p

membershipSiblings :: Commit.CommitParams -> [[Int]] -> Int -> Maybe [[Int]]
membershipSiblings _ [] _ = Nothing
membershipSiblings _ [_] idx
  | idx == 0 = Just []
  | otherwise = Nothing
membershipSiblings p ledger@(x : y : xs) idx
  | idx < 0 || idx >= length ledger = Nothing
  | otherwise =
      let sibling =
            if odd idx
              then ledger !! (idx - 1)
              else if idx + 1 < length ledger
                then ledger !! (idx + 1)
                else emptyCommitment p
       in fmap (sibling :) (membershipSiblings p (compressPairs p (x : y : xs)) (idx `div` 2))

membershipProve :: Commit.CommitParams -> [[Int]] -> [Int] -> Maybe MembershipProof
membershipProve p ledger c = do
  idx <- membershipIndexOf ledger c
  siblings <- membershipSiblings p ledger idx
  pure $
    MembershipProof
      idx
      (ledgerRoot p ledger)
      siblings
      (indexDirections (length siblings) idx)

membershipVerify :: Commit.CommitParams -> [Int] -> MembershipProof -> Bool
membershipVerify p c proof =
  let siblings = member_siblings proof
      directions = member_directions proof
   in length siblings == length directions &&
      directions == indexDirections (length siblings) (member_index proof) &&
      authPathRoot p c siblings directions == member_root proof

commitmentLedger :: [VerifiedNote] -> [[Int]]
commitmentLedger = map note_commitment

distinctList :: Eq a => [a] -> Bool
distinctList xs = length xs == length (nub xs)

ledgerValid ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [Int] ->
  [VerifiedNote] ->
  [[Int]] ->
  Bool
ledgerValid p gamma k ck root notes spent =
  ConfidentialBalance.validScalarCommitParams p &&
  Commit.valid_commit_key p ck &&
  root == ledgerRoot p (commitmentLedger notes) &&
  distinctList spent &&
  all
    (\note -> ConfidentialRange.rangeFsVerify p gamma k ck (note_commitment note) (note_range_proof note))
    notes

ledgerStepValid ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [VerifiedNote] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  TransactionProof ->
  Bool
ledgerStepValid p gamma k ck nk notes spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
  let preRoot = ledgerRoot p (commitmentLedger notes)
      updatedNotes = ledgerApplyNotes notes proof cOut1 cOut2
      updatedSpent = ledgerApplySpent spent nf1 nf2
      postRoot = ledgerRoot p (commitmentLedger updatedNotes)
   in ledgerValid p gamma k ck preRoot notes spent &&
      transactionFsVerify p gamma k ck nk preRoot spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof &&
      ledgerValid p gamma k ck postRoot updatedNotes updatedSpent

semanticStepValid ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [VerifiedNote] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  TransactionProof ->
  Bool
semanticStepValid = ledgerStepValid

transactionRelation ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  Bool
transactionRelation p ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 opIn1 opIn2 opOut1 opOut2 out1Bits out1Comps out2Bits out2Comps =
  nullifierRelation p ck nk cIn1 nf1 opIn1 &&
  nullifierRelation p ck nk cIn2 nf2 opIn2 &&
  cIn1 `elem` ledger &&
  cIn2 `elem` ledger &&
  nf1 `notElem` spent &&
  nf2 `notElem` spent &&
  nf1 /= nf2 &&
  ConfidentialRange.rangeRelation p ck cOut1 opOut1 out1Bits out1Comps &&
  ConfidentialRange.rangeRelation p ck cOut2 opOut2 out2Bits out2Comps &&
  ConfidentialBalance.amountOfOpening opIn1 + ConfidentialBalance.amountOfOpening opIn2 ==
    ConfidentialBalance.amountOfOpening opOut1 + ConfidentialBalance.amountOfOpening opOut2

transactionRelationWellformed ::
  Commit.CommitParams ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  Bool
transactionRelationWellformed p ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 opIn1 opIn2 opOut1 opOut2 out1Bits out1Comps out2Bits out2Comps =
  nullifierRelationWellformed p ck nk cIn1 nf1 opIn1 &&
  nullifierRelationWellformed p ck nk cIn2 nf2 opIn2 &&
  cIn1 `elem` ledger &&
  cIn2 `elem` ledger &&
  nf1 `notElem` spent &&
  nf2 `notElem` spent &&
  nf1 /= nf2 &&
  ConfidentialRange.rangeRelation p ck cOut1 opOut1 out1Bits out1Comps &&
  ConfidentialRange.rangeRelation p ck cOut2 opOut2 out2Bits out2Comps &&
  ConfidentialBalance.amountOfOpening opIn1 + ConfidentialBalance.amountOfOpening opIn2 ==
    ConfidentialBalance.amountOfOpening opOut1 + ConfidentialBalance.amountOfOpening opOut2

transactionFsVerify ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  TransactionProof ->
  Bool
transactionFsVerify p gamma k ck nk root spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 proof =
  Commit.valid_commit_key p ck &&
  Commit.valid_commit_key p nk &&
  membershipVerify p cIn1 (tx_in1_member proof) &&
  membershipVerify p cIn2 (tx_in2_member proof) &&
  member_root (tx_in1_member proof) == root &&
  member_root (tx_in2_member proof) == root &&
  member_index (tx_in1_member proof) /= member_index (tx_in2_member proof) &&
  nf1 `notElem` spent &&
  nf2 `notElem` spent &&
  nf1 /= nf2 &&
  nullifierFsVerify p gamma ck nk cIn1 nf1 (tx_in1_nullifier proof) &&
  nullifierFsVerify p gamma ck nk cIn2 nf2 (tx_in2_nullifier proof) &&
  ConfidentialBalance.balanceFsVerify p gamma ck
    (ConfidentialBalance.balanceCommitment cIn1 cIn2 cOut1 cOut2 (Commit.cp_q p))
    (tx_balance proof) &&
  ConfidentialRange.rangeFsVerify p gamma k ck cOut1 (tx_out1_range proof) &&
  ConfidentialRange.rangeFsVerify p gamma k ck cOut2 (tx_out2_range proof)

transactionFsProve ::
  Commit.CommitParams ->
  Int ->
  Int ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [[Int]] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  [Int] ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  Commit.CommitOpening ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [Commit.CommitOpening] ->
  [[Int]] ->
  [[Int]] ->
  [[[Int]]] ->
  [[Int]] ->
  [[[Int]]] ->
  Maybe TransactionProof
transactionFsProve p gamma k ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2 opIn1 opIn2 opOut1 opOut2 out1Bits out1Comps out2Bits out2Comps yIn1 yIn2 yBalance yOut1 yOut1Pairs yOut2 yOut2Pairs =
  case ( membershipProve p ledger cIn1
       , membershipProve p ledger cIn2
       , nullifierFsProve p gamma ck nk cIn1 nf1 opIn1 yIn1
       , nullifierFsProve p gamma ck nk cIn2 nf2 opIn2 yIn2
       , ConfidentialBalance.balanceFsProve p gamma ck
           (ConfidentialBalance.balanceCommitment cIn1 cIn2 cOut1 cOut2 (Commit.cp_q p))
           (ConfidentialBalance.aggregateRandomness opIn1 opIn2 opOut1 opOut2)
           yBalance
       , ConfidentialRange.rangeFsProve p gamma k ck cOut1 opOut1 out1Bits out1Comps yOut1 yOut1Pairs
       , ConfidentialRange.rangeFsProve p gamma k ck cOut2 opOut2 out2Bits out2Comps yOut2 yOut2Pairs
       ) of
    (Just member1, Just member2, Just nfProof1, Just nfProof2, Just balProof, Just range1, Just range2) ->
      if transactionRelationWellformed p ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2
           opIn1 opIn2 opOut1 opOut2 out1Bits out1Comps out2Bits out2Comps &&
         member_index member1 /= member_index member2
        then Just (TransactionProof member1 member2 nfProof1 nfProof2 balProof range1 range2)
        else Nothing
    _ -> Nothing

ledgerNoteAt :: [VerifiedNote] -> MembershipProof -> VerifiedNote
ledgerNoteAt notes proof = notes !! member_index proof

ledgerApplyNotes ::
  [VerifiedNote] ->
  TransactionProof ->
  [Int] ->
  [Int] ->
  [VerifiedNote]
ledgerApplyNotes notes proof cOut1 cOut2 =
  let note1 = ledgerNoteAt notes (tx_in1_member proof)
      note2 = ledgerNoteAt notes (tx_in2_member proof)
      remaining = delete note2 (delete note1 notes)
      out1 = VerifiedNote cOut1 (tx_out1_range proof)
      out2 = VerifiedNote cOut2 (tx_out2_range proof)
   in out1 : out2 : remaining

ledgerApplySpent :: [[Int]] -> [Int] -> [Int] -> [[Int]]
ledgerApplySpent spent nf1 nf2 = nf1 : nf2 : spent
