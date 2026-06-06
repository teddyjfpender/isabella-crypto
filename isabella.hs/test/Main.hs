-- | Basic tests for the Isabella library
module Main where

import qualified Canon.Commit_sis as Commit
import qualified Canon.Confidential_balance as ConfidentialBalance
import qualified Canon.Confidential_range as ConfidentialRange
import qualified Canon.Confidential_transaction as ConfidentialTransaction
import qualified Canon.Dilithium as Dilithium
import qualified Canon.Listvec as Listvec
import qualified Canon.Regev_pke as Regev
import qualified Canon.Zq as Zq
import System.Exit (exitSuccess, exitFailure)

confidentialCk :: [[Int]]
confidentialCk =
    [ [1, 0, 0]
    , [0, 1, 0]
    ]

nullifierNk :: [[Int]]
nullifierNk =
    [ [0, 1, 0]
    , [1, 0, 0]
    ]

data ConfidentialTransactionFixture = ConfidentialTransactionFixture
    { fixtureParams :: Commit.CommitParams
    , fixtureCk :: [[Int]]
    , fixtureNk :: [[Int]]
    , fixtureGamma :: Int
    , fixtureRangeK :: Int
    , fixtureSpent :: [[Int]]
    , fixtureCIn1 :: [Int]
    , fixtureCIn2 :: [Int]
    , fixtureCOut1 :: [Int]
    , fixtureCOut2 :: [Int]
    , fixtureNf1 :: [Int]
    , fixtureNf2 :: [Int]
    , fixtureProof :: ConfidentialTransaction.TransactionProof
    , fixtureMerkleProof :: ConfidentialTransaction.MerkleTransactionProof
    , fixtureNotes :: [ConfidentialTransaction.VerifiedNote]
    }

confidentialTransactionFixture :: Maybe ConfidentialTransactionFixture
confidentialTransactionFixture =
    let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
        ck = confidentialCk
        nk = nullifierNk
        gamma = 5
        rangeK = 1
        opIn1 = Commit.makeOpening [1] [1,0]
        opIn2 = Commit.makeOpening [1] [0,1]
        opOut1 = Commit.makeOpening [1] [1,1]
        opOut2 = Commit.makeOpening [1] [0,0]
        in1Bits =
          [ Commit.makeOpening [1] [1,0]
          ]
        in1Comps =
          [ Commit.makeOpening [0] [0,0]
          ]
        in2Bits =
          [ Commit.makeOpening [1] [0,1]
          ]
        in2Comps =
          [ Commit.makeOpening [0] [0,0]
          ]
        out1Bits =
          [ Commit.makeOpening [1] [1,1]
          ]
        out1Comps =
          [ Commit.makeOpening [0] [0,0]
          ]
        out2Bits =
          [ Commit.makeOpening [1] [0,0]
          ]
        out2Comps =
          [ Commit.makeOpening [0] [0,0]
          ]
        yIn1 = replicate ConfidentialBalance.balanceFsRounds (Commit.makeOpening [0] [1,0])
        yIn2 = replicate ConfidentialBalance.balanceFsRounds (Commit.makeOpening [1] [0,1])
        yBalance = replicate ConfidentialBalance.balanceFsRounds [0,1]
        yOut1 = replicate ConfidentialRange.rangeFsRounds [0,1]
        yOut1Pairs = replicate ConfidentialRange.rangeFsRounds [[0,0]]
        yOut2 = replicate ConfidentialRange.rangeFsRounds [1,0]
        yOut2Pairs = replicate ConfidentialRange.rangeFsRounds [[0,0]]
        cIn1 = Commit.commit ck opIn1 17
        cIn2 = Commit.commit ck opIn2 17
        cOut1 = Commit.commit ck opOut1 17
        cOut2 = Commit.commit ck opOut2 17
        nf1 = ConfidentialTransaction.nullifier params nk opIn1
        nf2 = ConfidentialTransaction.nullifier params nk opIn2
        ledger = [cIn1, cIn2]
        spent = []
     in do
        in1Range <- ConfidentialRange.rangeFsProve params gamma rangeK ck cIn1 opIn1 in1Bits in1Comps yOut1 yOut1Pairs
        in2Range <- ConfidentialRange.rangeFsProve params gamma rangeK ck cIn2 opIn2 in2Bits in2Comps yOut2 yOut2Pairs
        proof <- ConfidentialTransaction.transactionFsProve
            params gamma rangeK ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2
            opIn1 opIn2 opOut1 opOut2
            out1Bits out1Comps out2Bits out2Comps
            yIn1 yIn2 yBalance yOut1 yOut1Pairs yOut2 yOut2Pairs
        merkleProof <- ConfidentialTransaction.transactionFsProveMerkle
            params gamma rangeK ck nk ledger spent cIn1 cIn2 cOut1 cOut2 nf1 nf2
            opIn1 opIn2 opOut1 opOut2
            out1Bits out1Comps out2Bits out2Comps
            yIn1 yIn2 yBalance yOut1 yOut1Pairs yOut2 yOut2Pairs
        pure ConfidentialTransactionFixture
            { fixtureParams = params
            , fixtureCk = ck
            , fixtureNk = nk
            , fixtureGamma = gamma
            , fixtureRangeK = rangeK
            , fixtureSpent = spent
            , fixtureCIn1 = cIn1
            , fixtureCIn2 = cIn2
            , fixtureCOut1 = cOut1
            , fixtureCOut2 = cOut2
            , fixtureNf1 = nf1
            , fixtureNf2 = nf2
            , fixtureProof = proof
            , fixtureMerkleProof = merkleProof
            , fixtureNotes =
                [ ConfidentialTransaction.makeVerifiedNote cIn1 in1Range
                , ConfidentialTransaction.makeVerifiedNote cIn2 in2Range
                ]
            }

main :: IO ()
main = do
    putStrLn "Running Isabella tests..."
    results <- sequence tests
    if and results
        then do
            putStrLn $ "\nAll " ++ show (length results) ++ " tests passed!"
            exitSuccess
        else do
            putStrLn "\nSome tests failed!"
            exitFailure

tests :: [IO Bool]
tests =
    [ test "Zq.mod_centered identity at 0" $
        Zq.mod_centered 0 5 == 0

    , test "Zq.mod_centered small positive" $
        Zq.mod_centered 2 5 == 2

    , test "Zq.mod_centered wraps large values" $
        Zq.mod_centered 7 5 == 2

    , test "Zq.mod_centered negative result" $
        Zq.mod_centered 8 5 == -2

    , test "Zq and Dilithium centered reduction coexist under qualified aliases" $
        Zq.mod_centered 8 5 == -2 &&
        seq Dilithium.dil_ntt_q (seq Dilithium.mod_centered True)

    , test "Dilithium params wrapper exposes ML-DSA-44 values" $
        let params = Dilithium.mldsa44Params in
        Dilithium.dilQ params == 8380417 &&
        Dilithium.dilK params == 4 &&
        Dilithium.dilGamma2 params == 95232

    , test "Dilithium modCentered wrapper matches shared semantics" $
        Dilithium.modCentered 9 16 == -7 &&
        Dilithium.modCentered (-3) 16 == -3

    , test "Dilithium power2Round reconstructs" $
        let params = Dilithium.mldsa44Params
            (r1, r0) = Dilithium.power2Round 1234567 (Dilithium.dilD params)
        in r1 * (2 ^ Dilithium.dilD params) + r0 == 1234567

    , test "Dilithium decompose agrees with highBits/lowBits" $
        let alpha = 2 * Dilithium.dilGamma2 Dilithium.mldsa44Params
            (r1, r0) = Dilithium.decompose 543210 alpha
        in r1 == Dilithium.highBits 543210 alpha &&
           r0 == Dilithium.lowBits 543210 alpha

    , test "Dilithium decompose takes the q-1 boundary branch" $
        let params = Dilithium.mldsa44Params
            alpha = 2 * Dilithium.dilGamma2 params
            qMinusOne = Dilithium.dilQ params - 1
        in Dilithium.decompose qMinusOne alpha == (0, -1)

    , test "Dilithium makeHint/useHint recover adjusted high bits" $
        let alpha = 2 * Dilithium.dilGamma2 Dilithium.mldsa44Params
            hint = Dilithium.makeHint 2000 100000 alpha
        in Dilithium.useHint hint 100000 alpha == Dilithium.highBits 102000 alpha

    , test "Dilithium makeHint remains a bit" $
        let params = Dilithium.mldsa44Params
            alpha = 2 * Dilithium.dilGamma2 params
            qMinusOne = Dilithium.dilQ params - 1
            hint = Dilithium.makeHint 2000 qMinusOne alpha
        in hint == 0 || hint == 1

    , test "Dilithium checkBound is strict and hintWeight sums rows" $
        Dilithium.checkBound 77 (Dilithium.dilBeta Dilithium.mldsa44Params) &&
        not (Dilithium.checkBound 78 78) &&
        Dilithium.hintWeight [[1,0,1],[0,1,0],[1]] == 4

    , test "dist0 is non-negative" $
        Zq.dist0 256 (-50) >= 0

    , test "dist0 of 0 is 0" $
        Zq.dist0 256 0 == 0

    , test "dist0 bound" $
        Zq.dist0 256 200 <= 128

    , test "encode_bit False is 0" $
        Zq.encode_bit 256 False == 0

    , test "encode_bit True is q/2" $
        Zq.encode_bit 256 True == 128

    , test "decode_bit near 0" $
        Zq.decode_bit 256 10 == False

    , test "decode_bit near q/2" $
        Zq.decode_bit 256 130 == True

    , test "encode/decode round-trip False" $
        Zq.decode_bit 256 (Zq.encode_bit 256 False) == False

    , test "encode/decode round-trip True" $
        Zq.decode_bit 256 (Zq.encode_bit 256 True) == True

    , test "encode/decode with small noise False" $
        Zq.decode_bit 256 (Zq.encode_bit 256 False + 10) == False

    , test "encode/decode with small noise True" $
        Zq.decode_bit 256 (Zq.encode_bit 256 True + 10) == True

    , test "inner_prod simple" $
        Listvec.inner_prod [1,2,3] [4,5,6] == 32

    , test "inner_prod zeros" $
        Listvec.inner_prod [0,0,0] [1,2,3] == 0

    , test "vec_add" $
        Listvec.vec_add [1,2,3] [4,5,6] == [5,7,9]

    , test "vec_sub" $
        Listvec.vec_sub [5,7,9] [1,2,3] == [4,5,6]

    , test "scalar_mult" $
        Listvec.scalar_mult 3 [1,2,3] == [3,6,9]

    , test "vec_neg" $
        Listvec.vec_neg [1,-2,3] == [-1,2,-3]

    , test "vec_mod" $
        Zq.vec_mod [7,13,-2] 5 == [2,3,3]

    , test "mat_vec_mult" $
        Listvec.mat_vec_mult [[1,0],[0,1]] [3,4] == [3,4]

    , test "transpose" $
        Listvec.transpose [[1,2],[3,4]] == [[1,3],[2,4]]

    , test "transpose rectangular matrix" $
        Listvec.transpose [[1,2,3],[4,5,6]] == [[1,4],[2,5],[3,6]]

    , test "Regev decrypt recovers False under small noise" $
        let q = 256
            a = [[1,2],[3,4]]
            s = [1,-1]
            e = [1,0]
            r = [1,0]
            (pk, sk) = Regev.regev_keygen a s e q
            ct = Regev.regev_encrypt pk r False q
        in Regev.regev_decrypt sk ct q == False

    , test "Regev decrypt recovers True under small noise" $
        let q = 256
            a = [[1,2],[3,4]]
            s = [1,-1]
            e = [1,0]
            r = [1,0]
            (pk, sk) = Regev.regev_keygen a s e q
            ct = Regev.regev_encrypt pk r True q
        in Regev.regev_decrypt sk ct q == True

    , test "Regev payload matches encode-plus-noise" $
        let q = 256
            a = [[1,2],[3,4]]
            s = [1,-1]
            e = [1,0]
            r = [1,0]
            (pk, sk) = Regev.regev_keygen a s e q
            ct = Regev.regev_encrypt pk r True q
            noise = Listvec.inner_prod e r
        in Regev.decrypt_payload sk ct q == (noise + Zq.encode_bit q True) `mod` q

    , test "Confidential balance commitment matches aggregate randomness when amounts cancel" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 3
            ck = confidentialCk
            opIn1 = Commit.makeOpening [7] [1,2]
            opIn2 = Commit.makeOpening [4] [0,-1]
            opOut1 = Commit.makeOpening [5] [2,0]
            opOut2 = Commit.makeOpening [6] [-1,1]
            cIn1 = Commit.commit ck opIn1 17
            cIn2 = Commit.commit ck opIn2 17
            cOut1 = Commit.commit ck opOut1 17
            cOut2 = Commit.commit ck opOut2 17
            aggregate = ConfidentialBalance.aggregateRandomness opIn1 opIn2 opOut1 opOut2
        in ConfidentialBalance.amountOfOpening opIn1 == 7 &&
           aggregate == [0,0] &&
           ConfidentialBalance.balanceCommitment cIn1 cIn2 cOut1 cOut2 (Commit.cp_q params) ==
             ConfidentialBalance.randCommit params ck aggregate

    , test "Confidential balance Fiat-Shamir proof verifies deterministically" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 3
            ck = confidentialCk
            gamma = 5
            r = [1,2]
            ys = replicate ConfidentialBalance.balanceFsRounds [0,1]
            c = ConfidentialBalance.randCommit params ck r
        in case ConfidentialBalance.balanceFsProve params gamma ck c r ys of
            Just proof ->
                let challenges =
                      ConfidentialBalance.balanceFsChallenges params ck c
                        (ConfidentialBalance.balance_as proof)
                in
                ConfidentialBalance.validScalarCommitParams params &&
                ConfidentialBalance.validBalanceWitness params r &&
                all (ConfidentialBalance.validBalanceMask params gamma) ys &&
                length challenges == ConfidentialBalance.balanceFsRounds &&
                and
                  (zipWith
                    (ConfidentialBalance.validBalanceResponse params gamma)
                    challenges
                    (ConfidentialBalance.balance_zs proof)) &&
                ConfidentialBalance.balanceFsVerify params gamma ck c proof
            Nothing -> False

    , test "Confidential balance proof rejects tampering" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 3
            ck = confidentialCk
            gamma = 5
            r = [1,2]
            ys = replicate ConfidentialBalance.balanceFsRounds [0,1]
            c = ConfidentialBalance.randCommit params ck r
        in case ConfidentialBalance.balanceFsProve params gamma ck c r ys of
            Just proof ->
                case ConfidentialBalance.balance_zs proof of
                    (z1 : zRest) : zsRest ->
                        let badProof =
                              ConfidentialBalance.makeBalanceProof
                                (ConfidentialBalance.balance_as proof)
                                ((z1 + 1 : zRest) : zsRest)
                        in not (ConfidentialBalance.balanceFsVerify params gamma ck c badProof)
                    _ -> False
            Nothing -> False

    , test "Confidential range amount commitment matches residual randomness" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
            ck = confidentialCk
            amountOpening = Commit.makeOpening [5] [1,2]
            bitOpenings =
              [ Commit.makeOpening [1] [1,0]
              , Commit.makeOpening [0] [0,1]
              , Commit.makeOpening [1] [1,1]
              ]
            cAmount = Commit.commit ck amountOpening 17
            cBits = map (\op -> Commit.commit ck op 17) bitOpenings
            residual = ConfidentialRange.rangeAmountRandomness params amountOpening bitOpenings
        in ConfidentialRange.rangeAmountCommitment params ck cAmount cBits ==
             ConfidentialBalance.randCommit params ck residual

    , test "Confidential range Fiat-Shamir proof verifies deterministically" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
            ck = confidentialCk
            gamma = 5
            rangeK = 3
            amountOpening = Commit.makeOpening [5] [1,2]
            bitOpenings =
              [ Commit.makeOpening [1] [1,0]
              , Commit.makeOpening [0] [0,1]
              , Commit.makeOpening [1] [1,1]
              ]
            compOpenings =
              [ Commit.makeOpening [0] [0,1]
              , Commit.makeOpening [1] [1,0]
              , Commit.makeOpening [0] [0,-1]
              ]
            yAmount = replicate ConfidentialRange.rangeFsRounds [0,1]
            yPairs = replicate ConfidentialRange.rangeFsRounds [[1,0],[0,0],[1,-1]]
            cAmount = Commit.commit ck amountOpening 17
            amountResidual = ConfidentialRange.rangeAmountRandomness params amountOpening bitOpenings
            pairResiduals = ConfidentialRange.rangePairRandomnesses params bitOpenings compOpenings
        in case ConfidentialRange.rangeFsProve params gamma rangeK ck cAmount amountOpening bitOpenings compOpenings yAmount yPairs of
            Just proof ->
              let challenges = ConfidentialRange.rangeFsChallenges params ck cAmount
                    (ConfidentialRange.range_bits proof)
                    (ConfidentialRange.range_comps proof)
                    (ConfidentialRange.range_amount_as proof)
                    (ConfidentialRange.range_pair_ass proof)
              in
              ConfidentialRange.validRangeAmountWitness params rangeK amountResidual &&
              all (ConfidentialRange.validRangePairWitness params) pairResiduals &&
              and (zipWith (ConfidentialRange.validRangeAmountResponse params gamma rangeK)
                    challenges
                    (ConfidentialRange.range_amount_zs proof)) &&
              and (zipWith (\challenge zs ->
                    all (ConfidentialRange.validRangePairResponse params gamma challenge) zs)
                    challenges
                    (ConfidentialRange.range_pair_zss proof)) &&
              ConfidentialRange.rangeFsVerify params gamma rangeK ck cAmount proof
            Nothing -> False

    , test "Confidential range proof rejects mismatched amount decomposition" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
            ck = confidentialCk
            gamma = 5
            rangeK = 3
            badAmountOpening = Commit.makeOpening [6] [1,2]
            bitOpenings =
              [ Commit.makeOpening [1] [1,0]
              , Commit.makeOpening [0] [0,1]
              , Commit.makeOpening [1] [1,1]
              ]
            compOpenings =
              [ Commit.makeOpening [0] [0,1]
              , Commit.makeOpening [1] [1,0]
              , Commit.makeOpening [0] [0,-1]
              ]
            yAmount = replicate ConfidentialRange.rangeFsRounds [0,1]
            yPairs = replicate ConfidentialRange.rangeFsRounds [[1,0],[0,0],[1,-1]]
            cAmount = Commit.commit ck badAmountOpening 17
        in ConfidentialRange.rangeFsProve params gamma rangeK ck cAmount badAmountOpening bitOpenings compOpenings yAmount yPairs == Nothing

    , test "Confidential transaction nullifier proof verifies deterministically" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
            ck = confidentialCk
            nk = nullifierNk
            gamma = 5
            opIn1 = Commit.makeOpening [4] [1,0]
            yIn1 = replicate ConfidentialBalance.balanceFsRounds (Commit.makeOpening [0] [1,0])
            cIn1 = Commit.commit ck opIn1 17
            nf1 = ConfidentialTransaction.nullifier params nk opIn1
        in case ConfidentialTransaction.nullifierFsProve params gamma ck nk cIn1 nf1 opIn1 yIn1 of
            Just proof ->
              length (ConfidentialTransaction.nullifier_a_commits proof) == ConfidentialBalance.balanceFsRounds &&
              length (ConfidentialTransaction.nullifier_a_nullifiers proof) == ConfidentialBalance.balanceFsRounds &&
              length (ConfidentialTransaction.nullifier_z_msgs proof) == ConfidentialBalance.balanceFsRounds &&
              length (ConfidentialTransaction.nullifier_z_rands proof) == ConfidentialBalance.balanceFsRounds &&
              ConfidentialTransaction.nullifierFsVerify params gamma ck nk cIn1 nf1 proof
            Nothing -> False

    , test "Confidential transaction membership proof finds the second input" $
        let params = ConfidentialBalance.makeScalarCommitParams 2 2 17 6
            ledger = [[11,4],[6,2],[9,4]]
        in case ConfidentialTransaction.membershipProve params ledger [6,2] of
            Just proof -> ConfidentialTransaction.member_index proof == 1 &&
                          ConfidentialTransaction.membershipVerify params [6,2] proof
            Nothing -> False

    , test "Confidential transaction Fiat-Shamir proof verifies deterministically" $
        case confidentialTransactionFixture of
            Just fixture ->
              let root = ConfidentialTransaction.ledgerRoot (fixtureParams fixture)
                            [fixtureCIn1 fixture, fixtureCIn2 fixture]
              in ConfidentialTransaction.transactionFsVerify
                   (fixtureParams fixture)
                   (fixtureGamma fixture)
                   (fixtureRangeK fixture)
                   (fixtureCk fixture)
                   (fixtureNk fixture)
                   root
                   (fixtureSpent fixture)
                   (fixtureCIn1 fixture)
                   (fixtureCIn2 fixture)
                   (fixtureCOut1 fixture)
                   (fixtureCOut2 fixture)
                   (fixtureNf1 fixture)
                   (fixtureNf2 fixture)
                   (fixtureProof fixture)
            Nothing -> False

    , test "Confidential transaction ledger helpers install outputs and spent nullifiers" $
        case confidentialTransactionFixture of
            Just fixture ->
              let updatedNotes =
                    ConfidentialTransaction.ledgerApplyNotes
                      (fixtureNotes fixture)
                      (fixtureProof fixture)
                      (fixtureCOut1 fixture)
                      (fixtureCOut2 fixture)
                  updatedSpent =
                    ConfidentialTransaction.ledgerApplySpent
                      (fixtureSpent fixture)
                      (fixtureNf1 fixture)
                      (fixtureNf2 fixture)
                  root = ConfidentialTransaction.ledgerRoot
                           (fixtureParams fixture)
                           (ConfidentialTransaction.commitmentLedger updatedNotes)
              in ConfidentialTransaction.commitmentLedger updatedNotes ==
                   [fixtureCOut1 fixture, fixtureCOut2 fixture] &&
                 updatedSpent == [fixtureNf1 fixture, fixtureNf2 fixture] &&
                 ConfidentialTransaction.ledgerValid
                   (fixtureParams fixture)
                   (fixtureGamma fixture)
                   (fixtureRangeK fixture)
                   (fixtureCk fixture)
                   root
                   updatedNotes
                   updatedSpent
            Nothing -> False

    , test "Confidential transaction scaffold ledger-step validity holds for verified-note pre-state" $
        case confidentialTransactionFixture of
            Just fixture ->
              ConfidentialTransaction.ledgerStepValidScaffold
                (fixtureParams fixture)
                (fixtureGamma fixture)
                (fixtureRangeK fixture)
                (fixtureCk fixture)
                (fixtureNk fixture)
                (fixtureNotes fixture)
                (fixtureSpent fixture)
                (fixtureCIn1 fixture)
                (fixtureCIn2 fixture)
                (fixtureCOut1 fixture)
                (fixtureCOut2 fixture)
                (fixtureNf1 fixture)
                (fixtureNf2 fixture)
                (fixtureProof fixture)
            _ -> False

    , test "Confidential transaction ledger-step validity defaults to Merkle verifier" $
        case confidentialTransactionFixture of
            Just fixture ->
              ConfidentialTransaction.ledgerStepValid
                (fixtureParams fixture)
                (fixtureGamma fixture)
                (fixtureRangeK fixture)
                (fixtureCk fixture)
                (fixtureNk fixture)
                (fixtureNotes fixture)
                (fixtureSpent fixture)
                (fixtureCIn1 fixture)
                (fixtureCIn2 fixture)
                (fixtureCOut1 fixture)
                (fixtureCOut2 fixture)
                (fixtureNf1 fixture)
                (fixtureNf2 fixture)
                (fixtureMerkleProof fixture) &&
              ConfidentialTransaction.ledgerStepValid
                (fixtureParams fixture)
                (fixtureGamma fixture)
                (fixtureRangeK fixture)
                (fixtureCk fixture)
                (fixtureNk fixture)
                (fixtureNotes fixture)
                (fixtureSpent fixture)
                (fixtureCIn1 fixture)
                (fixtureCIn2 fixture)
                (fixtureCOut1 fixture)
                (fixtureCOut2 fixture)
                (fixtureNf1 fixture)
                (fixtureNf2 fixture)
                (fixtureMerkleProof fixture) ==
              ConfidentialTransaction.ledgerStepValidMerkle
                (fixtureParams fixture)
                (fixtureGamma fixture)
                (fixtureRangeK fixture)
                (fixtureCk fixture)
                (fixtureNk fixture)
                (fixtureNotes fixture)
                (fixtureSpent fixture)
                (fixtureCIn1 fixture)
                (fixtureCIn2 fixture)
                (fixtureCOut1 fixture)
                (fixtureCOut2 fixture)
                (fixtureNf1 fixture)
                (fixtureNf2 fixture)
                (fixtureMerkleProof fixture)
            _ -> False

    , test "valid_vec true" $
        Listvec.valid_vec 3 [1,2,3] == True

    , test "valid_vec false" $
        Listvec.valid_vec 3 [1,2] == False

    , test "split_vec" $
        Listvec.split_vec 2 [1,2,3,4,5] == ([1,2], [3,4,5])

    , test "vec_concat" $
        Listvec.vec_concat [1,2] [3,4,5] == [1,2,3,4,5]
    ]

test :: String -> Bool -> IO Bool
test name result = do
    if result
        then putStrLn $ "  ✓ " ++ name
        else putStrLn $ "  ✗ " ++ name
    return result
