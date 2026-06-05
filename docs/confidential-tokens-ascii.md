# Confidential Tokens ASCII Diagram

```text
                         CONFIDENTIAL TOKEN FLOW

                    public ledger state on chain / contract
    ┌─────────────────────────────────────────────────────────────────────┐
    │ root = authenticated root of all live note commitments             │
    │ spent = set/list of already used nullifiers                        │
    └─────────────────────────────────────────────────────────────────────┘


1. A TOKEN IS A NOTE
──────────────────────────────────────────────────────────────────────────────

          secret opening                           public note
    ┌───────────────────────┐                ┌───────────────────────┐
    │ amount                │                │ commitment c          │
    │ blinding randomness r │ -- Commit -->  │ = Commit(ck, amount,r)│
    │ owner witness data    │                │ + range proof         │
    └───────────────────────┘                └───────────────────────┘

The ledger stores the public note commitment, not the clear amount.


2. A USER SPENDS TWO INPUT NOTES INTO TWO OUTPUT NOTES
──────────────────────────────────────────────────────────────────────────────

      inputs owned by spender                      outputs created
    ┌───────────────────────────┐               ┌───────────────────────────┐
    │ note 1: c_in1             │               │ note 1: c_out1            │
    │ hidden amount a1          │               │ hidden amount b1          │
    │ hidden randomness r1      │               │ hidden randomness s1      │
    └───────────────────────────┘               └───────────────────────────┘
    ┌───────────────────────────┐               ┌───────────────────────────┐
    │ note 2: c_in2             │               │ note 2: c_out2            │
    │ hidden amount a2          │               │ hidden amount b2          │
    │ hidden randomness r2      │               │ hidden randomness s2      │
    └───────────────────────────┘               └───────────────────────────┘

                 hidden law that must hold:
                      a1 + a2 = b1 + b2


3. TO PREVENT DOUBLE SPENDING, EACH INPUT GETS A NULLIFIER
──────────────────────────────────────────────────────────────────────────────

    input opening (amount, rand)  -- Nullifier key -->   nf

    ┌───────────────────────────┐                        ┌───────────────────┐
    │ same secret opening used  │ -- Commit(nk, op) --> │ nullifier nf      │
    │ for the input note        │                        │ deterministic      │
    └───────────────────────────┘                        └───────────────────┘

A spender reveals nf, not the input opening.
If nf is already in `spent`, the transaction is rejected.


4. THE PROOF BUNDLE THE USER SUBMITS
──────────────────────────────────────────────────────────────────────────────

    transaction proof
    ┌───────────────────────────────────────────────────────────────────────┐
    │ in1 membership proof   : "c_in1 is in the current ledger root"       │
    │ in2 membership proof   : "c_in2 is in the current ledger root"       │
    │ in1 nullifier proof    : "nf1 comes from the same secret as c_in1"   │
    │ in2 nullifier proof    : "nf2 comes from the same secret as c_in2"   │
    │ balance proof          : "inputs and outputs conserve value"          │
    │ out1 range proof       : "b1 is in allowed range"                    │
    │ out2 range proof       : "b2 is in allowed range"                    │
    └───────────────────────────────────────────────────────────────────────┘


5. WHAT THE BALANCE PROOF REALLY SAYS
──────────────────────────────────────────────────────────────────────────────

    public derived commitment:

      c_bal = c_in1 + c_in2 - c_out1 - c_out2    mod q

If the hidden amounts balance, then the message parts cancel and only
randomness remains.

So the prover shows:

      c_bal = rand_commit(ck, r_bal)

meaning:
      "this combined commitment opens to message 0"

That proves:
      input value = output value
without revealing any amount.


6. WHAT THE RANGE PROOFS SAY
──────────────────────────────────────────────────────────────────────────────

For each output amount b:

      b = bit0 + 2*bit1 + 4*bit2 + ...

and each bit is proved to be 0 or 1.

So the verifier learns:
      0 <= b < 2^k
but not the actual value of b.

This prevents cheating with negative values or oversized hidden outputs.


7. WHAT THE MEMBERSHIP PROOFS SAY
──────────────────────────────────────────────────────────────────────────────

    current notes in ledger
      c0   c1   c2   c3   ...

          │    │
          └────┴── hashed into authenticated root ──> root

A spender proves:
      "my input commitment c_in1 is one of the leaves under root"
      "my input commitment c_in2 is one of the leaves under root"

without needing to reveal anything except the path data.


8. WHAT THE CONTRACT / VERIFIER CHECKS
──────────────────────────────────────────────────────────────────────────────

    given:
      root, spent,
      c_in1, c_in2, c_out1, c_out2,
      nf1, nf2,
      proof bundle

    verify:
      1. c_in1 membership proof valid under root
      2. c_in2 membership proof valid under root
      3. input positions are distinct
      4. nf1 not already spent
      5. nf2 not already spent
      6. nf1 != nf2
      7. nullifier proof for input 1 valid
      8. nullifier proof for input 2 valid
      9. balance proof valid
     10. output 1 range proof valid
     11. output 2 range proof valid

If all pass, the transfer is accepted.


9. STATE UPDATE AFTER ACCEPTANCE
──────────────────────────────────────────────────────────────────────────────

    old state:
      live notes = {..., c_in1, c_in2, ...}
      spent      = {...}

    remove consumed inputs
    add new outputs
    add nullifiers

    new state:
      live notes = {..., c_out1, c_out2, ...}
      spent      = {..., nf1, nf2}
      new root   = root(live notes)

So the value moves privately from old notes to new notes.


10. THE KEY IDEA IN ONE LINE
──────────────────────────────────────────────────────────────────────────────

    reveal enough to prove:
      "these inputs exist, are unspent, and fund these outputs"

    while hiding:
      "which amounts were transferred"
```
