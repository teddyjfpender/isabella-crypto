import {
  listBalanceProof,
  listNullifierProof,
  listRangeProof,
  type MerkleTransactionProof,
} from './isabella-cli.ts';

export interface MerkleTransactionProofMutation {
  name: string;
  proof: MerkleTransactionProof;
  spent: number[][];
  root: string;
}

export function flipHexDigest(digest: string): string {
  return `${digest[0] === '0' ? '1' : '0'}${digest.slice(1)}`;
}

function mutateMatrixField<T extends Record<string, unknown>>(
  target: T,
  field: keyof T,
  rowIndex = 0
): T {
  const matrix = target[field] as number[][];
  return {
    ...target,
    [field]: matrix.map((row, index) =>
      index === rowIndex ? [row[0] + 1, ...row.slice(1)] : row
    ),
  };
}

export function merkleTransactionProofMutations(
  proof: MerkleTransactionProof,
  spent: number[][],
  root: string,
  spentNullifier: number[]
): MerkleTransactionProofMutation[] {
  const mutateRangeProof = (target: typeof proof.out1Range) => {
    const listed = listRangeProof(target);
    const mutated = mutateMatrixField(listed, 'amountsZ');
    return {
      bits: listed.bits,
      comps: listed.comps,
      amountAs: listed.amountsA,
      amountZs: mutated.amountsZ,
      pairAss: listed.pairAss,
      pairZss: listed.pairZss,
    };
  };
  const mutateNullifierProof = (target: typeof proof.in1Nullifier) =>
    mutateMatrixField(listNullifierProof(target), 'zMsgs');
  const mutateBalanceProof = (target: typeof proof.balance) =>
    mutateMatrixField(listBalanceProof(target), 'zs');

  return [
    {
      name: 'input member root',
      proof: { ...proof, in1Member: { ...proof.in1Member, root: flipHexDigest(proof.in1Member.root) } },
      spent,
      root,
    },
    {
      name: 'input member sibling',
      proof: {
        ...proof,
        in1Member: {
          ...proof.in1Member,
          siblings: [flipHexDigest(proof.in1Member.siblings[0]), ...proof.in1Member.siblings.slice(1)],
        },
      },
      spent,
      root,
    },
    {
      name: 'input member direction',
      proof: {
        ...proof,
        in1Member: {
          ...proof.in1Member,
          directions: [!proof.in1Member.directions[0], ...proof.in1Member.directions.slice(1)],
        },
      },
      spent,
      root,
    },
    {
      name: 'duplicate input member',
      proof: { ...proof, in2Member: proof.in1Member },
      spent,
      root,
    },
    {
      name: 'spent nullifier',
      proof,
      spent: [spentNullifier],
      root,
    },
    {
      name: 'nullifier response',
      proof: { ...proof, in1Nullifier: mutateNullifierProof(proof.in1Nullifier) },
      spent,
      root,
    },
    {
      name: 'balance response',
      proof: { ...proof, balance: mutateBalanceProof(proof.balance) },
      spent,
      root,
    },
    {
      name: 'range response',
      proof: { ...proof, out1Range: mutateRangeProof(proof.out1Range) },
      spent,
      root,
    },
    {
      name: 'swapped nullifier proofs',
      proof: {
        ...proof,
        in1Nullifier: proof.in2Nullifier,
        in2Nullifier: proof.in1Nullifier,
      },
      spent,
      root,
    },
    {
      name: 'swapped output ranges',
      proof: {
        ...proof,
        out1Range: proof.out2Range,
        out2Range: proof.out1Range,
      },
      spent,
      root,
    },
    {
      name: 'verifier root mismatch',
      proof,
      spent,
      root: flipHexDigest(root),
    },
  ];
}
