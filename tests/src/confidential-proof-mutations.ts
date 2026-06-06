import {
  listBalanceProof,
  listNullifierProof,
  listRangeProof,
  type MerkleMembershipProof,
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

function mutateMembershipSibling(proof: MerkleMembershipProof): MerkleMembershipProof {
  return {
    ...proof,
    siblings: [flipHexDigest(proof.siblings[0]), ...proof.siblings.slice(1)],
  };
}

function mutateMembershipDirection(proof: MerkleMembershipProof): MerkleMembershipProof {
  return {
    ...proof,
    directions: [!proof.directions[0], ...proof.directions.slice(1)],
  };
}

function mutateMembershipIndex(proof: MerkleMembershipProof): MerkleMembershipProof {
  return {
    ...proof,
    index: proof.index + 1,
  };
}

function extendMembershipPath(proof: MerkleMembershipProof): MerkleMembershipProof {
  return {
    ...proof,
    siblings: [...proof.siblings, proof.root],
    directions: [...proof.directions, false],
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
      proof: { ...proof, in1Member: mutateMembershipSibling(proof.in1Member) },
      spent,
      root,
    },
    {
      name: 'input member direction',
      proof: { ...proof, in1Member: mutateMembershipDirection(proof.in1Member) },
      spent,
      root,
    },
    {
      name: 'input member index',
      proof: { ...proof, in1Member: mutateMembershipIndex(proof.in1Member) },
      spent,
      root,
    },
    {
      name: 'input member extended path',
      proof: { ...proof, in1Member: extendMembershipPath(proof.in1Member) },
      spent,
      root,
    },
    {
      name: 'second input member root',
      proof: { ...proof, in2Member: { ...proof.in2Member, root: flipHexDigest(proof.in2Member.root) } },
      spent,
      root,
    },
    {
      name: 'second input member sibling',
      proof: { ...proof, in2Member: mutateMembershipSibling(proof.in2Member) },
      spent,
      root,
    },
    {
      name: 'second input member direction',
      proof: { ...proof, in2Member: mutateMembershipDirection(proof.in2Member) },
      spent,
      root,
    },
    {
      name: 'second input member index',
      proof: { ...proof, in2Member: mutateMembershipIndex(proof.in2Member) },
      spent,
      root,
    },
    {
      name: 'second input member extended path',
      proof: { ...proof, in2Member: extendMembershipPath(proof.in2Member) },
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
      name: 'second nullifier response',
      proof: { ...proof, in2Nullifier: mutateNullifierProof(proof.in2Nullifier) },
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
      name: 'second range response',
      proof: { ...proof, out2Range: mutateRangeProof(proof.out2Range) },
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
