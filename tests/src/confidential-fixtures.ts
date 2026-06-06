import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

export async function buildMerkleTransactionFixture(options: { publicFee?: number } = {}) {
  const sdk = await import(pathToFileURL(typeScriptEntry).href);
  const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const nk = [
    [0, 1, 0],
    [1, 0, 0],
  ];
  const gamma = 5;
  const k = 1;
  const publicFee = options.publicFee ?? 0;
  const out2Amount = 1 - publicFee;
  if (!Number.isSafeInteger(publicFee) || publicFee < 0 || out2Amount < 0 || out2Amount > 1) {
    throw new Error('fixture supports publicFee 0 or 1');
  }
  const rounds = sdk.ConfidentialBalance.fsRounds();
  const opIn1 = { msg: [1], rand: [1, 0] };
  const opIn2 = { msg: [1], rand: [0, 1] };
  const opOut1 = { msg: [1], rand: [1, 1] };
  const opOut2 = { msg: [out2Amount], rand: [0, 0] };
  const bit1 = [{ msg: [1], rand: [1, 1] }];
  const comp1 = [{ msg: [0], rand: [0, 0] }];
  const bit2 = [{ msg: [out2Amount], rand: [0, 0] }];
  const comp2 = [{ msg: [publicFee], rand: [0, 0] }];
  const yIn1 = Array.from({ length: rounds }, () => ({ msg: [0], rand: [1, 0] }));
  const yIn2 = Array.from({ length: rounds }, () => ({ msg: [1], rand: [0, 1] }));
  const yBalance = Array.from({ length: rounds }, () => [0, 1]);
  const yOut1 = Array.from({ length: rounds }, () => [0, 1]);
  const yOut1Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
  const yOut2 = Array.from({ length: rounds }, () => [1, 0]);
  const yOut2Pairs = Array.from({ length: rounds }, () => [[0, 0]]);
  const commitOf = (opening: { msg: number[]; rand: number[] }) =>
    sdk.Zq.matVecMultMod(ck, sdk.Vec.concat(opening.msg, opening.rand), params.q);
  const cIn1 = commitOf(opIn1);
  const cIn2 = commitOf(opIn2);
  const cOut1 = commitOf(opOut1);
  const cOut2 = commitOf(opOut2);
  const nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn1);
  const nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, opIn2);
  const ledger = [cIn1, cIn2];
  const spent: number[][] = [];
  const proof =
    publicFee === 0
      ? sdk.ConfidentialTransaction.fsProveMerkle(
          params,
          gamma,
          k,
          ck,
          nk,
          ledger,
          spent,
          cIn1,
          cIn2,
          cOut1,
          cOut2,
          nf1,
          nf2,
          opIn1,
          opIn2,
          opOut1,
          opOut2,
          bit1,
          comp1,
          bit2,
          comp2,
          yIn1,
          yIn2,
          yBalance,
          yOut1,
          yOut1Pairs,
          yOut2,
          yOut2Pairs
        )
      : sdk.ConfidentialTransaction.fsProveMerkleWithFee(
          params,
          gamma,
          k,
          ck,
          nk,
          ledger,
          spent,
          publicFee,
          cIn1,
          cIn2,
          cOut1,
          cOut2,
          nf1,
          nf2,
          opIn1,
          opIn2,
          opOut1,
          opOut2,
          bit1,
          comp1,
          bit2,
          comp2,
          yIn1,
          yIn2,
          yBalance,
          yOut1,
          yOut1Pairs,
          yOut2,
          yOut2Pairs
        );
  if (proof === null) {
    throw new Error('failed to build Merkle transaction fixture');
  }
  const root = sdk.ConfidentialTransaction.merkleLedgerRoot(ledger);
  return {
    sdk,
    params,
    gamma,
    k,
    ck,
    nk,
    ledger,
    root,
    spent,
    cIn1,
    cIn2,
    cOut1,
    cOut2,
    nf1,
    nf2,
    publicFee,
    proof,
  };
}
