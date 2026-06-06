import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..', '..');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts/dist/index.mjs');

function allBounded(values: number[], bound: number): boolean {
  return values.every(value => Number.isSafeInteger(value) && Math.abs(value) <= bound);
}

function allBigIntBounded(values: bigint[], bound: bigint): boolean {
  return values.every(value => value >= -bound && value <= bound);
}

describe('Confidential CSPRNG sampling helpers', () => {
  it('samples centered integers, vectors, and openings within explicit bounds', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const gamma = 5;

    for (let i = 0; i < 64; i += 1) {
      const sample = sdk.ConfidentialSampling.boundedInt(gamma);
      expect(Number.isSafeInteger(sample)).toBe(true);
      expect(Math.abs(sample)).toBeLessThanOrEqual(gamma);
    }

    const vector = sdk.ConfidentialSampling.intVector(32, gamma);
    expect(vector).toHaveLength(32);
    expect(allBounded(vector, gamma)).toBe(true);

    const opening = sdk.ConfidentialSampling.opening(1, 3, gamma);
    expect(opening.msg).toHaveLength(1);
    expect(opening.rand).toHaveLength(3);
    expect(allBounded(opening.msg, gamma)).toBe(true);
    expect(allBounded(opening.rand, gamma)).toBe(true);
  });

  it('samples centered BigInts, vectors, and openings within explicit bounds', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const gamma = 4835703278458516765933661n;

    for (let i = 0; i < 32; i += 1) {
      const sample = sdk.ConfidentialSampling.boundedBigInt(gamma);
      expect(typeof sample).toBe('bigint');
      expect(sample >= -gamma && sample <= gamma).toBe(true);
    }

    const vector = sdk.ConfidentialSampling.bigIntVector(16, gamma);
    expect(vector).toHaveLength(16);
    expect(allBigIntBounded(vector, gamma)).toBe(true);

    const opening = sdk.ConfidentialSampling.bigIntOpening(1, 3, gamma);
    expect(opening.msg).toHaveLength(1);
    expect(opening.rand).toHaveLength(3);
    expect(allBigIntBounded(opening.msg, gamma)).toBe(true);
    expect(allBigIntBounded(opening.rand, gamma)).toBe(true);
  });

  it('samples balance and nullifier proof masks with expected shapes', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const params = sdk.ConfidentialBalance.makeParams(2, 3, 17, 6);
    const gamma = 5;

    const balanceMask = sdk.ConfidentialBalance.sampleMask(params, gamma);
    expect(sdk.ConfidentialBalance.validMask(params, gamma, balanceMask)).toBe(true);

    const balanceMasks = sdk.ConfidentialBalance.sampleMasks(params, gamma, 4);
    expect(balanceMasks).toHaveLength(4);
    expect(balanceMasks.every(mask => sdk.ConfidentialBalance.validMask(params, gamma, mask))).toBe(true);

    const nullifierMask = sdk.ConfidentialTransaction.sampleNullifierMask(params, gamma);
    expect(nullifierMask.msg).toHaveLength(params.n1);
    expect(nullifierMask.rand).toHaveLength(params.n2);
    expect(allBounded(nullifierMask.msg, gamma)).toBe(true);
    expect(allBounded(nullifierMask.rand, gamma)).toBe(true);

    const nullifierMasks = sdk.ConfidentialTransaction.sampleNullifierMasks(params, gamma, 4);
    expect(nullifierMasks).toHaveLength(4);
    expect(nullifierMasks.every(mask =>
      mask.msg.length === params.n1 &&
      mask.rand.length === params.n2 &&
      allBounded(mask.msg, gamma) &&
      allBounded(mask.rand, gamma)
    )).toBe(true);
  });

  it('samples BigInt balance, nullifier, and range proof masks with expected shapes', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);
    const params = sdk.ConfidentialBalanceBigInt.makeParams(2, 3, '4835703278458516765933661', 16n);
    const gamma = 32n;
    const k = 4;

    const balanceMask = sdk.ConfidentialBalanceBigInt.sampleMask(params, gamma);
    expect(sdk.ConfidentialBalanceBigInt.validMask(params, gamma, balanceMask)).toBe(true);

    const balanceMasks = sdk.ConfidentialBalanceBigInt.sampleMasks(params, gamma, 4);
    expect(balanceMasks).toHaveLength(4);
    expect(balanceMasks.every(mask => sdk.ConfidentialBalanceBigInt.validMask(params, gamma, mask))).toBe(true);

    const nullifierMask = sdk.ConfidentialNullifierBigInt.sampleMask(params, gamma);
    expect(nullifierMask.msg).toHaveLength(params.n1);
    expect(nullifierMask.rand).toHaveLength(params.n2);
    expect(allBigIntBounded(nullifierMask.msg, gamma)).toBe(true);
    expect(allBigIntBounded(nullifierMask.rand, gamma)).toBe(true);

    const nullifierMasks = sdk.ConfidentialNullifierBigInt.sampleMasks(params, gamma, 4);
    expect(nullifierMasks).toHaveLength(4);
    expect(nullifierMasks.every(mask =>
      mask.msg.length === params.n1 &&
      mask.rand.length === params.n2 &&
      allBigIntBounded(mask.msg, gamma) &&
      allBigIntBounded(mask.rand, gamma)
    )).toBe(true);

    const amountMasks = sdk.ConfidentialRangeBigInt.sampleAmountMasks(params, gamma, 4);
    expect(amountMasks).toHaveLength(4);
    expect(amountMasks.every(mask => allBigIntBounded(mask, gamma))).toBe(true);

    const pairMasks = sdk.ConfidentialRangeBigInt.samplePairMasks(params, gamma, k, 4);
    expect(pairMasks).toHaveLength(4);
    expect(pairMasks.every(roundMasks =>
      roundMasks.length === k &&
      roundMasks.every(mask => mask.length === params.n2 && allBigIntBounded(mask, gamma))
    )).toBe(true);
  });

  it('rejects unsafe sampler bounds and allocation sizes', async () => {
    const sdk = await import(pathToFileURL(typeScriptEntry).href);

    expect(() => sdk.ConfidentialSampling.boundedInt(-1)).toThrow(RangeError);
    expect(() => sdk.ConfidentialSampling.boundedInt(2 ** 48)).toThrow(RangeError);
    expect(() => sdk.ConfidentialSampling.boundedBigInt(-1n)).toThrow(RangeError);
    expect(() => sdk.ConfidentialSampling.intVector(1_000_001, 1)).toThrow(RangeError);
  });
});
