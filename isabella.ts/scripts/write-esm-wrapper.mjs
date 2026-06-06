import { mkdir, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const distDir = path.join(__dirname, '..', 'dist');
const outputFile = path.join(distDir, 'index.mjs');

const wrapper = `import canon from './index.js';

export const { Zq, Vec, Mat, Dilithium, ConfidentialBignum, ConfidentialSampling, ConfidentialBalance, ConfidentialBalanceBigInt, ConfidentialRange, ConfidentialMerkle, ConfidentialTransaction, runtime } = canon;
export default canon;
`;

await mkdir(distDir, { recursive: true });
await writeFile(outputFile, wrapper, 'utf8');
