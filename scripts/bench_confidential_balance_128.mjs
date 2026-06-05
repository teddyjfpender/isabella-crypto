#!/usr/bin/env node
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const sdk = await import(pathToFileURL(path.join(projectRoot, 'isabella.ts/dist/index.mjs')).href);

const iterations = Number(process.env.ITERATIONS ?? '5');
const warmup = Number(process.env.WARMUP ?? '1');
const out = process.env.OUT ?? path.join(projectRoot, 'bench/data/confidential-balance-128.json');

const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
const gamma = 5;
const ck = [
  [1, 0, 0],
  [0, 1, 0],
];
const witness = [1, 2];
const commitment = sdk.ConfidentialBalance.randCommit(params, ck, witness);
const fsRounds = sdk.ConfidentialBalance.fsRounds();
const masks = Array.from({ length: fsRounds }, () => [0, 1]);
const proof = sdk.ConfidentialBalance.fsProve(params, gamma, ck, commitment, witness, masks);

if (proof === null || !sdk.ConfidentialBalance.fsVerify(params, gamma, ck, commitment, proof)) {
  throw new Error('failed to construct a valid confidential balance benchmark fixture');
}

function summarize(samples) {
  const sorted = [...samples].sort((a, b) => a - b);
  const mean = samples.reduce((acc, value) => acc + value, 0) / samples.length;
  const variance = samples.reduce((acc, value) => acc + (value - mean) ** 2, 0) / samples.length;
  return {
    min_ms: sorted[0],
    median_ms: sorted[Math.floor(sorted.length / 2)],
    max_ms: sorted[sorted.length - 1],
    mean_ms: mean,
    stdev_ms: Math.sqrt(variance),
  };
}

function bench(fn) {
  for (let i = 0; i < warmup; i += 1) {
    fn();
  }
  const samples = [];
  for (let i = 0; i < iterations; i += 1) {
    const start = process.hrtime.bigint();
    fn();
    const end = process.hrtime.bigint();
    samples.push(Number(end - start) / 1_000_000);
  }
  return summarize(samples);
}

const result = {
  benchmark: 'confidential-balance-128',
  timestamp: new Date().toISOString(),
  environment: {
    platform: process.platform,
    arch: process.arch,
    node: process.version,
    cpu: os.cpus()[0]?.model ?? 'unknown',
  },
  config: {
    iterations,
    warmup,
    fsRounds,
    params: { m: params.m, n2: params.n2, q: params.q, beta: params.beta, gamma },
  },
  cases: {
    balance_fs_prove: bench(() => {
      const nextProof = sdk.ConfidentialBalance.fsProve(params, gamma, ck, commitment, witness, masks);
      if (nextProof === null) {
        throw new Error('balance_fs_prove returned null');
      }
    }),
    balance_fs_verify: bench(() => {
      if (!sdk.ConfidentialBalance.fsVerify(params, gamma, ck, commitment, proof)) {
        throw new Error('balance_fs_verify rejected fixture');
      }
    }),
  },
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(result, null, 2)}\n`);
console.log(JSON.stringify(result, null, 2));
