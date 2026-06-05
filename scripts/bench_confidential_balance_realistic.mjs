#!/usr/bin/env node
import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const sdk = await import(pathToFileURL(path.join(projectRoot, 'isabella.ts/dist/index.mjs')).href);

const iterations = Number(process.env.ITERATIONS ?? '1');
const warmup = Number(process.env.WARMUP ?? '0');
const out = process.env.OUT ?? path.join(projectRoot, 'bench/data/confidential-balance-realistic.json');

if (!Number.isInteger(iterations) || iterations <= 0) {
  throw new Error(`ITERATIONS must be a positive integer, got ${iterations}`);
}
if (!Number.isInteger(warmup) || warmup < 0) {
  throw new Error(`WARMUP must be a non-negative integer, got ${warmup}`);
}

const candidate = {
  name: 'ct_sis_note_mvp_v0',
  architecture: 'SIS note commitment MVP',
  m: 1024,
  n2: 1024,
  q: 8380417,
  beta: 65536,
  gamma: 16777216,
  fsRounds: sdk.ConfidentialBalance.fsRounds(),
};

const params = sdk.ConfidentialBalance.makeParams(
  candidate.m,
  candidate.n2,
  candidate.q,
  candidate.beta
);

function buildStructuredCommitKey() {
  const width = params.n1 + params.n2;
  return Array.from({ length: params.m }, (_, row) =>
    Array.from({ length: width }, (_, col) => {
      if (col === 0) {
        return (row % 7) + 1;
      }
      return col - 1 === row ? 1 : 0;
    })
  );
}

function buildWitness() {
  return Array.from({ length: params.n2 }, (_, index) => (index % 3) - 1);
}

function buildMasks() {
  return Array.from({ length: candidate.fsRounds }, () =>
    Array.from({ length: params.n2 }, (_, index) => (index % 2 === 0 ? 1 : -1))
  );
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
  for (let index = 0; index < warmup; index += 1) {
    fn();
  }
  const samples = [];
  for (let index = 0; index < iterations; index += 1) {
    const start = process.hrtime.bigint();
    fn();
    const end = process.hrtime.bigint();
    samples.push(Number(end - start) / 1_000_000);
  }
  return summarize(samples);
}

const ck = buildStructuredCommitKey();
const witness = buildWitness();
const masks = buildMasks();
const commitment = sdk.ConfidentialBalance.randCommit(params, ck, witness);
const proof = sdk.ConfidentialBalance.fsProve(params, candidate.gamma, ck, commitment, witness, masks);

if (proof === null || !sdk.ConfidentialBalance.fsVerify(params, candidate.gamma, ck, commitment, proof)) {
  throw new Error('failed to construct a valid realistic confidential balance benchmark fixture');
}

const proofJson = JSON.stringify(proof);
const proofSize = {
  json_bytes: Buffer.byteLength(proofJson, 'utf8'),
  a_rows: proof.as.length,
  a_row_width: proof.as[0]?.length ?? 0,
  z_rows: proof.zs.length,
  z_row_width: proof.zs[0]?.length ?? 0,
  response_entries: proof.zs.reduce((acc, row) => acc + row.length, 0),
  commitment_entries: proof.as.reduce((acc, row) => acc + row.length, 0),
};

const result = {
  benchmark: 'confidential-balance-realistic',
  timestamp: new Date().toISOString(),
  warning:
    'Deterministic structured-key runtime benchmark for ct_sis_note_mvp_v0 dimensions. This is not a lattice security estimate or LaZer parameter report.',
  environment: {
    platform: process.platform,
    arch: process.arch,
    node: process.version,
    cpu: os.cpus()[0]?.model ?? 'unknown',
  },
  config: {
    iterations,
    warmup,
    params: { m: params.m, n1: params.n1, n2: params.n2, q: params.q, beta: params.beta },
    gamma: candidate.gamma,
    fsRounds: candidate.fsRounds,
    fixture: {
      candidate: candidate.name,
      commitmentKey: 'deterministic structured identity-plus-message-column matrix',
      witness: 'periodic entries in {-1,0,1}',
      masks: 'periodic entries in {-1,1}',
    },
  },
  proofSize,
  cases: {
    balance_fs_prove_realistic: bench(() => {
      const nextProof = sdk.ConfidentialBalance.fsProve(
        params,
        candidate.gamma,
        ck,
        commitment,
        witness,
        masks
      );
      if (nextProof === null) {
        throw new Error('balance_fs_prove_realistic returned null');
      }
    }),
    balance_fs_verify_realistic: bench(() => {
      if (!sdk.ConfidentialBalance.fsVerify(params, candidate.gamma, ck, commitment, proof)) {
        throw new Error('balance_fs_verify_realistic rejected fixture');
      }
    }),
  },
};

fs.mkdirSync(path.dirname(out), { recursive: true });
fs.writeFileSync(out, `${JSON.stringify(result, null, 2)}\n`);
console.log(JSON.stringify(result, null, 2));
