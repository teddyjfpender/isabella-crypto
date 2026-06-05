#!/usr/bin/env node
import fs from 'node:fs';
import path from 'node:path';
import process from 'node:process';
import { fileURLToPath } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');

const defaults = {
  balance128: path.join(projectRoot, 'bench/data/confidential-balance-128.json'),
  realistic: path.join(projectRoot, 'bench/data/confidential-balance-realistic.json'),
};

const budgets = {
  balance128ProveMedianMs: Number(process.env.CT_BUDGET_BALANCE_128_PROVE_MS ?? '50'),
  balance128VerifyMedianMs: Number(process.env.CT_BUDGET_BALANCE_128_VERIFY_MS ?? '50'),
  realisticProveMedianMs: Number(process.env.CT_BUDGET_REALISTIC_PROVE_MS ?? '10000'),
  realisticVerifyMedianMs: Number(process.env.CT_BUDGET_REALISTIC_VERIFY_MS ?? '10000'),
  realisticProofJsonBytes: Number(process.env.CT_BUDGET_REALISTIC_PROOF_JSON_BYTES ?? '1200000'),
};

function parseArgs(argv) {
  const args = { ...defaults };
  for (let index = 0; index < argv.length; index += 1) {
    const arg = argv[index];
    if (arg === '--balance128') {
      args.balance128 = path.resolve(argv[index + 1]);
      index += 1;
    } else if (arg === '--realistic') {
      args.realistic = path.resolve(argv[index + 1]);
      index += 1;
    } else if (arg === '--help' || arg === '-h') {
      console.log(
        'Usage: node scripts/check_confidential_bench_budgets.mjs [--balance128 PATH] [--realistic PATH]'
      );
      process.exit(0);
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }
  return args;
}

function readJson(filePath) {
  return JSON.parse(fs.readFileSync(filePath, 'utf8'));
}

function requireNumber(value, label) {
  if (typeof value !== 'number' || !Number.isFinite(value)) {
    throw new Error(`${label} must be a finite number`);
  }
  return value;
}

function assertAtMost(actual, limit, label) {
  if (actual > limit) {
    throw new Error(`${label} budget exceeded: ${actual} > ${limit}`);
  }
}

function assertEqual(actual, expected, label) {
  if (actual !== expected) {
    throw new Error(`${label} mismatch: ${actual} !== ${expected}`);
  }
}

const args = parseArgs(process.argv.slice(2));
const balance128 = readJson(args.balance128);
const realistic = readJson(args.realistic);

assertEqual(balance128.benchmark, 'confidential-balance-128', '128-round benchmark name');
assertEqual(balance128.config?.fsRounds, 128, '128-round benchmark Fiat-Shamir rounds');
assertEqual(realistic.benchmark, 'confidential-balance-realistic', 'realistic benchmark name');
assertEqual(realistic.config?.fsRounds, 128, 'realistic benchmark Fiat-Shamir rounds');
assertEqual(realistic.config?.fixture?.candidate, 'ct_sis_note_mvp_v0', 'realistic benchmark candidate');

const balance128Prove = requireNumber(
  balance128.cases?.balance_fs_prove?.median_ms,
  'balance_fs_prove median_ms'
);
const balance128Verify = requireNumber(
  balance128.cases?.balance_fs_verify?.median_ms,
  'balance_fs_verify median_ms'
);
const realisticProve = requireNumber(
  realistic.cases?.balance_fs_prove_realistic?.median_ms,
  'balance_fs_prove_realistic median_ms'
);
const realisticVerify = requireNumber(
  realistic.cases?.balance_fs_verify_realistic?.median_ms,
  'balance_fs_verify_realistic median_ms'
);
const realisticProofBytes = requireNumber(
  realistic.proofSize?.json_bytes,
  'realistic proofSize.json_bytes'
);

assertAtMost(balance128Prove, budgets.balance128ProveMedianMs, 'balance_fs_prove median_ms');
assertAtMost(balance128Verify, budgets.balance128VerifyMedianMs, 'balance_fs_verify median_ms');
assertAtMost(realisticProve, budgets.realisticProveMedianMs, 'balance_fs_prove_realistic median_ms');
assertAtMost(realisticVerify, budgets.realisticVerifyMedianMs, 'balance_fs_verify_realistic median_ms');
assertAtMost(realisticProofBytes, budgets.realisticProofJsonBytes, 'realistic proof JSON bytes');

assertEqual(realistic.proofSize?.a_rows, 128, 'realistic proof announcement rows');
assertEqual(realistic.proofSize?.z_rows, 128, 'realistic proof response rows');
assertEqual(realistic.proofSize?.a_row_width, 1024, 'realistic proof announcement width');
assertEqual(realistic.proofSize?.z_row_width, 1024, 'realistic proof response width');

console.log(JSON.stringify({
  gate: 'confidential-bench-budgets',
  status: 'passed',
  budgets,
  observed: {
    balance128Prove,
    balance128Verify,
    realisticProve,
    realisticVerify,
    realisticProofBytes,
  },
}, null, 2));
