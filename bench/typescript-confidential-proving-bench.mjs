#!/usr/bin/env node

/**
 * Deterministic TypeScript proof benchmark for the confidential-token slice.
 *
 * Contract:
 * - Measures only stable public TypeScript SDK entrypoints.
 * - Uses fixed fixtures; no hidden randomness or network dependencies.
 * - Prove-only cases validate produced artifacts outside the timed region.
 * - Verify-only cases use precomputed proofs so timing does not include proving.
 * - Fails fast if a proof-producing function returns an invalid artifact.
 */

import fs from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');

function parseArgs(argv) {
  const config = {
    iterations: 20,
    warmup: 5,
    out: null,
    json: false,
    cases: null,
  };

  for (let i = 0; i < argv.length; i += 1) {
    const arg = argv[i];
    if (arg === '--iterations' || arg === '-i') {
      config.iterations = Number(argv[++i]);
    } else if (arg === '--warmup' || arg === '-w') {
      config.warmup = Number(argv[++i]);
    } else if (arg === '--case' || arg === '-c') {
      const raw = argv[++i];
      config.cases = raw.split(',').map((name) => name.trim()).filter(Boolean);
    } else if (arg === '--out' || arg === '-o') {
      config.out = argv[++i];
    } else if (arg === '--json') {
      config.json = true;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node bench/typescript-confidential-proving-bench.mjs [options]

Options:
  -i, --iterations <n>   Timed iterations per benchmark case (default: 20)
  -w, --warmup <n>       Warmup iterations per benchmark case (default: 5)
  -c, --case <name,...>  Benchmark only the named case(s)
  -o, --out <path>       Write JSON results to a file
      --json             Print JSON only
  -h, --help             Show this help
`);
      process.exit(0);
    } else {
      throw new Error(`Unknown argument: ${arg}`);
    }
  }

  if (!Number.isInteger(config.iterations) || config.iterations <= 0) {
    throw new Error(`iterations must be a positive integer, got ${config.iterations}`);
  }
  if (!Number.isInteger(config.warmup) || config.warmup < 0) {
    throw new Error(`warmup must be a non-negative integer, got ${config.warmup}`);
  }

  return config;
}

function assertBuilt() {
  if (!fs.existsSync(typeScriptEntry)) {
    throw new Error(
      `${typeScriptEntry} is missing. Build the TypeScript SDK first with \`make typescript\` or \`cd isabella.ts && bun run build\`.`
    );
  }
}

function median(values) {
  const sorted = [...values].sort((a, b) => a - b);
  const mid = Math.floor(sorted.length / 2);
  return sorted.length % 2 === 0
    ? (sorted[mid - 1] + sorted[mid]) / 2
    : sorted[mid];
}

function stddev(values, mean) {
  if (values.length <= 1) {
    return 0;
  }
  const variance = values.reduce((sum, value) => sum + (value - mean) ** 2, 0) / (values.length - 1);
  return Math.sqrt(variance);
}

function summarizeTimings(samplesNs) {
  const millis = samplesNs.map((value) => Number(value) / 1e6);
  const mean = millis.reduce((sum, value) => sum + value, 0) / millis.length;
  return {
    unit: 'milliseconds',
    min: Math.min(...millis),
    max: Math.max(...millis),
    mean,
    median: median(millis),
    stdev: stddev(millis, mean),
  };
}

function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

function buildFixtures(sdk) {
  const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
  const gamma = 5;
  const rangeK = 3;
  const ck = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const nk = [
    [1, 0, 0],
    [0, 1, 0],
  ];
  const fsRounds = sdk.ConfidentialBalance.fsRounds();

  const commitOfOpening = (opening) =>
    sdk.Zq.matVecMultMod(ck, sdk.Vec.concat(opening.msg, opening.rand), params.q);

  const balanceFixture = {
    params,
    gamma,
    ck,
    witness: [1, 2],
    masks: Array.from({ length: fsRounds }, () => [0, 1]),
  };
  balanceFixture.commitment = sdk.ConfidentialBalance.randCommit(
    params,
    ck,
    balanceFixture.witness
  );
  balanceFixture.proof = sdk.ConfidentialBalance.fsProve(
    params,
    gamma,
    ck,
    balanceFixture.commitment,
    balanceFixture.witness,
    balanceFixture.masks
  );

  const rangeFixture = {
    params,
    gamma,
    k: rangeK,
    ck,
    opening: { msg: [5], rand: [1, 2] },
    bits: [
      { msg: [1], rand: [1, 0] },
      { msg: [0], rand: [0, 1] },
      { msg: [1], rand: [1, 1] },
    ],
    comps: [
      { msg: [0], rand: [0, 1] },
      { msg: [1], rand: [1, 0] },
      { msg: [0], rand: [0, -1] },
    ],
    yAmounts: Array.from({ length: fsRounds }, () => [0, 1]),
    yPairss: Array.from({ length: fsRounds }, () => [
      [1, 0],
      [0, 0],
      [1, -1],
    ]),
  };
  rangeFixture.commitment = commitOfOpening(rangeFixture.opening);
  rangeFixture.proof = sdk.ConfidentialRange.fsProve(
    params,
    gamma,
    rangeK,
    ck,
    rangeFixture.commitment,
    rangeFixture.opening,
    rangeFixture.bits,
    rangeFixture.comps,
    rangeFixture.yAmounts,
    rangeFixture.yPairss
  );

  const txFixture = {
    params,
    gamma,
    k: rangeK,
    ck,
    nk,
    opIn1: { msg: [4], rand: [1, 0] },
    opIn2: { msg: [3], rand: [0, 1] },
    opOut1: clone(rangeFixture.opening),
    opOut2: { msg: [2], rand: [1, 0] },
    out1Bits: clone(rangeFixture.bits),
    out1Comps: clone(rangeFixture.comps),
    out2Bits: [
      { msg: [0], rand: [0, 1] },
      { msg: [1], rand: [1, 0] },
      { msg: [0], rand: [0, 0] },
    ],
    out2Comps: [
      { msg: [1], rand: [1, 0] },
      { msg: [0], rand: [0, 1] },
      { msg: [1], rand: [1, 1] },
    ],
    yIn1: Array.from({ length: fsRounds }, () => ({ msg: [0], rand: [1, 0] })),
    yIn2: Array.from({ length: fsRounds }, () => ({ msg: [1], rand: [0, 1] })),
    yBalance: Array.from({ length: fsRounds }, () => [0, 1]),
    yOut1: clone(rangeFixture.yAmounts),
    yOut1Pairs: clone(rangeFixture.yPairss),
    yOut2: Array.from({ length: fsRounds }, () => [1, 0]),
    yOut2Pairs: Array.from({ length: fsRounds }, () => [
      [0, 1],
      [1, 0],
      [0, 0],
    ]),
  };

  txFixture.cIn1 = commitOfOpening(txFixture.opIn1);
  txFixture.cIn2 = commitOfOpening(txFixture.opIn2);
  txFixture.cOut1 = commitOfOpening(txFixture.opOut1);
  txFixture.cOut2 = commitOfOpening(txFixture.opOut2);
  txFixture.nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, txFixture.opIn1);
  txFixture.nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, txFixture.opIn2);
  txFixture.ledger = [txFixture.cIn1, txFixture.cIn2, [9, 4]];
  txFixture.root = sdk.ConfidentialTransaction.ledgerRoot(params, txFixture.ledger);
  txFixture.spent = [];
  txFixture.balanceCommitment = sdk.ConfidentialBalance.balanceCommitment(
    txFixture.cIn1,
    txFixture.cIn2,
    txFixture.cOut1,
    txFixture.cOut2,
    txFixture.params.q
  );
  txFixture.balanceWitness = sdk.ConfidentialBalance.aggregateRandomness(
    txFixture.opIn1,
    txFixture.opIn2,
    txFixture.opOut1,
    txFixture.opOut2
  );

  const membershipIn1 = sdk.ConfidentialTransaction.membershipProve(
    txFixture.params,
    txFixture.ledger,
    txFixture.cIn1
  );
  const membershipIn2 = sdk.ConfidentialTransaction.membershipProve(
    txFixture.params,
    txFixture.ledger,
    txFixture.cIn2
  );
  const nullifier1 = sdk.ConfidentialTransaction.nullifierFsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.ck,
    txFixture.nk,
    txFixture.cIn1,
    txFixture.nf1,
    txFixture.opIn1,
    txFixture.yIn1
  );
  const nullifier2 = sdk.ConfidentialTransaction.nullifierFsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.ck,
    txFixture.nk,
    txFixture.cIn2,
    txFixture.nf2,
    txFixture.opIn2,
    txFixture.yIn2
  );
  const balanceProof = sdk.ConfidentialBalance.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.ck,
    txFixture.balanceCommitment,
    txFixture.balanceWitness,
    txFixture.yBalance
  );
  const out1RangeProof = sdk.ConfidentialRange.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.k,
    txFixture.ck,
    txFixture.cOut1,
    txFixture.opOut1,
    txFixture.out1Bits,
    txFixture.out1Comps,
    txFixture.yOut1,
    txFixture.yOut1Pairs
  );
  const out2RangeProof = sdk.ConfidentialRange.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.k,
    txFixture.ck,
    txFixture.cOut2,
    txFixture.opOut2,
    txFixture.out2Bits,
    txFixture.out2Comps,
    txFixture.yOut2,
    txFixture.yOut2Pairs
  );
  const txProof = sdk.ConfidentialTransaction.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.k,
    txFixture.ck,
    txFixture.nk,
    txFixture.ledger,
    txFixture.spent,
    txFixture.cIn1,
    txFixture.cIn2,
    txFixture.cOut1,
    txFixture.cOut2,
    txFixture.nf1,
    txFixture.nf2,
    txFixture.opIn1,
    txFixture.opIn2,
    txFixture.opOut1,
    txFixture.opOut2,
    txFixture.out1Bits,
    txFixture.out1Comps,
    txFixture.out2Bits,
    txFixture.out2Comps,
    txFixture.yIn1,
    txFixture.yIn2,
    txFixture.yBalance,
    txFixture.yOut1,
    txFixture.yOut1Pairs,
    txFixture.yOut2,
    txFixture.yOut2Pairs
  );

  const verifiedInputRange1 = sdk.ConfidentialRange.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.k,
    txFixture.ck,
    txFixture.cIn1,
    txFixture.opIn1,
    [
      { msg: [0], rand: [0, 1] },
      { msg: [0], rand: [1, 0] },
      { msg: [1], rand: [1, 1] },
    ],
    [
      { msg: [1], rand: [1, 0] },
      { msg: [1], rand: [0, 1] },
      { msg: [0], rand: [0, -1] },
    ],
    txFixture.yOut1,
    txFixture.yOut1Pairs
  );
  const verifiedInputRange2 = sdk.ConfidentialRange.fsProve(
    txFixture.params,
    txFixture.gamma,
    txFixture.k,
    txFixture.ck,
    txFixture.cIn2,
    txFixture.opIn2,
    [
      { msg: [1], rand: [1, 0] },
      { msg: [1], rand: [0, 1] },
      { msg: [0], rand: [0, 0] },
    ],
    [
      { msg: [0], rand: [0, 1] },
      { msg: [0], rand: [1, 0] },
      { msg: [1], rand: [1, 1] },
    ],
    txFixture.yOut2,
    txFixture.yOut2Pairs
  );

  if (
    membershipIn1 === null ||
    membershipIn2 === null ||
    balanceFixture.proof === null ||
    rangeFixture.proof === null ||
    nullifier1 === null ||
    nullifier2 === null ||
    balanceProof === null ||
    out1RangeProof === null ||
    out2RangeProof === null ||
    txProof === null ||
    verifiedInputRange1 === null ||
    verifiedInputRange2 === null
  ) {
    throw new Error('buildFixtures failed to precompute one or more confidential proof artifacts');
  }

  txFixture.precomputed = {
    membershipIn1,
    membershipIn2,
    nullifier1,
    nullifier2,
    balanceProof,
    out1RangeProof,
    out2RangeProof,
    txProof,
    verifiedNotes: [
      { commitment: txFixture.cIn1, rangeProof: verifiedInputRange1 },
      { commitment: txFixture.cIn2, rangeProof: verifiedInputRange2 },
    ],
  };

  return { balanceFixture, rangeFixture, txFixture, fsRounds };
}

async function loadSdk() {
  assertBuilt();
  return import(pathToFileURL(typeScriptEntry).href);
}

function benchCase(name, description, warmup, iterations, spec) {
  for (let i = 0; i < warmup; i += 1) {
    const result = spec.run();
    if (spec.validate) {
      spec.validate(result);
    }
  }

  const samples = [];
  for (let i = 0; i < iterations; i += 1) {
    const start = process.hrtime.bigint();
    const result = spec.run();
    const end = process.hrtime.bigint();
    samples.push(end - start);
    if (spec.validate) {
      spec.validate(result);
    }
  }

  return {
    name,
    description,
    mode: spec.mode,
    iterations,
    warmupIterations: warmup,
    timing: summarizeTimings(samples),
  };
}

function formatMillis(value) {
  return `${value.toFixed(3)} ms`;
}

function printSummary(results) {
  console.log('TypeScript confidential proof benchmarks');
  console.log('=======================================');
  console.log('');
  for (const result of results.cases) {
    console.log(`${result.name}`);
    console.log(`  ${result.description}`);
    console.log(`  mean:   ${formatMillis(result.timing.mean)}`);
    console.log(`  median: ${formatMillis(result.timing.median)}`);
    console.log(`  min:    ${formatMillis(result.timing.min)}`);
    console.log(`  max:    ${formatMillis(result.timing.max)}`);
    console.log(`  stdev:  ${formatMillis(result.timing.stdev)}`);
    console.log('');
  }
}

function buildResults(config, cases) {
  return {
    benchmark: 'typescript-confidential-proofs',
    timestamp: new Date().toISOString(),
    environment: {
      platform: process.platform,
      arch: process.arch,
      node: process.version,
      cpu: os.cpus()[0]?.model ?? 'unknown',
    },
    config,
    cases,
  };
}

function selectCases(config, allCases) {
  if (config.cases === null) {
    return allCases;
  }

  const wanted = new Set(config.cases);
  const available = new Set(allCases.map((benchmarkCase) => benchmarkCase.name));
  const unknown = config.cases.filter((name) => !available.has(name));
  if (unknown.length > 0) {
    throw new Error(`Unknown benchmark case(s): ${unknown.join(', ')}`);
  }

  return allCases.filter((benchmarkCase) => wanted.has(benchmarkCase.name));
}

function verifyMembership(sdk, params, commitment, proof) {
  return proof !== null && sdk.ConfidentialTransaction.membershipVerify(params, commitment, proof);
}

function verifyNullifier(sdk, fixture, commitment, nullifier, proof) {
  return (
    proof !== null &&
    sdk.ConfidentialTransaction.nullifierFsVerify(
      fixture.params,
      fixture.gamma,
      fixture.ck,
      fixture.nk,
      commitment,
      nullifier,
      proof
    )
  );
}

function verifyBalance(sdk, fixture, commitment, proof, witness = null) {
  if (proof === null) {
    return false;
  }
  if (witness !== null && !sdk.ConfidentialBalance.relation(fixture.params, fixture.ck, commitment, witness)) {
    return false;
  }
  return sdk.ConfidentialBalance.fsVerify(
    fixture.params,
    fixture.gamma,
    fixture.ck,
    commitment,
    proof
  );
}

function verifyRange(sdk, fixture, commitment, proof) {
  return (
    proof !== null &&
    sdk.ConfidentialRange.fsVerify(
      fixture.params,
      fixture.gamma,
      fixture.k,
      fixture.ck,
      commitment,
      proof
    )
  );
}

function verifyTransaction(sdk, fixture, proof) {
  return (
    proof !== null &&
    sdk.ConfidentialTransaction.fsVerify(
      fixture.params,
      fixture.gamma,
      fixture.k,
      fixture.ck,
      fixture.nk,
      fixture.root,
      fixture.spent,
      fixture.cIn1,
      fixture.cIn2,
      fixture.cOut1,
      fixture.cOut2,
      fixture.nf1,
      fixture.nf2,
      proof
    )
  );
}

function verifyFullProcessArtifacts(sdk, fixture, artifacts) {
  return (
    verifyMembership(sdk, fixture.params, fixture.cIn1, artifacts.membershipIn1) &&
    verifyMembership(sdk, fixture.params, fixture.cIn2, artifacts.membershipIn2) &&
    verifyNullifier(sdk, fixture, fixture.cIn1, fixture.nf1, artifacts.nullifier1) &&
    verifyNullifier(sdk, fixture, fixture.cIn2, fixture.nf2, artifacts.nullifier2) &&
    verifyBalance(sdk, fixture, fixture.balanceCommitment, artifacts.balanceProof, fixture.balanceWitness) &&
    verifyRange(sdk, fixture, fixture.cOut1, artifacts.out1RangeProof) &&
    verifyRange(sdk, fixture, fixture.cOut2, artifacts.out2RangeProof) &&
    verifyTransaction(sdk, fixture, artifacts.txProof)
  );
}

const config = parseArgs(process.argv.slice(2));
const sdk = await loadSdk();
const { balanceFixture, rangeFixture, txFixture } = buildFixtures(sdk);

const caseSpecs = [
  {
    name: 'membership_prove',
    description: 'Authenticated ledger membership proof for one input note.',
    mode: 'prove-only',
    run() {
      return sdk.ConfidentialTransaction.membershipProve(
        txFixture.params,
        txFixture.ledger,
        txFixture.cIn2
      );
    },
    validate(proof) {
      if (!verifyMembership(sdk, txFixture.params, txFixture.cIn2, proof)) {
        throw new Error('membershipProve produced an invalid proof');
      }
    },
  },
  {
    name: 'membership_verify',
    description: 'Authenticated ledger membership verifier over a precomputed proof.',
    mode: 'verify-only',
    run() {
      return sdk.ConfidentialTransaction.membershipVerify(
        txFixture.params,
        txFixture.cIn2,
        txFixture.precomputed.membershipIn2
      );
    },
    validate(valid) {
      if (!valid) {
        throw new Error('membershipVerify rejected the precomputed proof');
      }
    },
  },
  {
    name: 'nullifier_fs_prove',
    description: 'Repeated Fiat-Shamir nullifier proof for one input note.',
    mode: 'prove-only',
    run() {
      return sdk.ConfidentialTransaction.nullifierFsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.ck,
        txFixture.nk,
        txFixture.cIn1,
        txFixture.nf1,
        txFixture.opIn1,
        txFixture.yIn1
      );
    },
    validate(proof) {
      if (!verifyNullifier(sdk, txFixture, txFixture.cIn1, txFixture.nf1, proof)) {
        throw new Error('nullifierFsProve produced an invalid proof');
      }
    },
  },
  {
    name: 'nullifier_fs_verify',
    description: 'Repeated Fiat-Shamir nullifier verifier over a precomputed proof.',
    mode: 'verify-only',
    run() {
      return sdk.ConfidentialTransaction.nullifierFsVerify(
        txFixture.params,
        txFixture.gamma,
        txFixture.ck,
        txFixture.nk,
        txFixture.cIn1,
        txFixture.nf1,
        txFixture.precomputed.nullifier1
      );
    },
    validate(valid) {
      if (!valid) {
        throw new Error('nullifierFsVerify rejected the precomputed proof');
      }
    },
  },
  {
    name: 'balance_fs_prove',
    description: 'Repeated Fiat-Shamir balance proof over the zero-message residual commitment.',
    mode: 'prove-only',
    run() {
      return sdk.ConfidentialBalance.fsProve(
        balanceFixture.params,
        balanceFixture.gamma,
        balanceFixture.ck,
        balanceFixture.commitment,
        balanceFixture.witness,
        balanceFixture.masks
      );
    },
    validate(proof) {
      if (!verifyBalance(sdk, balanceFixture, balanceFixture.commitment, proof, balanceFixture.witness)) {
        throw new Error('balanceFsProve produced an invalid proof');
      }
    },
  },
  {
    name: 'balance_fs_verify',
    description: 'Repeated Fiat-Shamir balance verifier over a precomputed proof.',
    mode: 'verify-only',
    run() {
      return sdk.ConfidentialBalance.fsVerify(
        balanceFixture.params,
        balanceFixture.gamma,
        balanceFixture.ck,
        balanceFixture.commitment,
        balanceFixture.proof
      );
    },
    validate(valid) {
      if (!valid) {
        throw new Error('balanceFsVerify rejected the precomputed proof');
      }
    },
  },
  {
    name: 'range_fs_prove',
    description: 'Repeated Fiat-Shamir bounded-amount proof for one output note.',
    mode: 'prove-only',
    run() {
      return sdk.ConfidentialRange.fsProve(
        rangeFixture.params,
        rangeFixture.gamma,
        rangeFixture.k,
        rangeFixture.ck,
        rangeFixture.commitment,
        rangeFixture.opening,
        rangeFixture.bits,
        rangeFixture.comps,
        rangeFixture.yAmounts,
        rangeFixture.yPairss
      );
    },
    validate(proof) {
      if (!verifyRange(sdk, rangeFixture, rangeFixture.commitment, proof)) {
        throw new Error('rangeFsProve produced an invalid proof');
      }
    },
  },
  {
    name: 'range_fs_verify',
    description: 'Repeated Fiat-Shamir bounded-amount verifier over a precomputed proof.',
    mode: 'verify-only',
    run() {
      return sdk.ConfidentialRange.fsVerify(
        rangeFixture.params,
        rangeFixture.gamma,
        rangeFixture.k,
        rangeFixture.ck,
        rangeFixture.commitment,
        rangeFixture.proof
      );
    },
    validate(valid) {
      if (!valid) {
        throw new Error('rangeFsVerify rejected the precomputed proof');
      }
    },
  },
  {
    name: 'transaction_fs_prove',
    description: 'Top-level 2-in/2-out confidential transfer proof generator.',
    mode: 'prove-only',
    run() {
      return sdk.ConfidentialTransaction.fsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.k,
        txFixture.ck,
        txFixture.nk,
        txFixture.ledger,
        txFixture.spent,
        txFixture.cIn1,
        txFixture.cIn2,
        txFixture.cOut1,
        txFixture.cOut2,
        txFixture.nf1,
        txFixture.nf2,
        txFixture.opIn1,
        txFixture.opIn2,
        txFixture.opOut1,
        txFixture.opOut2,
        txFixture.out1Bits,
        txFixture.out1Comps,
        txFixture.out2Bits,
        txFixture.out2Comps,
        txFixture.yIn1,
        txFixture.yIn2,
        txFixture.yBalance,
        txFixture.yOut1,
        txFixture.yOut1Pairs,
        txFixture.yOut2,
        txFixture.yOut2Pairs
      );
    },
    validate(proof) {
      if (!verifyTransaction(sdk, txFixture, proof)) {
        throw new Error('transactionFsProve produced an invalid proof');
      }
    },
  },
  {
    name: 'transaction_fs_verify',
    description: 'Top-level 2-in/2-out confidential transfer verifier over a precomputed proof.',
    mode: 'verify-only',
    run() {
      return sdk.ConfidentialTransaction.fsVerify(
        txFixture.params,
        txFixture.gamma,
        txFixture.k,
        txFixture.ck,
        txFixture.nk,
        txFixture.root,
        txFixture.spent,
        txFixture.cIn1,
        txFixture.cIn2,
        txFixture.cOut1,
        txFixture.cOut2,
        txFixture.nf1,
        txFixture.nf2,
        txFixture.precomputed.txProof
      );
    },
    validate(valid) {
      if (!valid) {
        throw new Error('transactionFsVerify rejected the precomputed proof');
      }
    },
  },
  {
    name: 'full_confidential_transfer_prove',
    description: 'Deterministic end-to-end client proving flow: derive public data, build subproofs, and build the transaction proof.',
    mode: 'prove-only',
    run() {
      const membershipIn1 = sdk.ConfidentialTransaction.membershipProve(
        txFixture.params,
        txFixture.ledger,
        txFixture.cIn1
      );
      const membershipIn2 = sdk.ConfidentialTransaction.membershipProve(
        txFixture.params,
        txFixture.ledger,
        txFixture.cIn2
      );
      const nullifier1 = sdk.ConfidentialTransaction.nullifierFsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.ck,
        txFixture.nk,
        txFixture.cIn1,
        txFixture.nf1,
        txFixture.opIn1,
        txFixture.yIn1
      );
      const nullifier2 = sdk.ConfidentialTransaction.nullifierFsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.ck,
        txFixture.nk,
        txFixture.cIn2,
        txFixture.nf2,
        txFixture.opIn2,
        txFixture.yIn2
      );
      const balanceCommitment = sdk.ConfidentialBalance.balanceCommitment(
        txFixture.cIn1,
        txFixture.cIn2,
        txFixture.cOut1,
        txFixture.cOut2,
        txFixture.params.q
      );
      const balanceProof = sdk.ConfidentialBalance.fsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.ck,
        balanceCommitment,
        sdk.ConfidentialBalance.aggregateRandomness(
          txFixture.opIn1,
          txFixture.opIn2,
          txFixture.opOut1,
          txFixture.opOut2
        ),
        txFixture.yBalance
      );
      const range1 = sdk.ConfidentialRange.fsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.k,
        txFixture.ck,
        txFixture.cOut1,
        txFixture.opOut1,
        txFixture.out1Bits,
        txFixture.out1Comps,
        txFixture.yOut1,
        txFixture.yOut1Pairs
      );
      const range2 = sdk.ConfidentialRange.fsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.k,
        txFixture.ck,
        txFixture.cOut2,
        txFixture.opOut2,
        txFixture.out2Bits,
        txFixture.out2Comps,
        txFixture.yOut2,
        txFixture.yOut2Pairs
      );
      const txProof = sdk.ConfidentialTransaction.fsProve(
        txFixture.params,
        txFixture.gamma,
        txFixture.k,
        txFixture.ck,
        txFixture.nk,
        txFixture.ledger,
        txFixture.spent,
        txFixture.cIn1,
        txFixture.cIn2,
        txFixture.cOut1,
        txFixture.cOut2,
        txFixture.nf1,
        txFixture.nf2,
        txFixture.opIn1,
        txFixture.opIn2,
        txFixture.opOut1,
        txFixture.opOut2,
        txFixture.out1Bits,
        txFixture.out1Comps,
        txFixture.out2Bits,
        txFixture.out2Comps,
        txFixture.yIn1,
        txFixture.yIn2,
        txFixture.yBalance,
        txFixture.yOut1,
        txFixture.yOut1Pairs,
        txFixture.yOut2,
        txFixture.yOut2Pairs
      );
      return {
        membershipIn1,
        membershipIn2,
        nullifier1,
        nullifier2,
        balanceCommitment,
        balanceProof,
        out1RangeProof: range1,
        out2RangeProof: range2,
        txProof,
      };
    },
    validate(artifacts) {
      if (
        artifacts.membershipIn1 === null ||
        artifacts.membershipIn2 === null ||
        artifacts.nullifier1 === null ||
        artifacts.nullifier2 === null ||
        artifacts.balanceProof === null ||
        artifacts.out1RangeProof === null ||
        artifacts.out2RangeProof === null ||
        artifacts.txProof === null
      ) {
        throw new Error('full process failed to produce one or more expected artifacts');
      }
      if (
        !verifyMembership(sdk, txFixture.params, txFixture.cIn1, artifacts.membershipIn1) ||
        !verifyMembership(sdk, txFixture.params, txFixture.cIn2, artifacts.membershipIn2) ||
        !verifyNullifier(sdk, txFixture, txFixture.cIn1, txFixture.nf1, artifacts.nullifier1) ||
        !verifyNullifier(sdk, txFixture, txFixture.cIn2, txFixture.nf2, artifacts.nullifier2) ||
        !verifyBalance(sdk, txFixture, artifacts.balanceCommitment, artifacts.balanceProof, txFixture.balanceWitness) ||
        !verifyRange(sdk, txFixture, txFixture.cOut1, artifacts.out1RangeProof) ||
        !verifyRange(sdk, txFixture, txFixture.cOut2, artifacts.out2RangeProof) ||
        !verifyTransaction(sdk, txFixture, artifacts.txProof)
      ) {
        throw new Error('full process produced one or more invalid confidential artifacts');
      }
    },
  },
  {
    name: 'full_confidential_transfer_verify',
    description: 'Deterministic end-to-end verifier flow over precomputed subproofs and the precomputed transaction proof.',
    mode: 'verify-only',
    run() {
      return verifyFullProcessArtifacts(sdk, txFixture, txFixture.precomputed);
    },
    validate(valid) {
      if (!valid) {
        throw new Error('full process verifier rejected the precomputed artifact set');
      }
    },
  },
  {
    name: 'full_confidential_transfer_process',
    description: 'Deterministic end-to-end client flow: derive public data, build subproofs, build the transaction proof, then verify the full artifact set.',
    mode: 'prove+verify',
    run() {
      const artifacts = caseSpecs.find((spec) => spec.name === 'full_confidential_transfer_prove').run();
      return verifyFullProcessArtifacts(sdk, txFixture, artifacts);
    },
    validate(valid) {
      if (!valid) {
        throw new Error('full process end-to-end benchmark rejected the generated artifact set');
      }
    },
  },
];

const selectedCaseSpecs = selectCases(config, caseSpecs);
const cases = selectedCaseSpecs.map((caseSpec) =>
  benchCase(
    caseSpec.name,
    caseSpec.description,
    config.warmup,
    config.iterations,
    caseSpec
  )
);
const results = buildResults(config, cases);

if (config.out !== null) {
  fs.writeFileSync(config.out, `${JSON.stringify(results, null, 2)}\n`);
}

if (config.json) {
  console.log(JSON.stringify(results, null, 2));
} else {
  printSummary(results);
  if (config.out !== null) {
    console.log(`JSON written to ${config.out}`);
  }
}
