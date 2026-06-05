#!/usr/bin/env node

/**
 * Deterministic comparison harness for confidential verifier hot paths.
 *
 * Measures the current js_of_ocaml-backed TypeScript verifier against native
 * OCaml and Haskell CLI verifier loops that parse the proof once and then
 * benchmark the pure verification function in-process.
 */

import fs from 'node:fs';
import path from 'node:path';
import { execFileSync } from 'node:child_process';
import { fileURLToPath, pathToFileURL } from 'node:url';

const __filename = fileURLToPath(import.meta.url);
const __dirname = path.dirname(__filename);
const projectRoot = path.resolve(__dirname, '..');
const typeScriptEntry = path.join(projectRoot, 'isabella.ts', 'dist', 'index.mjs');
const defaultOcamlCli = path.join(projectRoot, 'isabella.ml', '_build', 'default', 'bin', 'isabella_cli.exe');
const haskellDir = path.join(projectRoot, 'isabella.hs');

function parseArgs(argv) {
  const config = {
    iterations: 1,
    warmup: 0,
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
      config.cases = argv[++i].split(',').map((name) => name.trim()).filter(Boolean);
    } else if (arg === '--json') {
      config.json = true;
    } else if (arg === '--help' || arg === '-h') {
      console.log(`Usage: node bench/confidential-verifier-compare.mjs [options]

Options:
  -i, --iterations <n>   Timed iterations per benchmark case (default: 1)
  -w, --warmup <n>       Warmup iterations per benchmark case (default: 0)
  -c, --case <name,...>  Benchmark only named case(s): range_fs_verify,transaction_fs_verify
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
    throw new Error(`${typeScriptEntry} is missing. Build the TypeScript SDK first.`);
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

function summarizeSamplesNs(samplesNs) {
  const meanNs = samplesNs.reduce((sum, value) => sum + value, 0) / samplesNs.length;
  return {
    unit: 'nanoseconds',
    iterations: samplesNs.length,
    totalNs: samplesNs.reduce((sum, value) => sum + value, 0),
    meanNs,
    medianNs: median(samplesNs),
    minNs: Math.min(...samplesNs),
    maxNs: Math.max(...samplesNs),
    stdevNs: stddev(samplesNs, meanNs),
  };
}

function clone(value) {
  return JSON.parse(JSON.stringify(value));
}

function listRangeProof(proof) {
  if ('amountAs' in proof && 'amountZs' in proof && 'pairAss' in proof && 'pairZss' in proof) {
    return {
      bits: proof.bits,
      comps: proof.comps,
      amountAs: proof.amountAs,
      amountZs: proof.amountZs,
      pairAss: proof.pairAss,
      pairZss: proof.pairZss,
    };
  }
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return {
      bits: proof.bits,
      comps: proof.comps,
      amountAs: proof.rounds.map((round) => round.amountA),
      amountZs: proof.rounds.map((round) => round.amountZ),
      pairAss: proof.rounds.map((round) => round.pairAs),
      pairZss: proof.rounds.map((round) => round.pairZs),
    };
  }
  return {
    bits: proof.bits,
    comps: proof.comps,
    amountAs: [proof.amountA],
    amountZs: [proof.amountZ],
    pairAss: [proof.pairAs],
    pairZss: [proof.pairZs],
  };
}

function listNullifierProof(proof) {
  if ('aCommits' in proof && 'aNullifiers' in proof && 'zMsgs' in proof && 'zRands' in proof) {
    return {
      aCommits: proof.aCommits,
      aNullifiers: proof.aNullifiers,
      zMsgs: proof.zMsgs,
      zRands: proof.zRands,
    };
  }
  if ('rounds' in proof && Array.isArray(proof.rounds)) {
    return {
      aCommits: proof.rounds.map((round) => round.aCommit),
      aNullifiers: proof.rounds.map((round) => round.aNullifier),
      zMsgs: proof.rounds.map((round) => round.zMsg),
      zRands: proof.rounds.map((round) => round.zRand),
    };
  }
  return {
    aCommits: [proof.aCommit],
    aNullifiers: [proof.aNullifier],
    zMsgs: [proof.zMsg],
    zRands: [proof.zRand],
  };
}

function runJavaScriptBenchmark(warmup, iterations, verify) {
  for (let i = 0; i < warmup; i += 1) {
    if (!verify()) {
      throw new Error('JavaScript verifier rejected the benchmark fixture during warmup');
    }
  }

  const samples = [];
  let allValid = true;
  for (let i = 0; i < iterations; i += 1) {
    const start = process.hrtime.bigint();
    const valid = verify();
    const stop = process.hrtime.bigint();
    allValid &&= valid;
    samples.push(Number(stop - start));
  }

  return {
    backend: 'typescript-js',
    valid: allValid,
    timing: summarizeSamplesNs(samples),
  };
}

function parseCliBenchmark(output) {
  const parsed = JSON.parse(output);
  if (parsed && typeof parsed === 'object' && 'error' in parsed) {
    throw new Error(`CLI benchmark failed: ${parsed.error}`);
  }
  return parsed.result;
}

function normalizeCliBenchmarkResult(backend, stats) {
  return {
    backend,
    valid: stats.valid,
    timing: {
      unit: 'nanoseconds',
      iterations: stats.iterations,
      totalNs: Number(stats.totalNs),
      meanNs: Number(stats.meanNs),
      medianNs: Number(stats.medianNs ?? stats.meanNs),
      minNs: Number(stats.minNs),
      maxNs: Number(stats.maxNs),
      stdevNs: Number(stats.stdevNs ?? 0),
    },
  };
}

function findBuiltHaskellCli(root) {
  if (!fs.existsSync(root)) {
    return null;
  }

  const matches = [];
  function walk(dir) {
    for (const entry of fs.readdirSync(dir, { withFileTypes: true })) {
      const fullPath = path.join(dir, entry.name);
      if (entry.isDirectory()) {
        walk(fullPath);
      } else if (entry.isFile() && entry.name === 'isabella-cli') {
        matches.push(fullPath);
      }
    }
  }

  walk(root);
  matches.sort((left, right) => fs.statSync(right).mtimeMs - fs.statSync(left).mtimeMs);
  return matches[0] ?? null;
}

function resolveBackends() {
  const ocaml = process.env.ISABELLA_OCAML_CLI
    ? path.resolve(process.env.ISABELLA_OCAML_CLI)
    : defaultOcamlCli;
  const haskell = process.env.ISABELLA_HASKELL_CLI
    ? path.resolve(process.env.ISABELLA_HASKELL_CLI)
    : findBuiltHaskellCli(path.join(haskellDir, 'dist-newstyle'));

  return {
    ocaml: fs.existsSync(ocaml) ? ocaml : null,
    haskell: haskell && fs.existsSync(haskell) ? haskell : null,
  };
}

function buildFixtures(sdk, requested) {
  const needRange = requested.includes('range_fs_verify') || requested.includes('transaction_fs_verify');
  const needTransaction = requested.includes('transaction_fs_verify');
  const params = sdk.ConfidentialBalance.makeParams(2, 2, 17, 6);
  const gamma = 5;
  const k = 3;
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

  const range = needRange ? {
    params,
    gamma,
    k,
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
  } : null;
  if (range) {
    range.commitment = commitOfOpening(range.opening);
    range.proof = sdk.ConfidentialRange.fsProve(
      params,
      gamma,
      k,
      ck,
      range.commitment,
      range.opening,
      range.bits,
      range.comps,
      range.yAmounts,
      range.yPairss
    );
    if (range.proof === null || !sdk.ConfidentialRange.fsVerify(params, gamma, k, ck, range.commitment, range.proof)) {
      throw new Error('Failed to build a valid range_fs_verify benchmark fixture');
    }
  }

  const tx = needTransaction ? {
    params,
    gamma,
    k,
    ck,
    nk,
    opIn1: { msg: [4], rand: [1, 0] },
    opIn2: { msg: [3], rand: [0, 1] },
    opOut1: clone(range.opening),
    opOut2: { msg: [2], rand: [1, 0] },
    out1Bits: clone(range.bits),
    out1Comps: clone(range.comps),
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
    yOut1: clone(range.yAmounts),
    yOut1Pairs: clone(range.yPairss),
    yOut2: Array.from({ length: fsRounds }, () => [1, 0]),
    yOut2Pairs: Array.from({ length: fsRounds }, () => [
      [0, 1],
      [1, 0],
      [0, 0],
    ]),
  } : null;
  if (tx) {
    tx.cIn1 = commitOfOpening(tx.opIn1);
    tx.cIn2 = commitOfOpening(tx.opIn2);
    tx.cOut1 = commitOfOpening(tx.opOut1);
    tx.cOut2 = commitOfOpening(tx.opOut2);
    tx.nf1 = sdk.ConfidentialTransaction.nullifier(params, nk, tx.opIn1);
    tx.nf2 = sdk.ConfidentialTransaction.nullifier(params, nk, tx.opIn2);
    tx.ledger = [tx.cIn1, tx.cIn2, [9, 4]];
    tx.root = sdk.ConfidentialTransaction.ledgerRoot(params, tx.ledger);
    tx.spent = [];

    tx.proof = sdk.ConfidentialTransaction.fsProve(
      params,
      gamma,
      k,
      ck,
      nk,
      tx.ledger,
      tx.spent,
      tx.cIn1,
      tx.cIn2,
      tx.cOut1,
      tx.cOut2,
      tx.nf1,
      tx.nf2,
      tx.opIn1,
      tx.opIn2,
      tx.opOut1,
      tx.opOut2,
      tx.out1Bits,
      tx.out1Comps,
      tx.out2Bits,
      tx.out2Comps,
      tx.yIn1,
      tx.yIn2,
      tx.yBalance,
      tx.yOut1,
      tx.yOut1Pairs,
      tx.yOut2,
      tx.yOut2Pairs
    );
    if (
      tx.proof === null ||
      !sdk.ConfidentialTransaction.fsVerify(
        params,
        gamma,
        k,
        ck,
        nk,
        tx.root,
        tx.spent,
        tx.cIn1,
        tx.cIn2,
        tx.cOut1,
        tx.cOut2,
        tx.nf1,
        tx.nf2,
        tx.proof
      )
    ) {
      throw new Error('Failed to build a valid transaction_fs_verify benchmark fixture');
    }
  }

  return { range, tx };
}

function formatNs(ns) {
  if (ns >= 1_000_000) {
    return `${(ns / 1_000_000).toFixed(3)} ms`;
  }
  if (ns >= 1_000) {
    return `${(ns / 1_000).toFixed(3)} us`;
  }
  return `${ns.toFixed(0)} ns`;
}

function printSummary(results, backends) {
  console.log('Confidential verifier comparison');
  console.log('===============================');
  console.log('');
  if (!backends.ocaml || !backends.haskell) {
    console.log(`Available native backends: ocaml=${Boolean(backends.ocaml)}, haskell=${Boolean(backends.haskell)}`);
    console.log('');
  }

  for (const result of results) {
    console.log(result.case);
    for (const backend of result.backends) {
      console.log(`  ${backend.backend}: mean ${formatNs(backend.timing.meanNs)} min ${formatNs(backend.timing.minNs)} max ${formatNs(backend.timing.maxNs)} valid=${backend.valid}`);
    }
    const js = result.backends.find((backend) => backend.backend === 'typescript-js');
    for (const backend of result.backends) {
      if (backend.backend !== 'typescript-js' && js) {
        console.log(`  ${backend.backend} vs js: ${(js.timing.meanNs / backend.timing.meanNs).toFixed(2)}x`);
      }
    }
    console.log('');
  }
}

async function main() {
  const config = parseArgs(process.argv.slice(2));
  assertBuilt();
  const sdk = await import(pathToFileURL(typeScriptEntry).href);
  const backends = resolveBackends();
  const requested = config.cases ?? ['range_fs_verify', 'transaction_fs_verify'];
  const fixtures = buildFixtures(sdk, requested);
  const results = [];

  if (requested.includes('range_fs_verify')) {
    const rangeListed = listRangeProof(fixtures.range.proof);
    const backendsForCase = [
      runJavaScriptBenchmark(config.warmup, config.iterations, () =>
        sdk.ConfidentialRange.fsVerify(
          fixtures.range.params,
          fixtures.range.gamma,
          fixtures.range.k,
          fixtures.range.ck,
          fixtures.range.commitment,
          fixtures.range.proof
        )
      ),
    ];

    const rangeArgs = [
      String(config.iterations),
      String(config.warmup),
      String(fixtures.range.params.m),
      String(fixtures.range.params.n2),
      String(fixtures.range.params.q),
      String(fixtures.range.params.beta),
      String(fixtures.range.gamma),
      String(fixtures.range.k),
      JSON.stringify(fixtures.range.ck),
      JSON.stringify(fixtures.range.commitment),
      JSON.stringify(rangeListed.bits),
      JSON.stringify(rangeListed.comps),
      JSON.stringify(rangeListed.amountAs),
      JSON.stringify(rangeListed.amountZs),
      JSON.stringify(rangeListed.pairAss),
      JSON.stringify(rangeListed.pairZss),
    ];

    if (backends.ocaml) {
      backendsForCase.push(
        normalizeCliBenchmarkResult(
          'ocaml-cli',
          parseCliBenchmark(
            execFileSync(backends.ocaml, ['--json', 'cr-verify-bench', ...rangeArgs], {
              cwd: projectRoot,
              encoding: 'utf8',
              timeout: 120000,
            }).trim()
          )
        )
      );
    }
    if (backends.haskell) {
      backendsForCase.push(
        normalizeCliBenchmarkResult(
          'haskell-cli',
          parseCliBenchmark(
            execFileSync(backends.haskell, ['--json', 'cr-verify-bench', ...rangeArgs], {
              cwd: projectRoot,
              encoding: 'utf8',
              timeout: 120000,
            }).trim()
          )
        )
      );
    }
    results.push({ case: 'range_fs_verify', backends: backendsForCase });
  }

  if (requested.includes('transaction_fs_verify')) {
    const out1Range = listRangeProof(fixtures.tx.proof.out1Range);
    const out2Range = listRangeProof(fixtures.tx.proof.out2Range);
    const in1Nullifier = listNullifierProof(fixtures.tx.proof.in1Nullifier);
    const in2Nullifier = listNullifierProof(fixtures.tx.proof.in2Nullifier);
    const backendsForCase = [
      runJavaScriptBenchmark(config.warmup, config.iterations, () =>
        sdk.ConfidentialTransaction.fsVerify(
          fixtures.tx.params,
          fixtures.tx.gamma,
          fixtures.tx.k,
          fixtures.tx.ck,
          fixtures.tx.nk,
          fixtures.tx.root,
          fixtures.tx.spent,
          fixtures.tx.cIn1,
          fixtures.tx.cIn2,
          fixtures.tx.cOut1,
          fixtures.tx.cOut2,
          fixtures.tx.nf1,
          fixtures.tx.nf2,
          fixtures.tx.proof
        )
      ),
    ];

    const txArgs = [
      String(config.iterations),
      String(config.warmup),
      String(fixtures.tx.params.m),
      String(fixtures.tx.params.n2),
      String(fixtures.tx.params.q),
      String(fixtures.tx.params.beta),
      String(fixtures.tx.gamma),
      String(fixtures.tx.k),
      JSON.stringify(fixtures.tx.ck),
      JSON.stringify(fixtures.tx.nk),
      JSON.stringify(fixtures.tx.ledger),
      JSON.stringify(fixtures.tx.spent),
      JSON.stringify(fixtures.tx.cIn1),
      JSON.stringify(fixtures.tx.cIn2),
      JSON.stringify(fixtures.tx.cOut1),
      JSON.stringify(fixtures.tx.cOut2),
      JSON.stringify(fixtures.tx.nf1),
      JSON.stringify(fixtures.tx.nf2),
      JSON.stringify(in1Nullifier.aCommits),
      JSON.stringify(in1Nullifier.aNullifiers),
      JSON.stringify(in1Nullifier.zMsgs),
      JSON.stringify(in1Nullifier.zRands),
      JSON.stringify(in2Nullifier.aCommits),
      JSON.stringify(in2Nullifier.aNullifiers),
      JSON.stringify(in2Nullifier.zMsgs),
      JSON.stringify(in2Nullifier.zRands),
      JSON.stringify(fixtures.tx.proof.balance.as),
      JSON.stringify(fixtures.tx.proof.balance.zs),
      JSON.stringify(out1Range.bits),
      JSON.stringify(out1Range.comps),
      JSON.stringify(out1Range.amountAs),
      JSON.stringify(out1Range.amountZs),
      JSON.stringify(out1Range.pairAss),
      JSON.stringify(out1Range.pairZss),
      JSON.stringify(out2Range.bits),
      JSON.stringify(out2Range.comps),
      JSON.stringify(out2Range.amountAs),
      JSON.stringify(out2Range.amountZs),
      JSON.stringify(out2Range.pairAss),
      JSON.stringify(out2Range.pairZss),
    ];

    if (backends.ocaml) {
      backendsForCase.push(
        normalizeCliBenchmarkResult(
          'ocaml-cli',
          parseCliBenchmark(
            execFileSync(backends.ocaml, ['--json', 'ct-verify-bench', ...txArgs], {
              cwd: projectRoot,
              encoding: 'utf8',
              timeout: 120000,
            }).trim()
          )
        )
      );
    }
    if (backends.haskell) {
      backendsForCase.push(
        normalizeCliBenchmarkResult(
          'haskell-cli',
          parseCliBenchmark(
            execFileSync(backends.haskell, ['--json', 'ct-verify-bench', ...txArgs], {
              cwd: projectRoot,
              encoding: 'utf8',
              timeout: 120000,
            }).trim()
          )
        )
      );
    }
    results.push({ case: 'transaction_fs_verify', backends: backendsForCase });
  }

  if (config.json) {
    console.log(JSON.stringify({ iterations: config.iterations, warmup: config.warmup, backends, cases: results }, null, 2));
  } else {
    printSummary(results, backends);
  }
}

main().catch((error) => {
  console.error(error instanceof Error ? error.message : String(error));
  process.exit(1);
});
