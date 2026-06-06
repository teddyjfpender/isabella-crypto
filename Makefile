# Isabella - Formally Verified Lattice Cryptography
# Makefile for building and testing libraries

.PHONY: all canon haskell ocaml typescript clean test examples help \
        test-validation test-vectors check-formalization \
        build-cool build-balanced build-fast build-export \
        test-sdk-equivalence test-confidential-production \
        check-confidential-domain-registry \
        check-confidential-parameter-readiness \
        check-confidential-production-readiness \
        run-confidential-lattice-estimator \
        bench-typescript-confidential bench-confidential-verify \
        bench-confidential-realistic

# Default target: low-heat Canon build profile
.DEFAULT_GOAL := build-cool

ISABELLE ?= isabelle
CANON_DIR ?= Canon
CANON_SESSIONS ?= Canon_Rings Canon_Crypto Canon_ZK
CANON_EXPORT_SESSION ?= Canon_Crypto_Export
NICE ?= nice -n 10
CONFIDENTIAL_ESTIMATOR_REPORT_OUT ?= /tmp/confidential-lattice-estimator-reports.json

# Isabelle build profiles
ISABELLE_COOL_OPTS ?= -j1 -o threads=2 -o parallel_limit=2 -o parallel_proofs=0
ISABELLE_BALANCED_OPTS ?= -j2 -o threads=3 -o parallel_limit=3 -o parallel_proofs=1
ISABELLE_FAST_OPTS ?= -j4 -o threads=0 -o parallel_proofs=1

# Full pipeline target
all: canon haskell ocaml typescript

# Build Canon Isabelle theories
canon: build-cool

build-cool:
	@echo "Building Canon Isabelle theories (cool profile: lower CPU/heat)..."
	@$(NICE) $(ISABELLE) build -d $(CANON_DIR) -b $(ISABELLE_COOL_OPTS) $(CANON_SESSIONS)
	@echo "Canon build-cool completed"

build-balanced:
	@echo "Building Canon Isabelle theories (balanced profile)..."
	@$(ISABELLE) build -d $(CANON_DIR) -b $(ISABELLE_BALANCED_OPTS) $(CANON_SESSIONS)
	@echo "Canon build-balanced completed"

build-fast:
	@echo "Building Canon Isabelle theories (fast profile: higher CPU usage)..."
	@$(ISABELLE) build -d $(CANON_DIR) -b $(ISABELLE_FAST_OPTS) $(CANON_SESSIONS)
	@echo "Canon build-fast completed"

build-export:
	@echo "Building optional code-export session..."
	@$(ISABELLE) build -d $(CANON_DIR) -b -j1 $(CANON_EXPORT_SESSION)
	@echo "Canon export session built"

# Check formal proof hygiene (no sorry/oops/admit in Canon theories)
check-formalization:
	@./scripts/check_formalization.sh

# Build Haskell library
haskell:
	@echo "Building Haskell library..."
	@cd isabella.hs && cabal build
	@echo "Haskell library built successfully"

# Build OCaml library
ocaml:
	@echo "Building OCaml library..."
	@cd isabella.ml && eval $$(opam env) && dune build
	@echo "OCaml library built successfully"

# Build TypeScript library (requires OCaml/js_of_ocaml)
typescript: ocaml
	@echo "Building TypeScript library..."
	@mkdir -p isabella.ts/dist
	@cd isabella.ml && eval $$(opam env) && dune build src/js/isabella_js.bc.js
	@rm -f isabella.ts/dist/isabella.js isabella.ts/dist/isabella.cjs isabella.ts/dist/index.mjs
	@cp isabella.ml/_build/default/src/js/isabella_js.bc.js isabella.ts/dist/isabella.js
	@cp isabella.ml/_build/default/src/js/isabella_js.bc.js isabella.ts/dist/isabella.cjs
	@cp isabella.ts/src/runtime.cjs isabella.ts/dist/runtime.cjs
	@cd isabella.ts && npm ci
	@cd isabella.ts && npx tsc
	@cd isabella.ts && node ./scripts/write-esm-wrapper.mjs
	@echo "TypeScript library built successfully"

# Run all tests
test: check-formalization test-haskell test-ocaml test-typescript test-validation

test-haskell:
	@echo "Running Haskell tests..."
	@cd isabella.hs && cabal test

test-ocaml:
	@echo "Running OCaml tests..."
	@cd isabella.ml && eval $$(opam env) && dune test

test-typescript:
	@echo "Running TypeScript tests..."
	@cd isabella.ts && node --test examples/test.mjs

# Cross-validation tests against noble-post-quantum
test-validation:
	@echo "Running cross-validation tests..."
	@cd tests && bun test

test-sdk-equivalence:
	@echo "Running cross-SDK equivalence harnesses..."
	@cd tests && bun run validate-sdks

check-confidential-domain-registry:
	@echo "Checking confidential domain-separation registry..."
	@python3 scripts/check_confidential_domain_registry.py

check-confidential-parameter-readiness:
	@echo "Screening confidential transfer parameters..."
	@python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json
	@echo "Checking confidential parameter readiness honesty gate..."
	@python3 scripts/check_confidential_parameter_readiness.py --report bench/data/confidential-parameter-screen.json
	@echo "Checking confidential parameter readiness negative regressions..."
	@python3 scripts/check_confidential_parameter_readiness_regressions.py

run-confidential-lattice-estimator:
	@echo "Screening confidential transfer parameters..."
	@python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json
	@echo "Running confidential lattice-estimator report generator..."
	@python3 scripts/run_confidential_lattice_estimator.py \
		--parameter-screen bench/data/confidential-parameter-screen.json \
		--out $(CONFIDENTIAL_ESTIMATOR_REPORT_OUT)
	@echo "Wrote $(CONFIDENTIAL_ESTIMATOR_REPORT_OUT)"

check-confidential-production-readiness:
	@echo "Screening confidential transfer parameters..."
	@python3 scripts/confidential_parameter_screen.py --out bench/data/confidential-parameter-screen.json
	@git diff --exit-code -- bench/data/confidential-parameter-screen.json
	@echo "Checking strict confidential production-readiness gate..."
	@python3 scripts/check_confidential_parameter_readiness.py --report bench/data/confidential-parameter-screen.json --require-production

test-confidential-production: check-formalization build-cool ocaml haskell typescript
	@echo "Generating confidential transcript vectors..."
	@node scripts/generate_confidential_transcript_vectors.mjs
	@echo "Generating confidential Merkle vectors..."
	@node scripts/generate_confidential_merkle_vectors.mjs
	@echo "Generating confidential transaction context vectors..."
	@node scripts/generate_confidential_transaction_vectors.mjs
	@$(MAKE) check-confidential-domain-registry
	@$(MAKE) check-confidential-parameter-readiness
	@echo "Checking confidential scaffold quarantine..."
	@python3 scripts/check_confidential_scaffold_quarantine.py
	@echo "Running confidential transcript vector tests..."
	@cd tests && bun test confidential-transcript
	@echo "Running confidential CSPRNG sampling tests..."
	@cd tests && bun test confidential-sampling
	@echo "Running confidential Merkle vector tests..."
	@cd tests && bun test confidential-merkle
	@echo "Running confidential transaction context vector tests..."
	@cd tests && bun test confidential-transaction
	@echo "Running confidential transaction audit..."
	@cd tests && bun run audit-confidential
	@$(MAKE) test-sdk-equivalence
	@node scripts/bench_confidential_balance_128.mjs
	@node scripts/bench_confidential_balance_realistic.mjs
	@node scripts/check_confidential_bench_budgets.mjs

bench-typescript-confidential: typescript
	@echo "Running deterministic TypeScript confidential proof benchmarks..."
	@node bench/typescript-confidential-proving-bench.mjs

bench-confidential-verify: typescript
	@echo "Running deterministic confidential verifier comparison benchmarks..."
	@node bench/confidential-verifier-compare.mjs

bench-confidential-realistic: typescript
	@echo "Running realistic-dimension confidential balance benchmark..."
	@node scripts/bench_confidential_balance_realistic.mjs

# Generate test vectors from noble-post-quantum
test-vectors:
	@echo "Generating test vectors..."
	@cd tests && bun run generate-vectors

# Run examples
examples: examples-haskell examples-ocaml examples-typescript

examples-haskell:
	@echo "Running Haskell examples..."
	@echo "============================="
	@cd isabella.hs && cabal run isabella-cli -- examples

examples-ocaml:
	@echo ""
	@echo "Running OCaml examples..."
	@echo "========================="
	@cd isabella.ml && eval $$(opam env) && dune exec isabella_cli -- examples

examples-typescript:
	@echo ""
	@echo "Running TypeScript examples..."
	@echo "=============================="
	@cd isabella.ts && node examples/example.mjs

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	@rm -rf isabella.hs/dist-newstyle
	@rm -rf isabella.ml/_build
	@rm -rf isabella.ts/dist/*.js isabella.ts/dist/*.mjs isabella.ts/dist/*.d.ts isabella.ts/dist/*.map isabella.ts/dist/*.cjs
	@echo "Cleaned"

# Generate code from Isabelle (full pipeline)
generate:
	@./generate.sh

generate-build:
	@./generate.sh --build-only

generate-examples:
	@./generate.sh --run-examples

# Help
help:
	@echo "Isabella Makefile"
	@echo ""
	@echo "Targets:"
	@echo "  build-cool          Build Canon (default, low-heat settings)"
	@echo "  build-balanced      Build Canon with moderate parallelism"
	@echo "  build-fast          Build Canon with high parallelism"
	@echo "  build-export        Build optional Canon export session ($(CANON_EXPORT_SESSION))"
	@echo "  all                 Build Canon + all libraries"
	@echo "  canon               Alias for build-cool"
	@echo "  check-formalization Check Canon has no sorry/oops/admit"
	@echo "  haskell             Build Haskell library"
	@echo "  ocaml               Build OCaml library"
	@echo "  typescript          Build TypeScript library (via js_of_ocaml)"
	@echo "  test                Run all tests (including validation)"
	@echo "  test-haskell        Run Haskell tests"
	@echo "  test-ocaml          Run OCaml tests"
	@echo "  test-typescript     Run TypeScript tests"
	@echo "  test-validation     Run cross-validation tests vs noble-post-quantum"
	@echo "  test-sdk-equivalence Run Haskell/OCaml/TypeScript shared-surface checks"
	@echo "  test-confidential-production Run production-facing confidential-transfer gates"
	@echo "  check-confidential-domain-registry Check confidential domain/tag registry"
	@echo "  check-confidential-parameter-readiness Run soft confidential parameter honesty gate"
	@echo "  check-confidential-production-readiness Run strict launch parameter gate"
	@echo "  run-confidential-lattice-estimator Generate external lattice-estimator report collection"
	@echo "  bench-typescript-confidential Benchmark TypeScript confidential proof APIs"
	@echo "  bench-confidential-verify   Compare JS and native confidential verifier hot paths"
	@echo "  bench-confidential-realistic Benchmark 1024-dimensional confidential balance proof"
	@echo "  test-vectors        Generate test vectors from noble-post-quantum"
	@echo "  examples            Run examples in all languages"
	@echo "  examples-haskell    Run Haskell examples"
	@echo "  examples-ocaml      Run OCaml examples"
	@echo "  examples-typescript Run TypeScript examples"
	@echo "  clean               Clean build artifacts"
	@echo "  generate            Generate code from Isabelle"
	@echo "  help                Show this help"
