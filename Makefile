# Isabella - Formally Verified Lattice Cryptography
# Makefile for building and testing libraries

.PHONY: all canon haskell ocaml typescript clean test examples help \
        test-validation test-vectors check-formalization

# Default target
all: canon haskell ocaml typescript

# Build Canon Isabelle theories
canon:
	@echo "Building Canon Isabelle theories..."
	@cd Canon && isabelle build -D .
	@echo "Canon built successfully"

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
	@rm -f isabella.ts/dist/isabella.js
	@cp isabella.ml/_build/default/src/js/isabella_js.bc.js isabella.ts/dist/isabella.js
	@cp isabella.ts/src/runtime.cjs isabella.ts/dist/runtime.cjs
	@cd isabella.ts && npx tsc
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
	@rm -rf isabella.ts/dist/*.js isabella.ts/dist/*.d.ts isabella.ts/dist/*.map isabella.ts/dist/*.cjs
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
	@echo "  all                 Build Canon + all libraries (default)"
	@echo "  canon               Build Canon Isabelle theories"
	@echo "  check-formalization Check Canon has no sorry/oops/admit"
	@echo "  haskell             Build Haskell library"
	@echo "  ocaml               Build OCaml library"
	@echo "  typescript          Build TypeScript library (via js_of_ocaml)"
	@echo "  test                Run all tests (including validation)"
	@echo "  test-haskell        Run Haskell tests"
	@echo "  test-ocaml          Run OCaml tests"
	@echo "  test-typescript     Run TypeScript tests"
	@echo "  test-validation     Run cross-validation tests vs noble-post-quantum"
	@echo "  test-vectors        Generate test vectors from noble-post-quantum"
	@echo "  examples            Run examples in all languages"
	@echo "  examples-haskell    Run Haskell examples"
	@echo "  examples-ocaml      Run OCaml examples"
	@echo "  examples-typescript Run TypeScript examples"
	@echo "  clean               Clean build artifacts"
	@echo "  generate            Generate code from Isabelle"
	@echo "  help                Show this help"
