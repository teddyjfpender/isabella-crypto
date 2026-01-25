# Isabella - Formally Verified Lattice Cryptography
# Makefile for building and testing libraries

.PHONY: all canon haskell ocaml clean test examples help

# Default target
all: canon haskell ocaml

# Build Canon Isabelle theories
canon:
	@echo "Building Canon Isabelle theories..."
	@cd Canon && isabelle build -D .
	@echo "Canon built successfully"

# Build Haskell library
haskell:
	@echo "Building Haskell library..."
	@cd isabella.hs && cabal build
	@echo "Haskell library built successfully"

# Build OCaml library
ocaml:
	@echo "Building OCaml library..."
	@cd isabella.ml && dune build
	@echo "OCaml library built successfully"

# Run all tests
test: test-haskell test-ocaml

test-haskell:
	@echo "Running Haskell tests..."
	@cd isabella.hs && cabal test

test-ocaml:
	@echo "Running OCaml tests..."
	@cd isabella.ml && dune test

# Run examples
examples: examples-haskell examples-ocaml

examples-haskell:
	@echo "Running Haskell examples..."
	@echo "============================="
	@cd isabella.hs && cabal run isabella-cli -- examples

examples-ocaml:
	@echo ""
	@echo "Running OCaml examples..."
	@echo "========================="
	@cd isabella.ml && dune exec isabella_cli -- examples

# Clean build artifacts
clean:
	@echo "Cleaning build artifacts..."
	@rm -rf isabella.hs/dist-newstyle
	@rm -rf isabella.ml/_build
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
	@echo "  all              Build Canon, Haskell, and OCaml (default)"
	@echo "  canon            Build Canon Isabelle theories"
	@echo "  haskell          Build Haskell library"
	@echo "  ocaml            Build OCaml library"
	@echo "  test             Run all tests"
	@echo "  test-haskell     Run Haskell tests"
	@echo "  test-ocaml       Run OCaml tests"
	@echo "  examples         Run examples in both languages"
	@echo "  examples-haskell Run Haskell examples"
	@echo "  examples-ocaml   Run OCaml examples"
	@echo "  clean            Clean build artifacts"
	@echo "  generate         Generate code from Isabelle"
	@echo "  help             Show this help"
