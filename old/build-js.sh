#!/usr/bin/env bash
#
# build-js.sh - Build JavaScript/TypeScript from verified OCaml code
#
# This script compiles the Isabelle-generated OCaml code to JavaScript
# using js_of_ocaml, then creates TypeScript type definitions.
#
# Usage:
#   ./build-js.sh [--setup] [--clean]
#
# Options:
#   --setup    Install OCaml toolchain and dependencies (first time only)
#   --clean    Remove build artifacts before building
#
set -euo pipefail

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
OCAML_DIR="${SCRIPT_DIR}/ocaml/isabella"
JS_OUTPUT_DIR="${SCRIPT_DIR}/javascript/isabella"
TS_OUTPUT_DIR="${SCRIPT_DIR}/typescript/isabella"

# Colors
GREEN='\033[0;32m'
BLUE='\033[0;34m'
YELLOW='\033[1;33m'
RED='\033[0;31m'
NC='\033[0m'

log_info() { echo -e "${BLUE}[INFO]${NC} $1"; }
log_success() { echo -e "${GREEN}[OK]${NC} $1"; }
log_warn() { echo -e "${YELLOW}[WARN]${NC} $1"; }
log_error() { echo -e "${RED}[ERROR]${NC} $1"; }

SETUP=false
CLEAN=false

while [[ $# -gt 0 ]]; do
    case $1 in
        --setup) SETUP=true; shift ;;
        --clean) CLEAN=true; shift ;;
        *) log_error "Unknown option: $1"; exit 1 ;;
    esac
done

# Check for required tools
check_tools() {
    local missing=()

    if ! command -v opam &> /dev/null; then
        missing+=("opam")
    fi

    if [[ ${#missing[@]} -gt 0 ]]; then
        log_error "Missing required tools: ${missing[*]}"
        log_info "Run: brew install ${missing[*]}"
        log_info "Then run: ./build-js.sh --setup"
        exit 1
    fi
}

# Setup OCaml environment
setup_ocaml() {
    log_info "Setting up OCaml environment..."

    # Initialize opam if needed
    if [[ ! -d ~/.opam ]]; then
        log_info "Initializing opam..."
        opam init -y --bare
    fi

    # Create or update switch
    if ! opam switch show 2>/dev/null | grep -q "isabella"; then
        log_info "Creating opam switch 'isabella'..."
        opam switch create isabella 4.14.1 -y
    fi

    eval $(opam env --switch=isabella)

    # Install dependencies
    log_info "Installing OCaml dependencies..."
    opam install -y dune zarith zarith_stubs_js js_of_ocaml js_of_ocaml-ppx

    log_success "OCaml environment ready"
}

# Build JavaScript
build_js() {
    log_info "Building JavaScript..."

    # Ensure opam environment is loaded
    if command -v opam &> /dev/null; then
        eval $(opam env --switch=isabella 2>/dev/null || opam env)
    fi

    cd "$OCAML_DIR"

    if [[ "$CLEAN" == "true" ]]; then
        log_info "Cleaning build artifacts..."
        dune clean
    fi

    # Build with js_of_ocaml
    dune build src/js/isabella_js.bc.js

    # Copy output (dune generates read-only files, so make writable first)
    mkdir -p "$JS_OUTPUT_DIR/dist"
    chmod u+w "$JS_OUTPUT_DIR/dist/isabella.js" 2>/dev/null || true
    cp _build/default/src/js/isabella_js.bc.js "$JS_OUTPUT_DIR/dist/isabella.js"

    log_success "JavaScript built: javascript/isabella/dist/isabella.js"
}

# Create TypeScript definitions
create_typescript() {
    log_info "Creating TypeScript definitions..."

    mkdir -p "$TS_OUTPUT_DIR/src"

    cat > "$TS_OUTPUT_DIR/src/index.ts" << 'EOF'
/**
 * Isabella - Verified Lattice Cryptography
 *
 * TypeScript bindings for formally verified lattice-based cryptography.
 * The underlying implementation is extracted from Isabelle/HOL proofs
 * and compiled to JavaScript via js_of_ocaml.
 */

// Load the compiled OCaml runtime
import './isabella.js';

declare global {
  const Isabella: IsabellaModule;
}

/** Integer vector (arbitrary precision) */
export type IntVec = number[];

/** Integer matrix (list of rows) */
export type IntMatrix = number[][];

/** LWE ciphertext */
export interface LweCiphertext {
  u: IntVec;
  v: number;
}

/** Isabella lattice cryptography module */
export interface IsabellaModule {
  /** Vector addition: xs + ys (component-wise) */
  vecAdd(xs: IntVec, ys: IntVec): IntVec;

  /** Vector modular reduction: each x_i mod q */
  vecMod(v: IntVec, q: number): IntVec;

  /** Inner product (dot product): sum(x_i * y_i) */
  innerProd(xs: IntVec, ys: IntVec): number;

  /** Matrix-vector multiplication: A * x */
  matVecMult(mat: IntMatrix, vec: IntVec): IntVec;

  /** Matrix transpose */
  transpose(mat: IntMatrix): IntMatrix;

  /** Encode a bit for LWE: false -> 0, true -> q/2 */
  encodeBit(q: number, bit: boolean): number;

  /** Decode a bit from LWE: < q/2 -> false, >= q/2 -> true */
  decodeBit(q: number, d: number): boolean;

  /**
   * LWE encryption (Regev scheme)
   * @param pkA - Public key matrix A (N x n)
   * @param pkB - Public key vector b = A*s + e (length N)
   * @param q - Modulus
   * @param r - Random binary vector (length N)
   * @param m - Message bit to encrypt
   * @returns Ciphertext {u, v}
   */
  lweEncrypt(pkA: IntMatrix, pkB: IntVec, q: number, r: IntVec, m: boolean): LweCiphertext;

  /**
   * LWE decryption (Regev scheme)
   * @param skS - Secret key vector s (length n)
   * @param q - Modulus
   * @param ctU - Ciphertext u component
   * @param ctV - Ciphertext v component
   * @returns Decrypted bit
   */
  lweDecrypt(skS: IntVec, q: number, ctU: IntVec, ctV: number): boolean;
}

// Re-export the global Isabella object with types
export const Lattice: IsabellaModule = (globalThis as any).Isabella;

// Convenience wrapper class
export class LweRegev {
  constructor(
    private readonly q: number,
    private readonly pkA: IntMatrix,
    private readonly pkB: IntVec,
    private readonly skS?: IntVec
  ) {}

  /** Encrypt a single bit */
  encrypt(message: boolean, randomVector: IntVec): LweCiphertext {
    return Lattice.lweEncrypt(this.pkA, this.pkB, this.q, randomVector, message);
  }

  /** Decrypt a ciphertext (requires secret key) */
  decrypt(ciphertext: LweCiphertext): boolean {
    if (!this.skS) {
      throw new Error('Secret key not available for decryption');
    }
    return Lattice.lweDecrypt(this.skS, this.q, ciphertext.u, ciphertext.v);
  }

  /** Get the modulus */
  get modulus(): number {
    return this.q;
  }
}
EOF

    # Create package.json for TypeScript
    cat > "$TS_OUTPUT_DIR/package.json" << 'EOF'
{
  "name": "@isabella/lattice-crypto",
  "version": "0.1.0",
  "description": "Verified lattice cryptography from Isabelle/HOL",
  "main": "dist/index.js",
  "types": "dist/index.d.ts",
  "files": [
    "dist",
    "src"
  ],
  "scripts": {
    "build": "tsc",
    "prepare": "npm run build"
  },
  "keywords": [
    "cryptography",
    "lattice",
    "lwe",
    "post-quantum",
    "verified",
    "isabelle"
  ],
  "license": "MIT",
  "devDependencies": {
    "typescript": "^5.0.0"
  }
}
EOF

    # Create tsconfig.json
    cat > "$TS_OUTPUT_DIR/tsconfig.json" << 'EOF'
{
  "compilerOptions": {
    "target": "ES2020",
    "module": "ESNext",
    "moduleResolution": "node",
    "declaration": true,
    "declarationMap": true,
    "sourceMap": true,
    "outDir": "./dist",
    "rootDir": "./src",
    "strict": true,
    "esModuleInterop": true,
    "skipLibCheck": true,
    "forceConsistentCasingInFileNames": true
  },
  "include": ["src/**/*"],
  "exclude": ["node_modules", "dist"]
}
EOF

    # Copy the JS runtime
    mkdir -p "$TS_OUTPUT_DIR/src"
    if [[ -f "$JS_OUTPUT_DIR/dist/isabella.js" ]]; then
        chmod u+w "$TS_OUTPUT_DIR/src/isabella.js" 2>/dev/null || true
        cp "$JS_OUTPUT_DIR/dist/isabella.js" "$TS_OUTPUT_DIR/src/isabella.js"
    fi

    log_success "TypeScript definitions created: typescript/isabella/"
}

# Main
echo ""
echo -e "${GREEN}Isabella - Building JavaScript/TypeScript${NC}"
echo "==========================================="
echo ""

if [[ "$SETUP" == "true" ]]; then
    check_tools
    setup_ocaml
fi

# Check if OCaml files exist
if [[ ! -f "$OCAML_DIR/src/lattice/lwe_regev.ml" ]]; then
    log_error "No OCaml source files found"
    log_info "Run './collect.sh --lang ocaml' first to collect generated code"
    exit 1
fi

# Check if opam/dune are available
if ! command -v opam &> /dev/null; then
    log_error "opam not found"
    log_info "Install with: brew install opam"
    log_info "Then run: ./build-js.sh --setup"
    exit 1
fi

build_js
create_typescript

echo ""
log_success "Build complete!"
echo ""
echo "Output:"
echo "  JavaScript: javascript/isabella/dist/isabella.js"
echo "  TypeScript: typescript/isabella/src/index.ts"
echo ""
echo "To use in a project:"
echo "  cd typescript/isabella && npm install && npm run build"
echo ""
