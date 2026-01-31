#!/usr/bin/env bash
#
# test-ntt-proof.sh - Quick TDD-style test for NTT.thy proofs
#
# Usage:
#   ./scripts/test-ntt-proof.sh          # Test current NTT.thy
#   ./scripts/test-ntt-proof.sh --watch  # Watch mode (not implemented yet)
#

set -e

SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
PROJECT_ROOT="$(dirname "$SCRIPT_DIR")"
TIMEOUT_SECS=15

RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
NC='\033[0m'

cd "$PROJECT_ROOT/Canon"

echo -e "${YELLOW}Testing NTT.thy (${TIMEOUT_SECS}s timeout)...${NC}"
START_TIME=$(date +%s)

# Run isabelle build with timeout
# macOS doesn't have timeout, so we use a background job with kill
isabelle build -v -D . > /tmp/ntt-test-output.log 2>&1 &
BUILD_PID=$!

# Wait for timeout or completion
ELAPSED=0
while kill -0 $BUILD_PID 2>/dev/null; do
    sleep 1
    ELAPSED=$((ELAPSED + 1))
    if [[ $ELAPSED -ge $TIMEOUT_SECS ]]; then
        echo -e "${RED}✗ Build exceeded ${TIMEOUT_SECS}s - likely hanging${NC}"
        kill $BUILD_PID 2>/dev/null
        pkill -P $BUILD_PID 2>/dev/null || true
        # Also kill any poly processes
        pkill -f "poly.*Canon" 2>/dev/null || true
        echo ""
        echo "Last output:"
        tail -10 /tmp/ntt-test-output.log
        exit 1
    fi
done

# Check exit code
wait $BUILD_PID
EXIT_CODE=$?
END_TIME=$(date +%s)
DURATION=$((END_TIME - START_TIME))

if [[ $EXIT_CODE -eq 0 ]]; then
    echo -e "${GREEN}✓ Build passed in ${DURATION}s${NC}"
    exit 0
else
    echo -e "${RED}✗ Build failed in ${DURATION}s${NC}"
    echo ""
    echo "Errors:"
    grep -E "^\*\*\*" /tmp/ntt-test-output.log | head -30
    exit 1
fi
