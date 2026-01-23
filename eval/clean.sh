#!/usr/bin/env bash
#
# clean.sh - Remove generated directories for Isabelle evaluation harness
#
# Cleans up work directories, results, and Isabelle build artifacts.
#
# Usage:
#   ./clean.sh [options]
#
# Options:
#   --work              Clean work/ directory only
#   --results           Clean results/ directory only
#   --all               Clean everything (default)
#   --isabelle-cache    Also clean Isabelle's cache (~/.isabelle)
#   --dry-run           Show what would be deleted without deleting
#   --force             Skip confirmation prompt
#   --verbose           Enable verbose output
#
set -euo pipefail

# Script directory
SCRIPT_DIR="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"

# Default values
CLEAN_WORK=false
CLEAN_RESULTS=false
CLEAN_ISABELLE_CACHE=false
DRY_RUN=false
FORCE=false
VERBOSE=false

# Colors for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m'

log_info() {
    echo -e "${BLUE}[INFO]${NC} $1"
}

log_success() {
    echo -e "${GREEN}[OK]${NC} $1"
}

log_warn() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

log_error() {
    echo -e "${RED}[ERROR]${NC} $1" >&2
}

log_verbose() {
    if [[ "$VERBOSE" == "true" ]]; then
        echo -e "${BLUE}[DEBUG]${NC} $1"
    fi
}

usage() {
    cat <<EOF
Usage: $(basename "$0") [options]

Options:
  --work              Clean work/ directory only
  --results           Clean results/ directory only
  --all               Clean everything (default if no option specified)
  --isabelle-cache    Also clean Isabelle's build cache
  --dry-run           Show what would be deleted without deleting
  --force             Skip confirmation prompt
  --verbose           Enable verbose output
  -h, --help          Show this help message

Examples:
  $(basename "$0")                    # Clean work/ and results/
  $(basename "$0") --work --dry-run   # Show what would be cleaned in work/
  $(basename "$0") --all --force      # Clean everything without prompting
EOF
    exit 1
}

# Function to get directory size
get_dir_size() {
    local dir="$1"
    if [[ -d "$dir" ]]; then
        du -sh "$dir" 2>/dev/null | cut -f1 || echo "0"
    else
        echo "0"
    fi
}

# Function to count files
count_files() {
    local dir="$1"
    if [[ -d "$dir" ]]; then
        find "$dir" -type f 2>/dev/null | wc -l | tr -d ' '
    else
        echo "0"
    fi
}

# Function to safely remove directory
safe_remove() {
    local dir="$1"
    local desc="$2"

    if [[ ! -d "$dir" ]]; then
        log_verbose "${desc} not found: ${dir}"
        return 0
    fi

    local size=$(get_dir_size "$dir")
    local file_count=$(count_files "$dir")

    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY-RUN] Would remove ${desc}: ${dir}"
        log_info "          Size: ${size}, Files: ${file_count}"
    else
        log_info "Removing ${desc}: ${dir} (${size}, ${file_count} files)"
        rm -rf "$dir"
        log_success "Removed ${desc}"
    fi
}

# Parse command line arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --work)
            CLEAN_WORK=true
            shift
            ;;
        --results)
            CLEAN_RESULTS=true
            shift
            ;;
        --all)
            CLEAN_WORK=true
            CLEAN_RESULTS=true
            shift
            ;;
        --isabelle-cache)
            CLEAN_ISABELLE_CACHE=true
            shift
            ;;
        --dry-run)
            DRY_RUN=true
            shift
            ;;
        --force)
            FORCE=true
            shift
            ;;
        --verbose)
            VERBOSE=true
            shift
            ;;
        -h|--help)
            usage
            ;;
        *)
            log_error "Unknown option: $1"
            usage
            ;;
    esac
done

# Default to cleaning everything if no specific option given
if [[ "$CLEAN_WORK" == "false" ]] && [[ "$CLEAN_RESULTS" == "false" ]]; then
    CLEAN_WORK=true
    CLEAN_RESULTS=true
fi

# Directories to clean
WORK_DIR="${SCRIPT_DIR}/work"
RESULTS_DIR="${SCRIPT_DIR}/results"
ISABELLE_CACHE="${HOME}/.isabelle"

# Show what will be cleaned
log_info "Isabelle Evaluation Cleanup"
echo ""

TOTAL_SIZE=0
DIRS_TO_CLEAN=()

if [[ "$CLEAN_WORK" == "true" ]] && [[ -d "$WORK_DIR" ]]; then
    DIRS_TO_CLEAN+=("$WORK_DIR")
    log_info "work/:    $(get_dir_size "$WORK_DIR") ($(count_files "$WORK_DIR") files)"
fi

if [[ "$CLEAN_RESULTS" == "true" ]] && [[ -d "$RESULTS_DIR" ]]; then
    DIRS_TO_CLEAN+=("$RESULTS_DIR")
    log_info "results/: $(get_dir_size "$RESULTS_DIR") ($(count_files "$RESULTS_DIR") files)"
fi

if [[ "$CLEAN_ISABELLE_CACHE" == "true" ]] && [[ -d "$ISABELLE_CACHE" ]]; then
    log_warn "Isabelle cache: $(get_dir_size "$ISABELLE_CACHE")"
    log_warn "This may take a long time to rebuild!"
fi

echo ""

if [[ ${#DIRS_TO_CLEAN[@]} -eq 0 ]] && [[ "$CLEAN_ISABELLE_CACHE" == "false" ]]; then
    log_info "Nothing to clean"
    exit 0
fi

# Confirmation prompt
if [[ "$FORCE" == "false" ]] && [[ "$DRY_RUN" == "false" ]]; then
    echo -n "Are you sure you want to delete these directories? [y/N] "
    read -r response
    if [[ ! "$response" =~ ^[Yy]$ ]]; then
        log_info "Cancelled"
        exit 0
    fi
fi

# Perform cleanup
if [[ "$CLEAN_WORK" == "true" ]]; then
    safe_remove "$WORK_DIR" "work directory"
    # Recreate empty directory
    if [[ "$DRY_RUN" == "false" ]]; then
        mkdir -p "$WORK_DIR"
        log_verbose "Recreated empty work directory"
    fi
fi

if [[ "$CLEAN_RESULTS" == "true" ]]; then
    safe_remove "$RESULTS_DIR" "results directory"
    # Recreate empty directory
    if [[ "$DRY_RUN" == "false" ]]; then
        mkdir -p "$RESULTS_DIR"
        log_verbose "Recreated empty results directory"
    fi
fi

if [[ "$CLEAN_ISABELLE_CACHE" == "true" ]]; then
    if [[ "$DRY_RUN" == "true" ]]; then
        log_info "[DRY-RUN] Would clean Isabelle build cache"
    else
        # Only clean build artifacts, not user settings
        HEAPS_DIR="${ISABELLE_CACHE}/heaps"
        BROWSER_INFO="${ISABELLE_CACHE}/browser_info"

        if [[ -d "$HEAPS_DIR" ]]; then
            safe_remove "$HEAPS_DIR" "Isabelle heap images"
        fi

        if [[ -d "$BROWSER_INFO" ]]; then
            safe_remove "$BROWSER_INFO" "Isabelle browser info"
        fi

        log_success "Cleaned Isabelle build cache"
    fi
fi

# Summary
echo ""
if [[ "$DRY_RUN" == "true" ]]; then
    log_info "Dry run complete - no files were deleted"
else
    log_success "Cleanup complete"
fi

exit 0
