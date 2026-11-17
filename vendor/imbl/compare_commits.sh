#!/bin/bash
set -e

# Benchmark comparison script
# Compares two commits using criterion benchmarks

BASELINE_COMMIT="1c8f62a88b776e192a9c5df5fb919bb396d71783"
NEW_COMMIT="3502f2949ef7b5d56340070f71f3a48e6da4ba7f"

# CPU core for taskset (for consistent benchmarking)
CPU_CORE=0

# Color codes for output
RED='\033[0;31m'
GREEN='\033[0;32m'
YELLOW='\033[1;33m'
BLUE='\033[0;34m'
NC='\033[0m' # No Color

# Quick mode flag
QUICK_MODE=false

# Parse arguments
while [[ $# -gt 0 ]]; do
    case $1 in
        --quick|-q)
            QUICK_MODE=true
            shift
            ;;
        --baseline)
            BASELINE_COMMIT="$2"
            shift 2
            ;;
        --new)
            NEW_COMMIT="$2"
            shift 2
            ;;
        --cpu)
            CPU_CORE="$2"
            shift 2
            ;;
        --help|-h)
            echo "Usage: $0 [OPTIONS]"
            echo ""
            echo "Options:"
            echo "  --quick, -q          Run in quick mode (shorter benchmarks for validation)"
            echo "  --baseline COMMIT    Baseline commit (default: 1c8f62a)"
            echo "  --new COMMIT         New commit (default: 3502f29)"
            echo "  --cpu CORE           CPU core for taskset (default: 1)"
            echo "  --help, -h           Show this help message"
            echo ""
            echo "Example:"
            echo "  $0 --quick          # Quick validation run"
            echo "  $0                  # Full benchmark comparison"
            exit 0
            ;;
        *)
            echo "Unknown option: $1"
            echo "Use --help for usage information"
            exit 1
            ;;
    esac
done

# Function to print colored output
print_header() {
    echo -e "${BLUE}========================================${NC}"
    echo -e "${BLUE}$1${NC}"
    echo -e "${BLUE}========================================${NC}"
}

print_info() {
    echo -e "${GREEN}[INFO]${NC} $1"
}

print_warning() {
    echo -e "${YELLOW}[WARN]${NC} $1"
}

print_error() {
    echo -e "${RED}[ERROR]${NC} $1"
}

# Save current branch/commit
ORIGINAL_HEAD=$(git rev-parse HEAD)
ORIGINAL_BRANCH=$(git branch --show-current)

print_header "Benchmark Comparison Setup"
echo "Baseline: $BASELINE_COMMIT"
echo "New:      $NEW_COMMIT"
echo "CPU Core: $CPU_CORE"
echo "Mode:     $([ "$QUICK_MODE" = true ] && echo "QUICK" || echo "FULL")"
echo ""

# Check if commits exist
if ! git rev-parse "$BASELINE_COMMIT" >/dev/null 2>&1; then
    print_error "Baseline commit $BASELINE_COMMIT not found"
    exit 1
fi

if ! git rev-parse "$NEW_COMMIT" >/dev/null 2>&1; then
    print_error "New commit $NEW_COMMIT not found"
    exit 1
fi

# Function to restore original state
cleanup() {
    print_info "Restoring original state..."
    if [ -n "$ORIGINAL_BRANCH" ]; then
        git checkout "$ORIGINAL_BRANCH" 2>/dev/null || git checkout "$ORIGINAL_HEAD" 2>/dev/null
    else
        git checkout "$ORIGINAL_HEAD" 2>/dev/null
    fi
}

trap cleanup EXIT

# Benchmark filter for quick vs full mode
if [ "$QUICK_MODE" = true ]; then
    # Quick mode: only small benchmarks
    BENCH_FILTER="--quick"
    WARM_UP_TIME=1
    MEASUREMENT_TIME=1
    print_info "Quick mode: Running subset of benchmarks with reduced timing"
else
    # Full mode: all important benchmarks
    BENCH_FILTER=""
    WARM_UP_TIME=1
    MEASUREMENT_TIME=6
    print_info "Full mode: Running comprehensive benchmarks"
fi

# Create output directory
OUTPUT_DIR="benchmark_results_$(date +%Y%m%d_%H%M%S)"
mkdir -p "$OUTPUT_DIR"

print_info "Results will be saved to: $OUTPUT_DIR"

# Function to run benchmarks for a commit
run_benchmark() {
    local commit=$1
    local name=$2
    local output_file=$3

    print_header "Building and Benchmarking: $name ($commit)"

    # Checkout commit
    print_info "Checking out $commit..."
    git checkout "$commit" -q

    # Build benchmarks
    print_info "Building benchmarks..."
    cargo bench --bench hashmap --no-run

    # Run benchmarks
    print_info "Running benchmarks (this may take a while)..."
    taskset -c "$CPU_CORE" cargo bench --bench hashmap -- "$BENCH_FILTER" \
        --warm-up-time "$WARM_UP_TIME" \
        --measurement-time "$MEASUREMENT_TIME" \
        --noplot \
        | tee "$output_file"

    print_info "Benchmark complete for $name"
    echo ""
}

# Run baseline benchmarks
run_benchmark "$BASELINE_COMMIT" "BASELINE" "$OUTPUT_DIR/baseline.txt"

# Run new benchmarks
run_benchmark "$NEW_COMMIT" "NEW" "$OUTPUT_DIR/new.txt"
