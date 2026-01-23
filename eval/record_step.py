#!/usr/bin/env python3
"""
Record individual verification step to JSONL file.

Each invocation appends a single step record to steps.jsonl,
enabling incremental progress tracking during evaluation runs.
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


def read_file_content(path: Optional[Path], max_lines: int = 1000) -> Optional[str]:
    """Read file content, truncating if too long."""
    if path is None or not path.exists():
        return None

    try:
        content = path.read_text(encoding='utf-8', errors='replace')
        lines = content.split('\n')
        if len(lines) > max_lines:
            content = '\n'.join(lines[:max_lines])
            content += f'\n... (truncated, {len(lines) - max_lines} more lines)'
        return content
    except Exception as e:
        return f"Error reading file: {e}"


def record_step(
    out_dir: Path,
    step_name: str,
    status: str,
    exit_code: int,
    stdout_path: Optional[Path] = None,
    stderr_path: Optional[Path] = None,
    duration_ms: Optional[int] = None,
    metadata: Optional[dict] = None
) -> Path:
    """
    Record a verification step to steps.jsonl.

    Args:
        out_dir: Output directory for steps.jsonl
        step_name: Name of the step (e.g., 'isabelle_build', 'haskell_compile')
        status: Step status ('pass', 'fail', 'skip', 'error')
        exit_code: Process exit code
        stdout_path: Path to stdout file (optional)
        stderr_path: Path to stderr file (optional)
        duration_ms: Step duration in milliseconds (optional)
        metadata: Additional metadata dict (optional)

    Returns:
        Path to the steps.jsonl file
    """
    out_dir.mkdir(parents=True, exist_ok=True)
    steps_path = out_dir / 'steps.jsonl'

    # Build step record
    step = {
        'step': step_name,
        'status': status,
        'exit_code': exit_code,
        'timestamp': datetime.now(timezone.utc).isoformat(),
    }

    if duration_ms is not None:
        step['duration_ms'] = duration_ms

    # Include stdout/stderr content if available
    if stdout_path:
        stdout_content = read_file_content(stdout_path)
        if stdout_content:
            step['stdout'] = stdout_content
        step['stdout_path'] = str(stdout_path)

    if stderr_path:
        stderr_content = read_file_content(stderr_path)
        if stderr_content:
            step['stderr'] = stderr_content
        step['stderr_path'] = str(stderr_path)

    # Merge additional metadata
    if metadata:
        step['metadata'] = metadata

    # Append to JSONL file
    with open(steps_path, 'a', encoding='utf-8') as f:
        f.write(json.dumps(step) + '\n')

    return steps_path


def main():
    parser = argparse.ArgumentParser(
        description='Record verification step to JSONL',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Step Names (common):
  extract_code     - Extract code from assistant response
  isabelle_build   - Build/verify Isabelle theories
  export_haskell   - Export Haskell code from Isabelle
  haskell_compile  - Compile generated Haskell
  haskell_test     - Run Haskell tests
  format_check     - Check code formatting

Status Values:
  pass   - Step completed successfully
  fail   - Step completed but verification failed
  skip   - Step was skipped
  error  - Step encountered an error

Examples:
  # Record successful Isabelle build
  record_step.py ./results/run1 isabelle_build pass 0 stdout.txt stderr.txt

  # Record failed compilation
  record_step.py ./results/run1 haskell_compile fail 1 --stderr compile_err.txt

  # Record with duration
  record_step.py ./results/run1 isabelle_build pass 0 --duration 45000

  # Record with metadata
  record_step.py ./results/run1 isabelle_build pass 0 --meta '{"theories": 5}'
        """
    )
    parser.add_argument(
        'out_dir',
        type=Path,
        help='Output directory for steps.jsonl'
    )
    parser.add_argument(
        'step_name',
        type=str,
        help='Name of the verification step'
    )
    parser.add_argument(
        'status',
        type=str,
        choices=['pass', 'fail', 'skip', 'error'],
        help='Step status'
    )
    parser.add_argument(
        'exit_code',
        type=int,
        help='Process exit code'
    )
    parser.add_argument(
        'stdout_path',
        nargs='?',
        type=Path,
        default=None,
        help='Path to stdout file (optional positional)'
    )
    parser.add_argument(
        'stderr_path',
        nargs='?',
        type=Path,
        default=None,
        help='Path to stderr file (optional positional)'
    )
    parser.add_argument(
        '--stdout',
        type=Path,
        default=None,
        help='Path to stdout file (named argument)'
    )
    parser.add_argument(
        '--stderr',
        type=Path,
        default=None,
        help='Path to stderr file (named argument)'
    )
    parser.add_argument(
        '--duration', '-d',
        type=int,
        default=None,
        help='Step duration in milliseconds'
    )
    parser.add_argument(
        '--meta', '-m',
        type=str,
        default=None,
        help='Additional metadata as JSON string'
    )

    args = parser.parse_args()

    # Resolve stdout/stderr paths (named args take precedence)
    stdout_path = args.stdout or args.stdout_path
    stderr_path = args.stderr or args.stderr_path

    # Parse metadata if provided
    metadata = None
    if args.meta:
        try:
            metadata = json.loads(args.meta)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in --meta: {e}", file=sys.stderr)
            sys.exit(1)

    steps_path = record_step(
        out_dir=args.out_dir,
        step_name=args.step_name,
        status=args.status,
        exit_code=args.exit_code,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
        duration_ms=args.duration,
        metadata=metadata
    )

    print(f"Recorded step '{args.step_name}' ({args.status}) to {steps_path}", file=sys.stderr)
    print(steps_path)


if __name__ == '__main__':
    main()
