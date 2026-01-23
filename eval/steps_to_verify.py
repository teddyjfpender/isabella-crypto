#!/usr/bin/env python3
"""
Convert step JSONL to final verify.json.

Reads the steps.jsonl file produced by record_step.py and creates
a consolidated verify.json with overall status, timestamps, and step details.
"""

import argparse
import json
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


def load_steps(steps_path: Path) -> list[dict]:
    """Load steps from JSONL file."""
    steps = []
    with open(steps_path, 'r', encoding='utf-8') as f:
        for line_num, line in enumerate(f, 1):
            line = line.strip()
            if not line:
                continue
            try:
                steps.append(json.loads(line))
            except json.JSONDecodeError as e:
                print(f"Warning: Invalid JSON on line {line_num}: {e}", file=sys.stderr)
    return steps


def determine_overall_status(steps: list[dict]) -> str:
    """
    Determine overall verification status from steps.

    Priority (highest to lowest):
    - error: Any step errored
    - fail: Any step failed
    - skip: All steps skipped
    - pass: All steps passed
    """
    if not steps:
        return 'skip'

    statuses = [s.get('status', 'error') for s in steps]

    if 'error' in statuses:
        return 'error'
    if 'fail' in statuses:
        return 'fail'
    if all(s == 'skip' for s in statuses):
        return 'skip'
    if all(s in ('pass', 'skip') for s in statuses):
        return 'pass'

    return 'fail'


def compute_timestamps(steps: list[dict]) -> tuple[Optional[str], Optional[str]]:
    """Extract earliest and latest timestamps from steps."""
    timestamps = []
    for step in steps:
        if 'timestamp' in step:
            try:
                ts = datetime.fromisoformat(step['timestamp'].replace('Z', '+00:00'))
                timestamps.append(ts)
            except ValueError:
                pass

    if not timestamps:
        return None, None

    return min(timestamps).isoformat(), max(timestamps).isoformat()


def compute_total_duration(steps: list[dict]) -> Optional[int]:
    """Sum up duration_ms from all steps."""
    total = 0
    has_duration = False
    for step in steps:
        if 'duration_ms' in step:
            total += step['duration_ms']
            has_duration = True
    return total if has_duration else None


def create_verify_json(
    steps: list[dict],
    include_output: bool = True,
    max_output_lines: int = 100
) -> dict:
    """
    Create verify.json structure from steps.

    Args:
        steps: List of step records
        include_output: Include stdout/stderr in output
        max_output_lines: Maximum output lines to include per step

    Returns:
        verify.json structure
    """
    overall_status = determine_overall_status(steps)
    started_at, completed_at = compute_timestamps(steps)
    total_duration = compute_total_duration(steps)

    # Clean up steps for output
    clean_steps = []
    for step in steps:
        clean_step = {
            'step': step.get('step', 'unknown'),
            'status': step.get('status', 'error'),
            'exit_code': step.get('exit_code', -1),
        }

        if 'timestamp' in step:
            clean_step['timestamp'] = step['timestamp']

        if 'duration_ms' in step:
            clean_step['duration_ms'] = step['duration_ms']

        if include_output:
            if 'stdout' in step:
                lines = step['stdout'].split('\n')
                if len(lines) > max_output_lines:
                    clean_step['stdout'] = '\n'.join(lines[:max_output_lines])
                    clean_step['stdout_truncated'] = True
                else:
                    clean_step['stdout'] = step['stdout']

            if 'stderr' in step:
                lines = step['stderr'].split('\n')
                if len(lines) > max_output_lines:
                    clean_step['stderr'] = '\n'.join(lines[:max_output_lines])
                    clean_step['stderr_truncated'] = True
                else:
                    clean_step['stderr'] = step['stderr']

        if 'metadata' in step:
            clean_step['metadata'] = step['metadata']

        clean_steps.append(clean_step)

    verify = {
        'status': overall_status,
        'steps': clean_steps,
        'step_count': len(steps),
        'passed_count': sum(1 for s in steps if s.get('status') == 'pass'),
        'failed_count': sum(1 for s in steps if s.get('status') == 'fail'),
        'error_count': sum(1 for s in steps if s.get('status') == 'error'),
        'skipped_count': sum(1 for s in steps if s.get('status') == 'skip'),
    }

    if started_at:
        verify['started_at'] = started_at
    if completed_at:
        verify['completed_at'] = completed_at
    if total_duration is not None:
        verify['total_duration_ms'] = total_duration

    # Add timestamp for when verify.json was generated
    verify['generated_at'] = datetime.now(timezone.utc).isoformat()

    return verify


def steps_to_verify(
    steps_path: Path,
    verify_path: Path,
    include_output: bool = True
) -> dict:
    """
    Convert steps.jsonl to verify.json.

    Args:
        steps_path: Path to steps.jsonl
        verify_path: Path to write verify.json
        include_output: Include stdout/stderr in output

    Returns:
        The verify dict that was written
    """
    if not steps_path.exists():
        raise FileNotFoundError(f"Steps file not found: {steps_path}")

    steps = load_steps(steps_path)
    verify = create_verify_json(steps, include_output)

    verify_path.parent.mkdir(parents=True, exist_ok=True)
    with open(verify_path, 'w', encoding='utf-8') as f:
        json.dump(verify, f, indent=2)

    return verify


def main():
    parser = argparse.ArgumentParser(
        description='Convert step JSONL to final verify.json',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Basic conversion
  steps_to_verify.py ./results/run1/steps.jsonl ./results/run1/verify.json

  # Exclude stdout/stderr from output
  steps_to_verify.py steps.jsonl verify.json --no-output

  # Pretty print to stdout
  steps_to_verify.py steps.jsonl - --pretty

Output Structure:
  {
    "status": "pass|fail|error|skip",
    "steps": [...],
    "step_count": N,
    "passed_count": N,
    "failed_count": N,
    "error_count": N,
    "skipped_count": N,
    "started_at": "ISO timestamp",
    "completed_at": "ISO timestamp",
    "total_duration_ms": N,
    "generated_at": "ISO timestamp"
  }
        """
    )
    parser.add_argument(
        'steps_jsonl_path',
        type=Path,
        help='Path to steps.jsonl input file'
    )
    parser.add_argument(
        'verify_json_path',
        type=str,
        help='Path to verify.json output file (use - for stdout)'
    )
    parser.add_argument(
        '--no-output',
        action='store_true',
        help='Exclude stdout/stderr from verify.json'
    )
    parser.add_argument(
        '--pretty', '-p',
        action='store_true',
        help='Pretty print JSON output'
    )
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Suppress status messages'
    )

    args = parser.parse_args()

    if not args.steps_jsonl_path.exists():
        print(f"Error: Steps file not found: {args.steps_jsonl_path}", file=sys.stderr)
        sys.exit(1)

    try:
        steps = load_steps(args.steps_jsonl_path)
        verify = create_verify_json(steps, include_output=not args.no_output)
    except Exception as e:
        print(f"Error processing steps: {e}", file=sys.stderr)
        sys.exit(1)

    indent = 2 if args.pretty else None

    if args.verify_json_path == '-':
        # Output to stdout
        print(json.dumps(verify, indent=indent))
    else:
        verify_path = Path(args.verify_json_path)
        verify_path.parent.mkdir(parents=True, exist_ok=True)
        with open(verify_path, 'w', encoding='utf-8') as f:
            json.dump(verify, f, indent=2)

        if not args.quiet:
            print(f"Wrote verify.json: {verify_path}", file=sys.stderr)
            print(f"Overall status: {verify['status']}", file=sys.stderr)
            print(f"Steps: {verify['passed_count']} passed, "
                  f"{verify['failed_count']} failed, "
                  f"{verify['error_count']} errors, "
                  f"{verify['skipped_count']} skipped", file=sys.stderr)


if __name__ == '__main__':
    main()
