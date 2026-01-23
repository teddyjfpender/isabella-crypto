#!/usr/bin/env python3
"""
Convert step JSONL to final verify.json.

Usage:
    steps_to_verify.py <steps_file> <verify_json> <started_at> <ended_at> <project_dir>

Arguments:
    steps_file    Path to steps.jsonl input file
    verify_json   Path to write verify.json output
    started_at    ISO timestamp when verification started
    ended_at      ISO timestamp when verification ended
    project_dir   Path to the project directory being verified

Reads the steps.jsonl file produced by record_step.py and creates
a consolidated verify.json with overall status, timestamps, and step details.
"""

import json
import sys
from datetime import datetime
from pathlib import Path


def load_steps(steps_path: Path) -> list[dict]:
    """Load steps from JSONL file."""
    steps = []
    if not steps_path.exists():
        return steps

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


def compute_duration(started_at: str, ended_at: str) -> int:
    """Compute duration in seconds between two ISO timestamps."""
    try:
        start = datetime.fromisoformat(started_at.replace('Z', '+00:00'))
        end = datetime.fromisoformat(ended_at.replace('Z', '+00:00'))
        return int((end - start).total_seconds())
    except (ValueError, AttributeError):
        return 0


def read_file_content(path: str, max_lines: int = 100) -> "str | None":
    """Read file content for inclusion in verify.json."""
    if not path:
        return None

    p = Path(path)
    if not p.exists():
        return None

    try:
        content = p.read_text(encoding='utf-8', errors='replace')
        lines = content.split('\n')
        if len(lines) > max_lines:
            return '\n'.join(lines[:max_lines]) + f"\n... ({len(lines) - max_lines} more lines)"
        return content
    except Exception:
        return None


def create_verify_json(
    steps: list[dict],
    started_at: str,
    ended_at: str,
    project_dir: str
) -> dict:
    """Create verify.json structure from steps."""

    # Count statuses
    counts = {
        'pass': 0,
        'fail': 0,
        'skipped': 0,
        'error': 0
    }
    failed_steps = []

    for step in steps:
        status = step.get('status', 'error')
        # Normalize status names
        if status == 'skip':
            status = 'skipped'

        if status in counts:
            counts[status] += 1
        else:
            counts['error'] += 1

        if status == 'fail':
            failed_steps.append(step.get('step', 'unknown'))

    # Determine overall status
    if counts['error'] > 0:
        overall_status = 'error'
    elif counts['fail'] > 0:
        overall_status = 'fail'
    elif counts['pass'] > 0:
        overall_status = 'pass'
    else:
        overall_status = 'skipped'

    # Compute duration
    duration_sec = compute_duration(started_at, ended_at)

    # Build clean steps list
    clean_steps = []
    for step in steps:
        clean_step = {
            'name': step.get('step', 'unknown'),
            'cmd': step.get('cmd', ''),
            'status': step.get('status', 'error'),
            'exit_code': step.get('exit_code', -1),
            'duration_sec': step.get('duration_sec', 0),
        }

        # Include stdout/stderr paths
        if step.get('stdout_path'):
            clean_step['stdout_path'] = step['stdout_path']
        if step.get('stderr_path'):
            clean_step['stderr_path'] = step['stderr_path']

        # Include message if present
        if step.get('message'):
            clean_step['message'] = step['message']

        clean_steps.append(clean_step)

    verify = {
        'version': 1,
        'status': overall_status,
        'started_at': started_at,
        'ended_at': ended_at,
        'duration_sec': duration_sec,
        'project_dir': project_dir,
        'counts': {
            'pass': counts['pass'],
            'fail': counts['fail'],
            'skipped': counts['skipped'],
            'error': counts['error']
        },
        'failed_steps': failed_steps,
        'steps': clean_steps
    }

    return verify


def main():
    if len(sys.argv) < 6:
        print(__doc__, file=sys.stderr)
        print(f"\nError: Expected 5 arguments, got {len(sys.argv) - 1}", file=sys.stderr)
        print(f"Usage: {sys.argv[0]} <steps_file> <verify_json> <started_at> <ended_at> <project_dir>", file=sys.stderr)
        sys.exit(2)

    steps_file = Path(sys.argv[1])
    verify_json = Path(sys.argv[2])
    started_at = sys.argv[3]
    ended_at = sys.argv[4]
    project_dir = sys.argv[5]

    # Load steps
    steps = load_steps(steps_file)

    # Create verify.json
    verify = create_verify_json(steps, started_at, ended_at, project_dir)

    # Write output
    verify_json.parent.mkdir(parents=True, exist_ok=True)
    with open(verify_json, 'w', encoding='utf-8') as f:
        json.dump(verify, f, indent=2)

    # Print summary
    print(f"Wrote {verify_json}", file=sys.stderr)
    print(f"Status: {verify['status']} ({verify['counts']['pass']} pass, {verify['counts']['fail']} fail, {verify['counts']['skipped']} skip)", file=sys.stderr)


if __name__ == '__main__':
    main()
