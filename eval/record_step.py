#!/usr/bin/env python3
"""
Record individual verification step to JSONL file.

Usage:
    record_step.py <steps_file> <step> <cmd> <status> <exit_code> <duration_sec> <stdout_path> <stderr_path> [message]

Arguments:
    steps_file    Path to steps.jsonl file (will be created/appended)
    step          Step name (e.g., 'check', 'build', 'export')
    cmd           Command that was run
    status        Step status: 'pass', 'fail', 'skipped', or 'error'
    exit_code     Process exit code (integer)
    duration_sec  Step duration in seconds (integer)
    stdout_path   Path to stdout file (use empty string for none)
    stderr_path   Path to stderr file (use empty string for none)
    message       Optional message/notes about the step

Each invocation appends a single step record to the JSONL file.
"""

import json
import sys
from datetime import datetime, timezone
from pathlib import Path


def read_file_content(path: str, max_bytes: int = 50000) -> str | None:
    """Read file content, truncating if too long."""
    if not path or path == "":
        return None

    p = Path(path)
    if not p.exists():
        return None

    try:
        content = p.read_text(encoding='utf-8', errors='replace')
        if len(content) > max_bytes:
            content = content[:max_bytes] + f"\n... (truncated, {len(content) - max_bytes} more bytes)"
        return content
    except Exception as e:
        return f"[Error reading file: {e}]"


def record_step(
    steps_file: str,
    step: str,
    cmd: str,
    status: str,
    exit_code: int,
    duration_sec: int,
    stdout_path: str,
    stderr_path: str,
    message: str = ""
) -> None:
    """
    Append a step record to the JSONL file.
    """
    record = {
        "step": step,
        "cmd": cmd,
        "status": status,
        "exit_code": exit_code,
        "duration_sec": duration_sec,
        "timestamp": datetime.now(timezone.utc).isoformat(),
    }

    # Add paths if provided
    if stdout_path:
        record["stdout_path"] = stdout_path
    if stderr_path:
        record["stderr_path"] = stderr_path

    # Add message if provided
    if message:
        record["message"] = message

    # Append to JSONL
    with open(steps_file, 'a', encoding='utf-8') as f:
        f.write(json.dumps(record) + '\n')


def main():
    if len(sys.argv) < 9:
        print(__doc__, file=sys.stderr)
        print(f"\nError: Expected at least 8 arguments, got {len(sys.argv) - 1}", file=sys.stderr)
        print(f"Usage: {sys.argv[0]} <steps_file> <step> <cmd> <status> <exit_code> <duration_sec> <stdout_path> <stderr_path> [message]", file=sys.stderr)
        sys.exit(2)

    steps_file = sys.argv[1]
    step = sys.argv[2]
    cmd = sys.argv[3]
    status = sys.argv[4]

    try:
        exit_code = int(sys.argv[5])
    except ValueError:
        print(f"Error: exit_code must be an integer, got '{sys.argv[5]}'", file=sys.stderr)
        sys.exit(1)

    try:
        duration_sec = int(sys.argv[6])
    except ValueError:
        print(f"Error: duration_sec must be an integer, got '{sys.argv[6]}'", file=sys.stderr)
        sys.exit(1)

    stdout_path = sys.argv[7] if sys.argv[7] else ""
    stderr_path = sys.argv[8] if sys.argv[8] else ""
    message = sys.argv[9] if len(sys.argv) > 9 else ""

    # Validate status
    valid_statuses = ['pass', 'fail', 'skipped', 'skip', 'error']
    if status not in valid_statuses:
        print(f"Warning: Unexpected status '{status}', expected one of {valid_statuses}", file=sys.stderr)

    # Normalize 'skip' to 'skipped' for consistency
    if status == 'skip':
        status = 'skipped'

    record_step(
        steps_file=steps_file,
        step=step,
        cmd=cmd,
        status=status,
        exit_code=exit_code,
        duration_sec=duration_sec,
        stdout_path=stdout_path,
        stderr_path=stderr_path,
        message=message
    )


if __name__ == '__main__':
    main()
