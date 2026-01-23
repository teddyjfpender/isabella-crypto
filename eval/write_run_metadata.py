#!/usr/bin/env python3
"""
Write run.json with execution metadata.

Records comprehensive metadata about an evaluation run including
prompt info, model, timing, and results.
"""

import argparse
import json
import os
import sys
from datetime import datetime, timezone
from pathlib import Path
from typing import Optional


def get_git_info(work_dir: Path) -> dict:
    """Get git information if available."""
    import subprocess

    git_info = {}

    try:
        # Check if we're in a git repo
        result = subprocess.run(
            ['git', 'rev-parse', '--git-dir'],
            cwd=work_dir,
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode != 0:
            return git_info

        # Get commit hash
        result = subprocess.run(
            ['git', 'rev-parse', 'HEAD'],
            cwd=work_dir,
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            git_info['commit'] = result.stdout.strip()

        # Get branch name
        result = subprocess.run(
            ['git', 'rev-parse', '--abbrev-ref', 'HEAD'],
            cwd=work_dir,
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            git_info['branch'] = result.stdout.strip()

        # Check for uncommitted changes
        result = subprocess.run(
            ['git', 'status', '--porcelain'],
            cwd=work_dir,
            capture_output=True,
            text=True,
            timeout=5
        )
        if result.returncode == 0:
            git_info['dirty'] = bool(result.stdout.strip())

    except (subprocess.TimeoutExpired, FileNotFoundError):
        pass

    return git_info


def get_env_info() -> dict:
    """Collect relevant environment information."""
    env_info = {}

    # Isabelle-related env vars
    isabelle_vars = ['ISABELLE_HOME', 'ISABELLE_HOME_USER', 'ISABELLE_TOOL']
    for var in isabelle_vars:
        if var in os.environ:
            env_info[var] = os.environ[var]

    # Python version
    env_info['python_version'] = sys.version.split()[0]

    # Platform info
    import platform
    env_info['platform'] = platform.system()
    env_info['platform_version'] = platform.version()

    return env_info


def write_run_metadata(
    output_path: Path,
    prompt_id: str,
    prompt_path: Optional[Path] = None,
    skill: Optional[str] = None,
    work_dir: Optional[Path] = None,
    model: Optional[str] = None,
    exit_code: Optional[int] = None,
    started_at: Optional[str] = None,
    completed_at: Optional[str] = None,
    duration_ms: Optional[int] = None,
    extra_metadata: Optional[dict] = None
) -> dict:
    """
    Write run.json with execution metadata.

    Args:
        output_path: Path to write run.json
        prompt_id: Identifier for the prompt
        prompt_path: Path to the prompt file
        skill: Skill name being evaluated
        work_dir: Working directory for the run
        model: Model identifier
        exit_code: Final exit code
        started_at: ISO timestamp when run started
        completed_at: ISO timestamp when run completed
        duration_ms: Total duration in milliseconds
        extra_metadata: Additional metadata to include

    Returns:
        The metadata dict that was written
    """
    now = datetime.now(timezone.utc).isoformat()

    metadata = {
        'prompt_id': prompt_id,
        'generated_at': now,
    }

    if prompt_path:
        metadata['prompt_path'] = str(prompt_path.resolve())

    if skill:
        metadata['skill'] = skill

    if work_dir:
        metadata['work_dir'] = str(work_dir.resolve())
        metadata['git'] = get_git_info(work_dir)

    if model:
        metadata['model'] = model

    if exit_code is not None:
        metadata['exit_code'] = exit_code
        metadata['success'] = exit_code == 0

    # Timing information
    timing = {}
    if started_at:
        timing['started_at'] = started_at
    if completed_at:
        timing['completed_at'] = completed_at
    if duration_ms is not None:
        timing['duration_ms'] = duration_ms
    if timing:
        metadata['timing'] = timing

    # Environment information
    metadata['environment'] = get_env_info()

    # Merge extra metadata
    if extra_metadata:
        metadata['extra'] = extra_metadata

    # Write to file
    output_path.parent.mkdir(parents=True, exist_ok=True)
    with open(output_path, 'w', encoding='utf-8') as f:
        json.dump(metadata, f, indent=2)

    return metadata


def main():
    parser = argparse.ArgumentParser(
        description='Write run.json with execution metadata',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Minimal run metadata
  write_run_metadata.py ./results/run1/run.json --prompt-id lattice_001

  # Full metadata
  write_run_metadata.py ./results/run1/run.json \\
    --prompt-id lattice_001 \\
    --prompt-path ./prompts/lattice_001.json \\
    --skill isabelle_crypto \\
    --work-dir ./work/run1 \\
    --model claude-opus-4-5-20251101 \\
    --exit-code 0 \\
    --started-at 2024-01-15T10:00:00Z \\
    --duration 45000

  # With extra metadata
  write_run_metadata.py run.json --prompt-id test \\
    --extra '{"attempt": 2, "variant": "retry"}'

Output Structure:
  {
    "prompt_id": "...",
    "prompt_path": "...",
    "skill": "...",
    "work_dir": "...",
    "model": "...",
    "exit_code": 0,
    "success": true,
    "timing": {...},
    "environment": {...},
    "git": {...},
    "generated_at": "..."
  }
        """
    )
    parser.add_argument(
        'output_path',
        type=Path,
        help='Path to write run.json'
    )
    parser.add_argument(
        '--prompt-id', '-i',
        type=str,
        required=True,
        help='Identifier for the prompt'
    )
    parser.add_argument(
        '--prompt-path', '-p',
        type=Path,
        default=None,
        help='Path to the prompt file'
    )
    parser.add_argument(
        '--skill', '-s',
        type=str,
        default=None,
        help='Skill name being evaluated'
    )
    parser.add_argument(
        '--work-dir', '-w',
        type=Path,
        default=None,
        help='Working directory for the run'
    )
    parser.add_argument(
        '--model', '-m',
        type=str,
        default=None,
        help='Model identifier'
    )
    parser.add_argument(
        '--exit-code', '-e',
        type=int,
        default=None,
        help='Final exit code'
    )
    parser.add_argument(
        '--started-at',
        type=str,
        default=None,
        help='ISO timestamp when run started'
    )
    parser.add_argument(
        '--completed-at',
        type=str,
        default=None,
        help='ISO timestamp when run completed'
    )
    parser.add_argument(
        '--duration',
        type=int,
        default=None,
        help='Total duration in milliseconds'
    )
    parser.add_argument(
        '--extra',
        type=str,
        default=None,
        help='Additional metadata as JSON string'
    )
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Suppress status messages'
    )

    args = parser.parse_args()

    # Parse extra metadata if provided
    extra_metadata = None
    if args.extra:
        try:
            extra_metadata = json.loads(args.extra)
        except json.JSONDecodeError as e:
            print(f"Error: Invalid JSON in --extra: {e}", file=sys.stderr)
            sys.exit(1)

    try:
        metadata = write_run_metadata(
            output_path=args.output_path,
            prompt_id=args.prompt_id,
            prompt_path=args.prompt_path,
            skill=args.skill,
            work_dir=args.work_dir,
            model=args.model,
            exit_code=args.exit_code,
            started_at=args.started_at,
            completed_at=args.completed_at,
            duration_ms=args.duration,
            extra_metadata=extra_metadata
        )
    except Exception as e:
        print(f"Error writing metadata: {e}", file=sys.stderr)
        sys.exit(1)

    if not args.quiet:
        print(f"Wrote run metadata: {args.output_path}", file=sys.stderr)
        print(f"Prompt ID: {metadata['prompt_id']}", file=sys.stderr)
        if 'success' in metadata:
            status = 'success' if metadata['success'] else 'failed'
            print(f"Status: {status}", file=sys.stderr)


if __name__ == '__main__':
    main()
