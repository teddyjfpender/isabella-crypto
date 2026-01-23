#!/usr/bin/env python3
"""
Extract the 'code' field from JSON assistant output.

Handles both single .thy theory files and multi-file extraction for Isabelle projects.
"""

import argparse
import json
import sys
from pathlib import Path
from typing import Optional


def extract_code_from_json(json_path: Path) -> dict:
    """
    Extract code from a JSON file with {code, notes} structure.

    The code field can be either:
    - A string (single file content)
    - A dict mapping filenames to content (multi-file)

    Returns:
        dict mapping filename -> content
    """
    with open(json_path, 'r', encoding='utf-8') as f:
        data = json.load(f)

    if 'code' not in data:
        raise ValueError(f"JSON file {json_path} does not contain a 'code' field")

    code = data['code']

    # Handle single string (assume it's the main theory file)
    if isinstance(code, str):
        # Try to extract theory name from content
        theory_name = extract_theory_name(code)
        filename = f"{theory_name}.thy" if theory_name else "Main.thy"
        return {filename: code}

    # Handle dict of files
    if isinstance(code, dict):
        return code

    # Handle list of {filename, content} objects
    if isinstance(code, list):
        return {item['filename']: item['content'] for item in code}

    raise ValueError(f"Unexpected code format: {type(code)}")


def extract_theory_name(content: str) -> Optional[str]:
    """Extract the theory name from Isabelle theory file content."""
    for line in content.split('\n'):
        line = line.strip()
        if line.startswith('theory '):
            # theory TheoryName imports ...
            parts = line.split()
            if len(parts) >= 2:
                return parts[1]
    return None


def write_files(files: dict, output_dir: Optional[Path] = None) -> None:
    """Write extracted files to disk or stdout."""
    if output_dir:
        output_dir.mkdir(parents=True, exist_ok=True)
        for filename, content in files.items():
            output_path = output_dir / filename
            # Create subdirectories if needed
            output_path.parent.mkdir(parents=True, exist_ok=True)
            with open(output_path, 'w', encoding='utf-8') as f:
                f.write(content)
            print(f"Wrote: {output_path}", file=sys.stderr)
    else:
        # Single file to stdout
        if len(files) == 1:
            print(list(files.values())[0])
        else:
            # Multiple files: output as JSON
            print(json.dumps(files, indent=2))


def main():
    parser = argparse.ArgumentParser(
        description='Extract code field from JSON assistant output',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Extract single theory to stdout
  extract_code.py response.json

  # Extract to specific directory
  extract_code.py response.json --output-dir ./theories/

  # Extract specific file from multi-file response
  extract_code.py response.json --file Main.thy
        """
    )
    parser.add_argument(
        'json_file',
        type=Path,
        help='Path to JSON file with {code, notes} structure'
    )
    parser.add_argument(
        '--output-dir', '-o',
        type=Path,
        default=None,
        help='Directory to write extracted files (default: stdout)'
    )
    parser.add_argument(
        '--file', '-f',
        type=str,
        default=None,
        help='Extract only this specific file (for multi-file responses)'
    )
    parser.add_argument(
        '--list-files', '-l',
        action='store_true',
        help='List available files without extracting'
    )

    args = parser.parse_args()

    if not args.json_file.exists():
        print(f"Error: File not found: {args.json_file}", file=sys.stderr)
        sys.exit(1)

    try:
        files = extract_code_from_json(args.json_file)
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON in {args.json_file}: {e}", file=sys.stderr)
        sys.exit(1)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)

    if args.list_files:
        for filename in files.keys():
            print(filename)
        return

    if args.file:
        if args.file not in files:
            print(f"Error: File '{args.file}' not found in response", file=sys.stderr)
            print(f"Available files: {', '.join(files.keys())}", file=sys.stderr)
            sys.exit(1)
        files = {args.file: files[args.file]}

    write_files(files, args.output_dir)


if __name__ == '__main__':
    main()
