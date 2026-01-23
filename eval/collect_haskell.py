#!/usr/bin/env python3
"""
Collect generated Haskell files from Isabelle export directory.

Scans Isabelle's export directory for generated .hs files and copies
them to the project's Haskell source directory, updating module names
if needed.
"""

import argparse
import os
import re
import shutil
import sys
from pathlib import Path
from typing import Optional


# Default paths relative to project root
DEFAULT_EXPORT_DIR = 'isabelle/.isabelle/export'
DEFAULT_TARGET_DIR = 'haskell/lattice-crypto/src/Generated'


def find_export_dirs(isabelle_dir: Path) -> list[Path]:
    """
    Find Isabelle export directories that may contain Haskell files.

    Isabelle typically exports to:
    - .isabelle/export/<session>/<theory>/code/
    - Or directly in the session directory
    """
    export_dirs = []

    # Check common export locations
    possible_roots = [
        isabelle_dir / '.isabelle' / 'export',
        isabelle_dir / 'export',
        isabelle_dir,
    ]

    for root in possible_roots:
        if root.exists():
            # Find all directories containing .hs files
            for hs_file in root.rglob('*.hs'):
                parent = hs_file.parent
                if parent not in export_dirs:
                    export_dirs.append(parent)

    return export_dirs


def find_haskell_files(export_dir: Path) -> list[Path]:
    """Find all .hs files in the export directory."""
    return list(export_dir.rglob('*.hs'))


def extract_module_name(hs_content: str) -> Optional[str]:
    """Extract module name from Haskell file content."""
    match = re.search(r'^module\s+([A-Z][\w.]*)', hs_content, re.MULTILINE)
    return match.group(1) if match else None


def update_module_name(content: str, old_module: str, new_module: str) -> str:
    """Update module name in Haskell file content."""
    # Update module declaration
    content = re.sub(
        rf'^module\s+{re.escape(old_module)}(\s)',
        f'module {new_module}\\1',
        content,
        flags=re.MULTILINE
    )
    return content


def compute_target_path(
    hs_file: Path,
    export_dir: Path,
    target_dir: Path,
    module_prefix: Optional[str] = None
) -> tuple[Path, Optional[str]]:
    """
    Compute target path for a Haskell file.

    Returns:
        Tuple of (target_path, new_module_name or None)
    """
    # Read file to get module name
    content = hs_file.read_text(encoding='utf-8')
    current_module = extract_module_name(content)

    # Use the file's relative path from export dir
    rel_path = hs_file.relative_to(export_dir)

    # Compute new module name if prefix specified
    new_module = None
    if module_prefix and current_module:
        # Strip any existing prefix and add new one
        base_module = current_module.split('.')[-1]
        new_module = f"{module_prefix}.{base_module}"
        # Update relative path to match
        rel_path = Path(new_module.replace('.', '/') + '.hs')

    target_path = target_dir / rel_path
    return target_path, new_module


def copy_haskell_file(
    src: Path,
    dst: Path,
    new_module: Optional[str] = None,
    dry_run: bool = False
) -> bool:
    """
    Copy a Haskell file, optionally updating its module name.

    Returns:
        True if file was copied/would be copied
    """
    content = src.read_text(encoding='utf-8')

    if new_module:
        old_module = extract_module_name(content)
        if old_module:
            content = update_module_name(content, old_module, new_module)

    if dry_run:
        return True

    dst.parent.mkdir(parents=True, exist_ok=True)
    dst.write_text(content, encoding='utf-8')
    return True


def collect_haskell(
    export_dir: Path,
    target_dir: Path,
    module_prefix: Optional[str] = None,
    clean: bool = False,
    dry_run: bool = False
) -> list[dict]:
    """
    Collect Haskell files from export directory to target directory.

    Args:
        export_dir: Directory containing exported Haskell files
        target_dir: Target directory for collected files
        module_prefix: Prefix to add to module names (e.g., "Generated")
        clean: Remove existing files in target directory first
        dry_run: Don't actually copy files

    Returns:
        List of dicts describing copied files
    """
    results = []

    if clean and target_dir.exists() and not dry_run:
        shutil.rmtree(target_dir)

    # Find all .hs files
    hs_files = find_haskell_files(export_dir)

    if not hs_files:
        return results

    for hs_file in hs_files:
        target_path, new_module = compute_target_path(
            hs_file, export_dir, target_dir, module_prefix
        )

        success = copy_haskell_file(hs_file, target_path, new_module, dry_run)

        results.append({
            'source': str(hs_file),
            'target': str(target_path),
            'module': new_module or extract_module_name(hs_file.read_text()),
            'copied': success,
        })

    return results


def main():
    parser = argparse.ArgumentParser(
        description='Collect generated Haskell files from Isabelle export',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Auto-detect and collect from default locations
  collect_haskell.py

  # Specify export directory
  collect_haskell.py --export-dir ./isabelle/.isabelle/export

  # Specify target directory
  collect_haskell.py --target-dir ./haskell/src/Generated

  # Add module prefix
  collect_haskell.py --module-prefix Generated

  # Clean target directory before copying
  collect_haskell.py --clean

  # Dry run to see what would be copied
  collect_haskell.py --dry-run

Directory Structure:
  Isabelle typically exports Haskell code to:
    .isabelle/export/<session>/<theory>/code/*.hs

  Files are collected to:
    haskell/lattice-crypto/src/Generated/*.hs
        """
    )
    parser.add_argument(
        '--export-dir', '-e',
        type=Path,
        default=None,
        help='Isabelle export directory (auto-detected if not specified)'
    )
    parser.add_argument(
        '--target-dir', '-t',
        type=Path,
        default=None,
        help='Target directory for Haskell files'
    )
    parser.add_argument(
        '--module-prefix', '-p',
        type=str,
        default=None,
        help='Prefix to add to module names'
    )
    parser.add_argument(
        '--clean', '-c',
        action='store_true',
        help='Clean target directory before copying'
    )
    parser.add_argument(
        '--dry-run', '-n',
        action='store_true',
        help='Show what would be copied without copying'
    )
    parser.add_argument(
        '--project-root', '-r',
        type=Path,
        default=None,
        help='Project root directory (default: current directory)'
    )
    parser.add_argument(
        '--quiet', '-q',
        action='store_true',
        help='Suppress status messages'
    )
    parser.add_argument(
        '--json',
        action='store_true',
        help='Output results as JSON'
    )

    args = parser.parse_args()

    # Determine project root
    project_root = args.project_root or Path.cwd()

    # Determine export directory
    export_dir = args.export_dir
    if not export_dir:
        # Try to find export directories
        isabelle_dir = project_root / 'isabelle'
        if not isabelle_dir.exists():
            isabelle_dir = project_root

        export_dirs = find_export_dirs(isabelle_dir)
        if not export_dirs:
            if not args.quiet:
                print("No Haskell files found in export directories", file=sys.stderr)
            sys.exit(0)

        # Use the first directory with .hs files
        export_dir = export_dirs[0]
        if not args.quiet:
            print(f"Found export directory: {export_dir}", file=sys.stderr)

    if not export_dir.exists():
        print(f"Error: Export directory not found: {export_dir}", file=sys.stderr)
        sys.exit(1)

    # Determine target directory
    target_dir = args.target_dir
    if not target_dir:
        target_dir = project_root / DEFAULT_TARGET_DIR

    # Collect files
    results = collect_haskell(
        export_dir=export_dir,
        target_dir=target_dir,
        module_prefix=args.module_prefix,
        clean=args.clean,
        dry_run=args.dry_run
    )

    if args.json:
        import json
        print(json.dumps(results, indent=2))
    else:
        if not results:
            if not args.quiet:
                print("No Haskell files found to collect", file=sys.stderr)
        else:
            action = "Would copy" if args.dry_run else "Copied"
            for r in results:
                if not args.quiet:
                    print(f"{action}: {r['source']} -> {r['target']}", file=sys.stderr)

            if not args.quiet:
                print(f"\nTotal: {len(results)} files", file=sys.stderr)


if __name__ == '__main__':
    main()
