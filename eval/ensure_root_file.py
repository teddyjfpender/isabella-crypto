#!/usr/bin/env python3
"""
Normalize ROOT file with required Isabelle session settings.

Ensures proper session configuration, standard build options, and
code export configuration for Haskell generation.
"""

import argparse
import re
import sys
from pathlib import Path
from typing import Optional


# Default ROOT file template for Isabelle projects
ROOT_TEMPLATE = '''session "{session_name}" = "HOL" +
  options [
    document = false,
    timeout = 300,
    quick_and_dirty = false
  ]
  sessions
    "HOL-Library"
    "HOL-Computational_Algebra"
  theories
{theories}
  export_files (in "../haskell/lattice-crypto/src/Generated")
    "*:**.hs"
'''

# Export code configuration for Haskell
EXPORT_CODE_TEMPLATE = '''
  (* Haskell code generation *)
  export_code
    {exports}
  in Haskell
    module_name {module_name}
    file_prefix {file_prefix}
'''

# Standard options to ensure are present
REQUIRED_OPTIONS = {
    'document': 'false',
    'timeout': '300',
    'quick_and_dirty': 'false',
}


def find_theory_files(project_dir: Path) -> list[str]:
    """Find all .thy files in the project directory."""
    theories = []
    for thy_file in project_dir.glob('**/*.thy'):
        # Get relative path from project_dir
        rel_path = thy_file.relative_to(project_dir)
        # Convert to theory name (remove .thy, use dots for subdirs)
        theory_name = str(rel_path.with_suffix('')).replace('/', '.')
        theories.append(theory_name)
    return sorted(theories)


def parse_existing_root(root_path: Path) -> dict:
    """Parse existing ROOT file to extract current settings."""
    if not root_path.exists():
        return {}

    content = root_path.read_text(encoding='utf-8')

    result = {
        'content': content,
        'session_name': None,
        'options': {},
        'theories': [],
        'sessions': [],
    }

    # Extract session name
    session_match = re.search(r'session\s+"([^"]+)"', content)
    if session_match:
        result['session_name'] = session_match.group(1)

    # Extract options block
    options_match = re.search(r'options\s*\[(.*?)\]', content, re.DOTALL)
    if options_match:
        options_text = options_match.group(1)
        for opt_match in re.finditer(r'(\w+)\s*=\s*(\w+|"[^"]*")', options_text):
            key, value = opt_match.groups()
            result['options'][key] = value.strip('"')

    # Extract theories
    theories_match = re.search(r'theories\s+(.*?)(?:export_files|export_code|$)', content, re.DOTALL)
    if theories_match:
        theories_text = theories_match.group(1)
        result['theories'] = [t.strip() for t in theories_text.split() if t.strip() and not t.startswith('(')]

    return result


def generate_root_content(
    session_name: str,
    theories: list[str],
    options: Optional[dict] = None,
    export_haskell: bool = True
) -> str:
    """Generate ROOT file content."""
    opts = {**REQUIRED_OPTIONS}
    if options:
        opts.update(options)

    # Format options
    options_lines = ',\n    '.join(f'{k} = {v}' for k, v in opts.items())

    # Format theories (indent with 4 spaces)
    if theories:
        theories_lines = '\n'.join(f'    "{t}"' for t in theories)
    else:
        theories_lines = '    "Main"'

    content = f'''session "{session_name}" = "HOL" +
  options [
    {options_lines}
  ]
  sessions
    "HOL-Library"
    "HOL-Computational_Algebra"
  theories
{theories_lines}
'''

    if export_haskell:
        content += '''  export_files (in "../haskell/lattice-crypto/src/Generated")
    "*:**.hs"
'''

    return content


def ensure_root_file(
    project_dir: Path,
    session_name: Optional[str] = None,
    force: bool = False
) -> Path:
    """
    Ensure a properly configured ROOT file exists.

    Args:
        project_dir: Path to the Isabelle project directory
        session_name: Session name (default: derived from directory name)
        force: Overwrite existing ROOT file completely

    Returns:
        Path to the ROOT file
    """
    root_path = project_dir / 'ROOT'

    # Default session name from directory
    if not session_name:
        session_name = project_dir.name.replace('-', '_').replace(' ', '_')
        # Capitalize first letter
        session_name = session_name[0].upper() + session_name[1:] if session_name else 'Main'

    # Find theory files
    theories = find_theory_files(project_dir)
    if not theories:
        theories = ['Main']

    existing = parse_existing_root(root_path)

    if existing and not force:
        # Merge with existing settings
        if existing.get('session_name'):
            session_name = existing['session_name']

        # Merge options, ensuring required ones are present
        options = {**REQUIRED_OPTIONS}
        options.update(existing.get('options', {}))

        # Use existing theories if present, otherwise use discovered
        if existing.get('theories'):
            theories = existing['theories']

        content = generate_root_content(session_name, theories, options)
    else:
        # Generate fresh ROOT file
        content = generate_root_content(session_name, theories)

    root_path.write_text(content, encoding='utf-8')
    return root_path


def main():
    parser = argparse.ArgumentParser(
        description='Normalize ROOT file with required Isabelle settings',
        formatter_class=argparse.RawDescriptionHelpFormatter,
        epilog="""
Examples:
  # Auto-configure ROOT file in current directory
  ensure_root_file.py .

  # Configure with specific session name
  ensure_root_file.py ./theories LatticeCrypto

  # Force regeneration of ROOT file
  ensure_root_file.py ./theories --force

  # Skip Haskell export configuration
  ensure_root_file.py ./theories --no-export
        """
    )
    parser.add_argument(
        'project_dir',
        type=Path,
        help='Path to Isabelle project directory'
    )
    parser.add_argument(
        'session_name',
        nargs='?',
        default=None,
        help='Session name (default: derived from directory name)'
    )
    parser.add_argument(
        '--force', '-f',
        action='store_true',
        help='Overwrite existing ROOT file completely'
    )
    parser.add_argument(
        '--no-export',
        action='store_true',
        help='Skip Haskell export configuration'
    )
    parser.add_argument(
        '--dry-run', '-n',
        action='store_true',
        help='Print generated content without writing'
    )

    args = parser.parse_args()

    if not args.project_dir.exists():
        print(f"Error: Directory not found: {args.project_dir}", file=sys.stderr)
        sys.exit(1)

    if not args.project_dir.is_dir():
        print(f"Error: Not a directory: {args.project_dir}", file=sys.stderr)
        sys.exit(1)

    # Find theories
    theories = find_theory_files(args.project_dir)
    session_name = args.session_name or args.project_dir.name.replace('-', '_')
    session_name = session_name[0].upper() + session_name[1:] if session_name else 'Main'

    if args.dry_run:
        content = generate_root_content(
            session_name,
            theories if theories else ['Main'],
            export_haskell=not args.no_export
        )
        print(content)
        return

    root_path = ensure_root_file(
        args.project_dir,
        args.session_name,
        args.force
    )

    print(f"ROOT file written: {root_path}", file=sys.stderr)
    print(root_path)


if __name__ == '__main__':
    main()
