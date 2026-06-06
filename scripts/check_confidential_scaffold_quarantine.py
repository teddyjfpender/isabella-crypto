#!/usr/bin/env python3
"""Validate confidential-transfer scaffold quarantine.

The algebraic ledger transaction verifier remains available for compatibility
and audit tests, but production-facing validation should not invoke it through
ambiguous command names. This gate requires explicit scaffold-native aliases and
rejects legacy CLI spellings in production-facing scripts and validators.
"""

from __future__ import annotations

import json
import re
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]

LEGACY_COMMAND_PATTERN = re.compile(
    r"(?<![A-Za-z0-9_-])(ct-prove|ct-verify|ct-verify-bench)(?![A-Za-z0-9_-])"
)


def fail(message: str) -> None:
    raise SystemExit(message)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except FileNotFoundError:
        fail(f"required file is missing: {path.relative_to(ROOT)}")


def require_snippet(path: Path, snippet: str) -> None:
    if snippet not in read_text(path):
        fail(f"{path.relative_to(ROOT)} is missing required scaffold quarantine snippet: {snippet}")


def production_files() -> list[Path]:
    files = [
        ROOT / "Makefile",
        ROOT / ".github" / "workflows" / "ci.yml",
        ROOT / "tests" / "src" / "isabella-cli.ts",
        ROOT / "tests" / "src" / "validate-ocaml.ts",
        ROOT / "tests" / "src" / "validate-haskell.ts",
    ]
    scripts_dir = ROOT / "scripts"
    files.extend(
        path
        for path in sorted(scripts_dir.iterdir())
        if path.is_file()
        and path.name != Path(__file__).name
        and path.suffix in {".py", ".mjs", ".js", ".sh"}
    )
    return files


def find_legacy_command_uses(paths: list[Path]) -> list[str]:
    violations: list[str] = []
    for path in paths:
        text = read_text(path)
        for line_number, line in enumerate(text.splitlines(), start=1):
            match = LEGACY_COMMAND_PATTERN.search(line)
            if match is not None:
                violations.append(
                    f"{path.relative_to(ROOT)}:{line_number}: legacy scaffold CLI command `{match.group(1)}`"
                )
    return violations


def main() -> None:
    ocaml_cli = ROOT / "isabella.ml" / "bin" / "isabella_cli.ml"
    haskell_commands = ROOT / "isabella.hs" / "app" / "CLI" / "Commands.hs"
    haskell_main = ROOT / "isabella.hs" / "app" / "Main.hs"
    ts_cli = ROOT / "tests" / "src" / "isabella-cli.ts"
    makefile = ROOT / "Makefile"
    ci = ROOT / ".github" / "workflows" / "ci.yml"

    for path in (ocaml_cli, haskell_commands):
        require_snippet(path, "ct-prove-scaffold")
        require_snippet(path, "ct-verify-scaffold")
        require_snippet(path, "ct-verify-bench-scaffold")

    for path in (ocaml_cli, haskell_main):
        require_snippet(path, "deprecated scaffold compatibility aliases")
        require_snippet(path, "algebraic ledger hash")

    require_snippet(ts_cli, "export function ctProveScaffold")
    require_snippet(ts_cli, "'ct-prove-scaffold'")
    require_snippet(ts_cli, "export function ctVerifyScaffold")
    require_snippet(ts_cli, "'ct-verify-scaffold'")
    require_snippet(makefile, "scripts/check_confidential_scaffold_quarantine.py")
    require_snippet(ci, "scripts/check_confidential_scaffold_quarantine.py")

    violations = find_legacy_command_uses(production_files())
    if violations:
        fail(
            "ambiguous scaffold CLI commands are not allowed in production-facing checks:\n"
            + "\n".join(violations)
        )

    print(json.dumps({
        "gate": "confidential-scaffold-quarantine",
        "status": "passed",
        "checked_files": [str(path.relative_to(ROOT)) for path in production_files()],
    }, indent=2))


if __name__ == "__main__":
    main()
