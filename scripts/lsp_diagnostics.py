#!/usr/bin/env python3
"""
Aggregate Lean LSP diagnostics across the project.
Prints one-line summary. Full output to file.
"""

import subprocess
import sys
import json
from pathlib import Path


def get_lean_files():
    """Find all .lean files in VerifiedJS/"""
    return sorted(Path("VerifiedJS").rglob("*.lean"))


def run_lake_build():
    """Run lake build and capture diagnostics."""
    result = subprocess.run(
        ["lake", "build"],
        capture_output=True,
        text=True,
        timeout=600
    )
    return result.stdout + result.stderr


def parse_diagnostics(output):
    """Parse lake build output for errors and warnings."""
    errors = []
    warnings = []
    for line in output.splitlines():
        if "error" in line.lower() and ":" in line:
            errors.append(line.strip())
        elif "warning" in line.lower() and ":" in line:
            warnings.append(line.strip())
    return errors, warnings


def main():
    output_file = sys.argv[1] if len(sys.argv) > 1 else "test_logs/diagnostics.log"

    print("Running lake build for diagnostics...", file=sys.stderr)
    output = run_lake_build()

    Path(output_file).parent.mkdir(parents=True, exist_ok=True)
    Path(output_file).write_text(output)

    errors, warnings = parse_diagnostics(output)

    # One-line summary
    print(f"Diagnostics: {len(errors)} errors, {len(warnings)} warnings — full output in {output_file}")

    if errors:
        print("\nTop errors:", file=sys.stderr)
        for e in errors[:5]:
            print(f"  {e}", file=sys.stderr)

    return 1 if errors else 0


if __name__ == "__main__":
    sys.exit(main())
