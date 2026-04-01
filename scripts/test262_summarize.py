#!/usr/bin/env python3
"""Summarize test262 failures into a compact markdown file for agents."""
import collections
from pathlib import Path

latest = Path("/opt/verifiedjs/logs/test262_latest.txt")
if not latest.exists():
    exit(0)

text = latest.read_text()
cats = collections.Counter()
examples = collections.defaultdict(list)

for line in text.splitlines():
    if not line.startswith("TEST262_FAIL"):
        continue
    parts = line.split(" ", 2)
    reason = parts[1] if len(parts) > 1 else "unknown"
    path = parts[2].split(" :: ")[0] if len(parts) > 2 else ""
    cats[reason] += 1
    if len(examples[reason]) < 3:
        examples[reason].append(path.split("/")[-1] if "/" in path else path)

out = "# Test262 Failure Summary\n\n"
for reason, count in cats.most_common():
    exs = ", ".join(examples[reason])
    out += f"- **{reason}** ({count}): e.g. {exs}\n"
out += f"\nTotal failures: {sum(cats.values())}\n"
out += "Full details: `logs/test262_latest.txt`\n"
out += "Failure lines: `logs/test262_failures.txt` (first 50)\n"

Path("/opt/verifiedjs/logs/test262_summary.md").write_text(out)
