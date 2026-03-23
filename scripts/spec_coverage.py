#!/usr/bin/env python3
"""Compute spec.md coverage from SPEC: references in Lean files. Output JSON for dashboard."""
import json
import os
import re
import sys

SPEC_PATH = sys.argv[1] if len(sys.argv) > 1 else "spec.md"
LEAN_DIR = sys.argv[2] if len(sys.argv) > 2 else "VerifiedJS"
OUT_PATH = sys.argv[3] if len(sys.argv) > 3 else "logs/spec_coverage.json"

# Read spec to get section info
with open(SPEC_PATH) as f:
    spec_lines = f.readlines()

total_spec_lines = len(spec_lines)

# Find sections from TOC
sections = []
for i, line in enumerate(spec_lines):
    m = re.match(r'^(#{1,4})\s+(.*)', line)
    if m and i > 0:  # skip TOC heading itself
        level = len(m.group(1))
        title = m.group(2).strip()
        clean = re.sub(r'\\?\[([^\]]*)\](\{[^}]*\})?', r'\1', title)
        clean = re.sub(r'[`*\\_]', '', clean).strip()
        sections.append({"line": i + 1, "level": level, "title": clean[:80]})

# Find all SPEC: references in Lean files
covered_lines = set()
refs = []

for root, dirs, files in os.walk(LEAN_DIR):
    for f in files:
        if not f.endswith(".lean"):
            continue
        path = os.path.join(root, f)
        with open(path) as fh:
            for line_no, line in enumerate(fh, 1):
                m = re.search(r'SPEC:\s*L(\d+)\s*[-–]\s*L(\d+)', line)
                if m:
                    start, end = int(m.group(1)), int(m.group(2))
                    for i in range(start, end + 1):
                        covered_lines.add(i)
                    refs.append({
                        "file": path,
                        "line": line_no,
                        "spec_start": start,
                        "spec_end": end,
                    })

# Compute per-section coverage
for s in sections:
    s_start = s["line"]
    # Find next section at same or higher level
    s_end = total_spec_lines
    idx = sections.index(s)
    for j in range(idx + 1, len(sections)):
        if sections[j]["level"] <= s["level"]:
            s_end = sections[j]["line"] - 1
            break
    s["end"] = s_end
    s["total_lines"] = s_end - s_start + 1
    s["covered_lines"] = len([l for l in range(s_start, s_end + 1) if l in covered_lines])
    s["coverage"] = round(s["covered_lines"] / max(s["total_lines"], 1) * 100, 1)

# Top-level summary
output = {
    "total_spec_lines": total_spec_lines,
    "covered_lines": len(covered_lines),
    "coverage_pct": round(len(covered_lines) / total_spec_lines * 100, 1),
    "total_refs": len(refs),
    "sections": [s for s in sections if s["level"] == 1 and s["total_lines"] > 10],  # major sections only
    "refs": refs[-50:],  # last 50 refs
}

os.makedirs(os.path.dirname(OUT_PATH), exist_ok=True)
with open(OUT_PATH, "w") as f:
    json.dump(output, f)

print(f"Coverage: {output['covered_lines']}/{output['total_spec_lines']} lines ({output['coverage_pct']}%), {len(refs)} refs")
