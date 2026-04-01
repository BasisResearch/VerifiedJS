#!/usr/bin/env python3
"""Generate a Table of Contents for spec.md with line ranges and subsections."""
import re
import sys

SPEC_PATH = sys.argv[1] if len(sys.argv) > 1 else "spec.md"

with open(SPEC_PATH) as f:
    lines = f.readlines()

# Strip existing TOC if present
toc_start = None
toc_end = None
for i, line in enumerate(lines):
    if line.strip() == "<!-- TOC START -->":
        toc_start = i
    if line.strip() == "<!-- TOC END -->":
        toc_end = i + 1
        break

if toc_start is not None and toc_end is not None:
    lines = lines[:toc_start] + lines[toc_end:]

# Find all headings with levels
headings = []
for i, line in enumerate(lines):
    m = re.match(r'^(#{1,4})\s+(.*)', line)
    if m:
        level = len(m.group(1))
        title = m.group(2).strip()
        clean = re.sub(r'\\?\[([^\]]*)\](\{[^}]*\})?', r'\1', title)
        clean = re.sub(r'\\_([^_]*)_', r'\1', clean)
        clean = re.sub(r'[`*]', '', clean)
        clean = clean.strip()
        if len(clean) > 90:
            clean = clean[:87] + "..."
        headings.append({"line": i, "level": level, "title": clean})

# Compute end line for each heading (= start of next heading at same or higher level, or EOF)
for idx, h in enumerate(headings):
    end = len(lines) - 1
    for j in range(idx + 1, len(headings)):
        if headings[j]["level"] <= h["level"]:
            end = headings[j]["line"] - 1
            break
    h["end"] = end

# Build TOC
toc_body = []
for h in headings:
    indent = "  " * (h["level"] - 1)
    # Placeholder line numbers — will be adjusted
    toc_body.append({"indent": indent, "title": h["title"], "orig_start": h["line"], "orig_end": h["end"], "level": h["level"]})

# Compute TOC size
toc_header = ["<!-- TOC START -->\n", "# Table of Contents\n", "\n"]
toc_header.append(f"__{len(headings)} sections, {{TOTAL_LINES}} lines__\n\n")
toc_footer = ["<!-- TOC END -->\n"]
toc_extra = len(toc_header) + len(toc_body) + len(toc_footer)

# Build final TOC with adjusted line numbers
toc_lines = ["<!-- TOC START -->\n", "# Table of Contents\n", "\n"]
total = len(lines) + toc_extra
toc_lines.append(f"__{len(headings)} sections, {total} lines__\n\n")

for entry in toc_body:
    start = entry["orig_start"] + toc_extra + 1 + 1  # 1-indexed + TOC END newline
    end = entry["orig_end"] + toc_extra + 1 + 1
    span = end - start + 1
    toc_lines.append(f"{entry['indent']}- L{start}–L{end} ({span}L): {entry['title']}\n")

toc_lines.append("<!-- TOC END -->\n")

output = toc_lines + lines

with open(SPEC_PATH, "w") as f:
    f.writelines(output)

print(f"TOC: {len(headings)} entries with ranges, spec now {len(output)} lines")
