#!/usr/bin/env python3
"""Extract theorem-level dependency graph from Lean source files."""
import json, re, os
from datetime import datetime
from pathlib import Path

os.chdir("/opt/verifiedjs")

# Collect all theorem/lemma/def declarations
all_decls = {}
for root, dirs, files in os.walk("VerifiedJS"):
    for f in sorted(files):
        if not f.endswith(".lean"):
            continue
        path = os.path.join(root, f)
        text = open(path).read()
        lines = text.splitlines()
        for i, line in enumerate(lines):
            m = re.match(r"^(private\s+)?(theorem|lemma|def|instance)\s+(\S+)", line)
            if not m:
                continue
            name = m.group(3)
            kind = m.group(2)
            private = bool(m.group(1))
            # Get block until next top-level decl
            block_lines = []
            for j in range(i, min(i + 80, len(lines))):
                block_lines.append(lines[j])
                if j > i and re.match(r"^(private\s+)?(theorem|lemma|def|instance|structure|inductive|class|namespace|section|end\s|open|import|#)", lines[j]):
                    block_lines.pop()
                    break
            block = "\n".join(block_lines)
            has_sorry = "sorry" in block and kind in ("theorem", "lemma")
            module = path.replace("/", ".").replace(".lean", "")
            full_name = f"{module}.{name}"
            all_decls[full_name] = {
                "name": name, "full_name": full_name, "module": module,
                "file": path, "line": i + 1, "kind": kind,
                "private": private, "sorry": has_sorry, "block": block,
            }

# Find deps: which other declarations does each theorem reference?
nodes = []
edges = []
node_ids = set()

for fn, info in all_decls.items():
    if info["kind"] not in ("theorem", "lemma"):
        continue
    deps = set()
    block = info["block"]
    for other_fn, other_info in all_decls.items():
        if other_fn == fn:
            continue
        other_short = other_info["name"]
        if len(other_short) < 3:
            continue  # skip very short names to avoid false matches
        if re.search(r"\b" + re.escape(other_short) + r"\b", block):
            deps.add(other_fn)
    nodes.append({
        "id": fn, "name": info["name"], "module": info["module"],
        "file": info["file"], "line": info["line"],
        "kind": info["kind"], "sorry": info["sorry"],
    })
    node_ids.add(fn)
    for dep in deps:
        edges.append({"source": fn, "target": dep, "target_kind": all_decls[dep]["kind"]})

# Add def nodes that are referenced
for e in edges:
    if e["target"] not in node_ids:
        info = all_decls[e["target"]]
        nodes.append({
            "id": info["full_name"], "name": info["name"], "module": info["module"],
            "file": info["file"], "line": info["line"],
            "kind": info["kind"], "sorry": info.get("sorry", False),
        })
        node_ids.add(info["full_name"])

output = {"nodes": nodes, "edges": edges, "generated": datetime.utcnow().isoformat() + "Z"}

os.makedirs("logs/thm_snapshots", exist_ok=True)
ts = datetime.utcnow().strftime("%Y%m%d_%H%M%S")
with open("logs/thm_graph.json", "w") as f:
    json.dump(output, f)
with open(f"logs/thm_snapshots/{ts}.json", "w") as f:
    json.dump(output, f)

print(f"nodes: {len(nodes)}, edges: {len(edges)}, snapshots: {len(os.listdir('logs/thm_snapshots'))}")
