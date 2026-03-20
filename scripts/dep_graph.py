#!/usr/bin/env python3
"""Generate module dependency graph as JSON."""
import subprocess, json, os, re, sys

os.chdir("/opt/verifiedjs")
os.environ["ELAN_HOME"] = "/opt/elan"
os.environ["PATH"] = "/opt/elan/bin:/usr/local/bin:" + os.environ.get("PATH", "")

modules = []
for root, dirs, files in os.walk("VerifiedJS"):
    for f in sorted(files):
        if not f.endswith(".lean"):
            continue
        path = os.path.join(root, f)
        mod = path.replace("/", ".").replace(".lean", "")
        try:
            out = subprocess.check_output(
                ["lake", "env", "lean", "--deps", path],
                stderr=subprocess.DEVNULL, text=True, timeout=10
            )
            deps = []
            for line in out.strip().splitlines():
                if "/VerifiedJS/" in line and ".olean" in line:
                    dep = line.split("/VerifiedJS/")[1].replace("/", ".").replace(".olean", "")
                    deps.append("VerifiedJS." + dep)
        except Exception:
            deps = []
        text = open(path).read()
        has_sorry = "sorry" in text
        thm_names = re.findall(r"^(?:private )?(theorem|lemma) (\S+)", text, re.M)
        loc = text.count("\n")
        modules.append({
            "name": mod, "file": path, "deps": deps,
            "sorry": has_sorry, "theorems": len(thm_names), "loc": loc,
            "theorem_names": [t[1] for t in thm_names]
        })

out_path = "/opt/verifiedjs/logs/dep_graph.json"
os.makedirs(os.path.dirname(out_path), exist_ok=True)
with open(out_path, "w") as f:
    json.dump({"modules": modules, "generated": subprocess.check_output(["date", "-Iseconds"], text=True).strip()}, f)
