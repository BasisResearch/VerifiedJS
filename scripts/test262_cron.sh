#!/bin/bash
cd /opt/verifiedjs
export ELAN_HOME=/opt/elan PATH=/opt/elan/bin:/usr/local/bin:$PATH

mkdir -p logs

# Run test262 sample
OUT=$(bash scripts/run_test262_compare.sh --fast --sample 200 --seed stats 2>&1)

# Parse into JSON
python3 -c "
import json, re, sys, collections
from datetime import datetime

text = sys.stdin.read()
results = []
cats = collections.Counter()
cat_examples = collections.defaultdict(list)

for line in text.splitlines():
    m = re.match(r\"(TEST262_\w+)\s+(.*?)(?:\s+::\s+(.*))?$\", line)
    if not m: continue
    status = m.group(1).replace(\"TEST262_\",\"\").lower()
    path = m.group(2)
    detail = m.group(3) or \"\"
    # Extract category from path
    parts = path.replace(\"tests/test262/test/\",\"\").split(\"/\")
    cat = parts[0] if parts else \"other\"
    subcat = parts[1] if len(parts) > 1 else \"\"
    results.append({\"status\": status, \"path\": path, \"detail\": detail, \"cat\": cat, \"subcat\": subcat})
    cats[f\"{cat}/{subcat}\"] += 1
    key = f\"{status}:{cat}\"
    if len(cat_examples[key]) < 3:
        cat_examples[key].append(path.split(\"/\")[-1])

pass_count = sum(1 for r in results if r[\"status\"]==\"pass\")
fail_count = sum(1 for r in results if r[\"status\"]==\"fail\")
skip_count = sum(1 for r in results if r[\"status\"]==\"skip\")
xfail_count = sum(1 for r in results if r[\"status\"]==\"xfail\")

output = {
    \"timestamp\": datetime.utcnow().isoformat()+\"Z\",
    \"pass\": pass_count, \"fail\": fail_count, \"skip\": skip_count, \"xfail\": xfail_count,
    \"total\": len(results),
    \"results\": results,
}
json.dump(output, open(\"/opt/verifiedjs/logs/test262_results.json\",\"w\"))

# Also append to history
hist = []
try: hist = json.load(open(\"/opt/verifiedjs/logs/test262_history.json\"))
except: pass
hist.append({\"ts\": output[\"timestamp\"], \"pass\": pass_count, \"fail\": fail_count, \"skip\": skip_count, \"xfail\": xfail_count, \"total\": len(results)})
hist = hist[-100:]  # keep last 100
json.dump(hist, open(\"/opt/verifiedjs/logs/test262_history.json\",\"w\"))

# Summary for agents
summary = f\"# Test262: {pass_count} pass, {fail_count} fail, {skip_count} skip, {xfail_count} xfail / {len(results)} total\n\n\"
by_cat = collections.defaultdict(lambda: collections.Counter())
for r in results:
    by_cat[r[\"cat\"]][r[\"status\"]] += 1
for cat in sorted(by_cat):
    c = by_cat[cat]
    summary += f\"- **{cat}**: {c.get(\"pass\",0)} pass, {c.get(\"fail\",0)} fail, {c.get(\"skip\",0)} skip\n\"
open(\"/opt/verifiedjs/logs/test262_summary.md\",\"w\").write(summary)

print(f\"pass={pass_count} fail={fail_count} skip={skip_count} total={len(results)}\")
" <<< "$OUT"

chmod 644 /opt/verifiedjs/logs/test262_*.json /opt/verifiedjs/logs/test262_*.md 2>/dev/null
