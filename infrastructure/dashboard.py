from flask import Flask, Response, jsonify, request, abort
import glob
import json
import os
import subprocess
import time
from pathlib import Path
from datetime import datetime

app = Flask(__name__)
PROJECT = Path("/opt/verifiedjs")
AGENTS = ["jsspec", "wasmspec", "proof", "supervisor"]
LOG_DIR = Path("/var/log/verifiedjs")


def _read(path, tail=0):
    try:
        text = Path(path).read_text()
        if tail > 0:
            return "\n".join(text.splitlines()[-tail:])
        return text
    except Exception:
        return ""


def _sorry_count():
    try:
        out = subprocess.check_output(
            ["grep", "-rc", "sorry", "--include=*.lean", "VerifiedJS/"],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL
        )
        return sum(int(l.split(":")[-1]) for l in out.strip().splitlines() if ":" in l)
    except Exception:
        return -1


def _last_run(log_text):
    runs = log_text.split("## Run:")
    return ("## Run:" + runs[-1])[:1200] if len(runs) > 1 else "(no runs yet)"


def _escape(s):
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


_md_cache = {}
_md_cache_time = {}

def _md_to_html(text):
    """Render markdown to HTML, cached for 30 seconds."""
    key = hash(text)
    now = time.time()
    if key in _md_cache and now - _md_cache_time.get(key, 0) < 30:
        return _md_cache[key]
    import markdown
    result = markdown.markdown(
        text[:3000],  # cap input to prevent slow renders
        extensions=["tables", "fenced_code", "pymdownx.tasklist", "pymdownx.magiclink"],
        extension_configs={"pymdownx.tasklist": {"custom_checkbox": True}},
    )
    _md_cache[key] = result
    _md_cache_time[key] = now
    return result


def _parse_stream_json(raw, tail=60):
    lines = raw.strip().splitlines()
    if tail:
        lines = lines[-tail * 3:]
    output = []
    for line in lines:
        line = line.strip()
        if not line:
            continue
        try:
            obj = json.loads(line)
            t = obj.get("type", "")
            if t == "assistant":
                msg = obj.get("message", {})
                for block in msg.get("content", []):
                    if block.get("type") == "text":
                        output.append(block["text"])
                    elif block.get("type") == "tool_use":
                        name = block.get("name", "?")
                        inp = block.get("input", {})
                        if name == "Bash":
                            output.append(f"$ {inp.get('command', '?')[:120]}")
                        elif name == "Read":
                            output.append(f"[read {inp.get('file_path', '?')}]")
                        elif name in ("Edit", "Write"):
                            output.append(f"[{name.lower()} {inp.get('file_path', '?')}]")
                        elif name == "Grep":
                            output.append(f"[grep '{inp.get('pattern', '?')}']")
                        else:
                            output.append(f"[{name}]")
            elif t == "tool_result":
                content = obj.get("content", "")
                if isinstance(content, str) and content.strip():
                    tl = content.strip().splitlines()
                    if len(tl) > 4:
                        output.append("\n".join(tl[:4]) + f"\n  ... ({len(tl)} lines)")
                    else:
                        output.append(content.strip())
            elif t == "result":
                r = obj.get("result", "")
                if r:
                    output.append(f"=== DONE ===\n{r[:300]}")
        except (json.JSONDecodeError, KeyError):
            if line and not line.startswith("{"):
                output.append(line)
    result_lines = "\n".join(output).splitlines()
    return "\n".join(result_lines[-tail:]) if len(result_lines) > tail else "\n".join(result_lines)


def _agent_status(name):
    try:
        out = subprocess.check_output(["pgrep", "-u", name, "-a"], text=True, stderr=subprocess.DEVNULL)
        running = "claude" in out
    except Exception:
        running = False

    pattern = str(LOG_DIR / f"{name}_*.log")
    logs = sorted(glob.glob(pattern))
    latest_log = ""
    latest_log_name = ""
    if logs:
        latest_log_name = os.path.basename(logs[-1])
        raw = _read(logs[-1])
        latest_log = _parse_stream_json(raw, tail=60) if raw.strip() else ""

    return {"running": running, "latest_log": latest_log, "latest_log_name": latest_log_name}


def _e2e_results():
    import re
    # Primary: stats CSV (updated every 15 min with fresh run)
    stats_csv = _read(PROJECT / "logs" / "stats.csv")
    if stats_csv.strip():
        lines = stats_csv.strip().splitlines()
        if len(lines) > 1:
            last = lines[-1].split(",")
            if len(last) >= 4:
                try:
                    return f"E2E: {last[2]} passed, {last[3]} failed"
                except Exception:
                    pass
    # Fallback: agent logs
    for agent in AGENTS:
        log = _read(PROJECT / "agents" / agent / "log.md")
        if "E2E:" in log:
            matches = re.findall(r'E2E:\s*\d+\s*passed.*?(?:skipped|failed)[^\n]*', log)
            if matches:
                return matches[-1].strip()
    return "E2E: waiting for first test run..."


def _recent_file_changes():
    marker = Path("/tmp/.verifiedjs_dashboard_marker")
    try:
        out = subprocess.check_output(
            ["find", ".", "-newer", str(marker), "(", "-name", "*.lean", "-o", "-name", "*.md", "-o", "-name", "*.js", ")",
             "-not", "-path", "./.lake/*", "-not", "-path", "./.git/*"],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=5
        )
        marker.touch()
        files = [f.strip().lstrip("./") for f in out.strip().splitlines() if f.strip()]
        return files[-30:]
    except Exception:
        marker.touch()
        return []




STYLE = """
* { margin:0; padding:0; box-sizing:border-box; }
body { font-family:"JetBrains Mono","SF Mono","Fira Code",monospace; background:#0d1117; color:#c9d1d9; padding:16px; }
h1 { color:#58a6ff; font-size:1.4rem; }
h2 { color:#8b949e; font-size:1rem; margin:14px 0 6px; }
h3 { color:#58a6ff; font-size:0.95rem; margin-bottom:4px; }
.header { display:flex; align-items:center; gap:16px; margin-bottom:16px; flex-wrap:wrap; }
.badge { color:#0d1117; padding:6px 14px; border-radius:6px; font-weight:bold; font-size:1rem; display:inline-block; }
.grid { display:grid; grid-template-columns:repeat(2, 1fr); gap:10px; }
.card { background:#161b22; border:1px solid #30363d; border-radius:8px; padding:12px; }
.stat { font-size:0.8rem; margin-bottom:4px; }
.alive { color:#3fb950; font-weight:bold; }
.dead { color:#484f58; }
.log { background:#0d1117; padding:8px; border-radius:4px; font-size:0.65rem; line-height:1.4;
  max-height:280px; overflow-y:auto; white-space:pre-wrap; word-break:break-word; color:#8b949e; }
.tabs { display:flex; gap:6px; margin-bottom:6px; }
.tab { padding:3px 10px; border-radius:4px; cursor:pointer; font-size:0.75rem;
  border:1px solid #30363d; background:#0d1117; color:#8b949e; transition:all 0.15s; }
.tab:hover { border-color:#58a6ff; color:#c9d1d9; }
.tab.active { background:#58a6ff; color:#0d1117; border-color:#58a6ff; }
.tab-content { display:none; }
.tab-content.active { display:block; }
.metrics { display:flex; gap:10px; margin:10px 0; flex-wrap:wrap; }
.metric { background:#161b22; border:1px solid #30363d; border-radius:8px; padding:10px 16px; text-align:center; min-width:120px; }
.metric .value { font-size:1.6rem; font-weight:bold; }
.metric .label { font-size:0.7rem; color:#8b949e; margin-top:2px; }
.file-list { display:flex; flex-wrap:wrap; gap:4px; max-height:100px; overflow-y:auto; }
.file-tag { background:#1f2937; border:1px solid #30363d; border-radius:4px; padding:2px 6px;
  font-size:0.65rem; color:#8b949e; }
.file-tag.lean { border-color:#3fb950; color:#3fb950; }
.file-tag.md { border-color:#d29922; color:#d29922; }
.file-tag.js { border-color:#58a6ff; color:#58a6ff; }
.section { background:#161b22; border:1px solid #30363d; border-radius:8px; padding:12px; margin-top:10px; }
pre { font-size:0.75rem; white-space:pre-wrap; word-break:break-word; max-height:250px; overflow-y:auto; }
.md h1,.md h2,.md h3,.md h4 { color:#58a6ff; margin:8px 0 4px; }
.md h1 { font-size:1.1rem; } .md h2 { font-size:1rem; } .md h3 { font-size:0.9rem; } .md h4 { font-size:0.85rem; }
.md table { width:100%; border-collapse:collapse; font-size:0.7rem; margin:6px 0; }
.md td,.md th { padding:3px 6px; border:1px solid #30363d; text-align:left; }
.md th { background:#1f2937; color:#8b949e; }
.md code { background:#1f2937; padding:1px 4px; border-radius:3px; font-size:0.85em; }
.md pre code { background:none; padding:0; }
.md ul,.md ol { padding-left:16px; margin:4px 0; }
.md li { margin:2px 0; font-size:0.8rem; }
.md strong { color:#c9d1d9; }
.md p { margin:4px 0; font-size:0.8rem; }
.md .task-list-item { list-style:none; margin-left:-16px; }
.md .task-list-control { margin-right:6px; accent-color:#58a6ff; }
"""

JS = """
function loadETA() {
  fetch('/api/time_estimate').then(function(r){return r.json()}).then(function(data) {
    var el = document.getElementById('etaChart');
    if (!el) return;
    if (!data.length || typeof d3 === 'undefined') {
      el.innerHTML = '<span style="color:#484f58;font-size:0.75rem;padding:8px;display:block">Waiting for supervisor estimates...</span>';
      return;
    }
    el.innerHTML = '';
    var W = el.offsetWidth, H = 160, m = {t:20,r:10,b:30,l:35};
    var svg = d3.select(el).append('svg').attr('width',W).attr('height',H);

    // Compute "predicted completion" for each estimate: timestamp + hours_remaining
    // Then show how that drifts — if estimates are accurate, predicted completion converges
    var t0 = new Date(data[0].ts.replace('+00:00','Z')).getTime();
    var predicted = data.map(function(d) {
      var t = new Date(d.ts.replace('+00:00','Z')).getTime();
      return {elapsed: (t - t0) / 3600000, eta: d.hours, sorries: d.sorries, predicted_done: (t - t0) / 3600000 + d.hours};
    });

    var maxElapsed = d3.max(predicted, function(d){return d.elapsed}) || 1;
    var maxPredicted = d3.max(predicted, function(d){return d.predicted_done}) || 1;
    var maxSorries = d3.max(predicted, function(d){return d.sorries}) || 1;

    var x = d3.scaleLinear().domain([0, maxElapsed]).range([m.l, W-m.r]);
    var yP = d3.scaleLinear().domain([0, maxPredicted * 1.1]).range([H-m.b, m.t]);
    var yS = d3.scaleLinear().domain([0, maxSorries]).range([H-m.b, m.t]);

    // Predicted completion time line (orange) — should converge if estimates are accurate
    var pLine = d3.line().x(function(d){return x(d.elapsed)}).y(function(d){return yP(d.predicted_done)}).curve(d3.curveMonotoneX);
    svg.append('path').datum(predicted).attr('d',pLine).attr('fill','none').attr('stroke','#f0883e').attr('stroke-width',2);

    // ETA line (red, dashed) — raw hours remaining, should go to 0
    var eLine = d3.line().x(function(d){return x(d.elapsed)}).y(function(d){return yP(d.eta)}).curve(d3.curveMonotoneX);
    svg.append('path').datum(predicted).attr('d',eLine).attr('fill','none').attr('stroke','#f85149').attr('stroke-width',1.5).attr('stroke-dasharray','4,2');

    // Sorries line (yellow, dotted)
    var sLine = d3.line().x(function(d){return x(d.elapsed)}).y(function(d){return yS(d.sorries)}).curve(d3.curveMonotoneX);
    svg.append('path').datum(predicted).attr('d',sLine).attr('fill','none').attr('stroke','#d29922').attr('stroke-width',1).attr('stroke-dasharray','2,2');

    // Dots on latest
    var last = predicted[predicted.length-1];
    svg.append('circle').attr('cx',x(last.elapsed)).attr('cy',yP(last.predicted_done)).attr('r',4).attr('fill','#f0883e');

    // Legend — bottom row, spaced out
    var ly = H - 3;
    svg.append('line').attr('x1',m.l).attr('y1',ly-4).attr('x2',m.l+15).attr('y2',ly-4).attr('stroke','#f0883e').attr('stroke-width',2);
    svg.append('text').attr('x',m.l+18).attr('y',ly).text('predicted completion (h)').attr('fill','#f0883e').attr('font-size','8px').attr('font-family','monospace');

    svg.append('line').attr('x1',m.l+160).attr('y1',ly-4).attr('x2',m.l+175).attr('y2',ly-4).attr('stroke','#f85149').attr('stroke-width',1.5).attr('stroke-dasharray','4,2');
    svg.append('text').attr('x',m.l+178).attr('y',ly).text('ETA remaining (h)').attr('fill','#f85149').attr('font-size','8px').attr('font-family','monospace');

    svg.append('line').attr('x1',m.l+295).attr('y1',ly-4).attr('x2',m.l+310).attr('y2',ly-4).attr('stroke','#d29922').attr('stroke-width',1).attr('stroke-dasharray','2,2');
    svg.append('text').attr('x',m.l+313).attr('y',ly).text('sorries').attr('fill','#d29922').attr('font-size','8px').attr('font-family','monospace');

    // Current values — top right
    svg.append('text').attr('x',W-10).attr('y',m.t+5).text(last.eta+'h left').attr('fill','#f85149').attr('font-size','11px').attr('font-family','monospace').attr('font-weight','bold').attr('text-anchor','end');
    svg.append('text').attr('x',W-10).attr('y',m.t+17).text(last.sorries+' sorries').attr('fill','#d29922').attr('font-size','9px').attr('font-family','monospace').attr('text-anchor','end');

    // Accuracy indicator: if predicted completion is flat, estimates are good
    var first = predicted[0], mid = predicted[Math.floor(predicted.length/2)];
    var drift = Math.abs(last.predicted_done - mid.predicted_done);
    var accuracy = drift < 5 ? 'stable' : drift < 15 ? 'drifting' : 'volatile';
    var accColor = drift < 5 ? '#3fb950' : drift < 15 ? '#d29922' : '#f85149';
    svg.append('text').attr('x',W-10).attr('y',m.t+29).text(accuracy).attr('fill',accColor).attr('font-size','8px').attr('font-family','monospace').attr('text-anchor','end');

    // If predicted completion is converging, the orange line flattens — good
    // If it keeps rising, estimates are too optimistic
  });
}

function renderMd(s) {
  var NL = String.fromCharCode(10);
  var lines = s.split(NL);
  var out = '';
  for (var i = 0; i < lines.length; i++) {
    var l = lines[i].replace(/&/g,'&amp;').replace(/\x3c/g,'&lt;').replace(/>/g,'&gt;');
    if (l.match(/^### /)) l = '\x3ch4 style="color:#58a6ff;margin:6px 0 2px">' + l.slice(4) + '\x3c/h4>';
    else if (l.match(/^## /)) l = '\x3ch3 style="color:#58a6ff;margin:8px 0 3px">' + l.slice(3) + '\x3c/h3>';
    else if (l.match(/^# /)) l = '\x3ch2 style="color:#58a6ff;margin:10px 0 4px">' + l.slice(2) + '\x3c/h2>';
    else if (l.match(/^- /)) l = '\x3cdiv style="padding-left:12px;margin:1px 0">&bull; ' + l.slice(2) + '\x3c/div>';
    l = l.replace(/\*\*(.+?)\*\*/g, '\x3cstrong style="color:#c9d1d9">$1\x3c/strong>');
    l = l.replace(/`([^`]+)`/g, '\x3ccode style="background:#1f2937;padding:1px 4px;border-radius:3px;font-size:0.85em">$1\x3c/code>');
    out += l + '\x3cbr>';
  }
  return out;
}
function switchTab(agent, tab) {
  document.querySelectorAll('#' + agent + ' .tab').forEach(t => t.classList.remove('active'));
  document.querySelectorAll('#' + agent + ' .tab-content').forEach(t => t.classList.remove('active'));
  document.querySelector('#' + agent + ' .tab-' + tab).classList.add('active');
  document.querySelector('#' + agent + ' .content-' + tab).classList.add('active');
  if (tab === 'prompt') {
    var el = document.getElementById('prompt-' + agent);
    if (el && el.dataset.loaded === '0') {
      el.dataset.loaded = '1';
      fetch('/api/agent_prompt/' + agent).then(function(r) { return r.json(); }).then(function(d) {
        el.innerHTML = renderMd(d.content);
      });
    }
  }
}
const evtSource = new EventSource('/api/stream');
evtSource.onmessage = function(e) {
  const data = JSON.parse(e.data);
  // Update sorry badge
  const badges = document.querySelectorAll('.sorry-badge');
  badges.forEach(b => {{ b.textContent = 'Sorries: ' + data.sorry_count; }});
  // Update e2e badge
  const e2eBadge = document.getElementById('e2eBadge');
  if (e2eBadge) e2eBadge.textContent = data.e2e || '?';
  // Agents
  for (const [name, info] of Object.entries(data.agents)) {
    const dot = document.getElementById('status-' + name);
    if (dot) {
      dot.className = info.running ? 'stat alive' : 'stat dead';
      dot.innerHTML = info.running ? '&#9679; RUNNING' : '&#9675; idle (' + info.runs + ' runs)';
    }
    const logEl = document.getElementById('runlog-' + name);
    if (logEl && info.latest_log) {
      logEl.textContent = info.latest_log;
      logEl.scrollTop = logEl.scrollHeight;
    }
    const agentLog = document.getElementById('agentlog-' + name);
    if (agentLog && info.last_run) {
      agentLog.innerHTML = info.last_run_html || info.last_run;
    }
  }
  // File changes
  const fc = document.getElementById('file-changes');
  if (fc && data.file_changes) {
    fc.innerHTML = data.file_changes.map(f => {
      let cls = 'file-tag';
      if (f.endsWith('.lean')) cls += ' lean';
      else if (f.endsWith('.md')) cls += ' md';
      else if (f.endsWith('.js')) cls += ' js';
      return '<span class="' + cls + '">' + f + '</span>';
    }).join('') || '<span class="file-tag">no changes</span>';
  }
  // Timestamp
  const ts = document.getElementById('timestamp');
  if (ts) ts.textContent = data.timestamp;
};
"""


_page_cache = {"html": None, "time": 0}

@app.route("/")
def index():
    # Cache the full page for 15 seconds
    now = time.time()
    if _page_cache["html"] and now - _page_cache["time"] < 15:
        return _page_cache["html"]
    result = _index_impl()
    _page_cache["html"] = result
    _page_cache["time"] = now
    return result

def _index_impl():
    sorry = _sorry_count()
    now = datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    sorry_color = "#f85149" if sorry > 20 else "#d29922" if sorry > 5 else "#3fb950"

    # Lean LOC from stats.csv
    stats_csv = _read(PROJECT / "logs" / "stats.csv")
    total_loc = 0
    lean_files = 0
    if stats_csv.strip():
        last_line = stats_csv.strip().splitlines()[-1].split(",")
        try:
            total_loc = int(last_line[4]) if len(last_line) > 4 else 0
            lean_files = int(last_line[3]) if len(last_line) > 3 else 0
        except (ValueError, IndexError):
            pass
    compcert_loc = 170381  # CompCert Coq LOC
    pct_compcert = round(total_loc / compcert_loc * 100, 1) if total_loc else 0
    loc_bar = f'<span style="color:#3fb950;font-size:0.7rem">{total_loc:,} Lean LOC</span> <span style="color:#484f58;font-size:0.65rem">({pct_compcert}% of CompCert)</span>'

    def _theorems_html():
        thms = _theorems()
        if not thms:
            return '<span style="color:#484f58">no theorems found</span>'
        html = ""
        for t in thms:
            if t["status"] == "proved":
                color = "#3fb950"
                icon = "&#10003;"
            elif t["status"] == "sorry":
                color = "#d29922"
                icon = "&#9888;"
            else:
                color = "#484f58"
                icon = "&#9744;"
            priv = '<span style="color:#484f58;font-size:0.6rem">private </span>' if t.get("private") else ""
            link = f'/code/verifiedjs/tree/VerifiedJS/Proofs/{t["file"]}#n{t["line"]}'
            html += (
                f'<a href="{link}" style="text-decoration:none;display:inline-block;background:#161b22;border:1px solid #30363d;'
                f'border-radius:4px;padding:3px 8px;font-size:0.7rem;color:{color};margin:1px">'
                f'{icon} {priv}<code style="color:{color}">{_escape(t["name"])}</code>'
                f' <span style="color:#484f58;font-size:0.6rem">{_escape(t["file"])}</span></a>'
            )
        proved = sum(1 for t in thms if t["status"] == "proved")
        sorry = sum(1 for t in thms if t["status"] == "sorry")
        todo = sum(1 for t in thms if t["status"] == "todo")
        html = (f'<div style="font-size:0.75rem;color:#8b949e;margin-bottom:4px;width:100%">'
                f'<span style="color:#3fb950">&#10003; {proved} proved</span> &middot; '
                f'<span style="color:#d29922">&#9888; {sorry} sorry</span> &middot; '
                f'<span style="color:#484f58">&#9744; {todo} todo</span></div>') + html
        return html
    e2e = _escape(_e2e_results())

    agents_html = ""
    for a in AGENTS:
        log = _read(PROJECT / "agents" / a / "log.md")
        last = _escape(_last_run(log))
        runs = log.count("## Run:")
        st = _agent_status(a)
        status_class = "alive" if st["running"] else "dead"
        status_icon = "&#9679;" if st["running"] else "&#9675;"
        status_text = "RUNNING" if st["running"] else f"idle ({runs} runs)"
        run_log = _escape(st["latest_log"]) if st["latest_log"] else "(waiting for run output...)"
        # prompt rendered inline via _md_to_html

        agents_html += (
            f'<div class="card" id="{a}">'
            f'<h3>{a}</h3>'
            f'<div class="stat {status_class}" id="status-{a}">{status_icon} {status_text}</div>'
            f'<div class="tabs">'
            f'<div class="tab tab-run active" onclick="switchTab(\'{a}\',\'run\')">live output</div>'
            f'<div class="tab tab-log" onclick="switchTab(\'{a}\',\'log\')">agent log</div>'
            f'<div class="tab tab-prompt" onclick="switchTab(\'{a}\',\'prompt\')">prompt</div>'
            f'</div>'
            f'<pre class="log tab-content content-run active" id="runlog-{a}">{run_log}</pre>'
            f'<div class="log md tab-content content-log" id="agentlog-{a}">{_md_to_html(last)}</div>'
            f'<div class="log md tab-content content-prompt" style="max-height:500px" id="prompt-{a}" data-loaded="0">loading...</div>'
            f'</div>'
        )

    progress = _md_to_html(_read(PROJECT / "PROGRESS.md")[:3000])
    tasks = _md_to_html(_read(PROJECT / "TASKS.md")[:3000])
    blockers = _md_to_html(_read(PROJECT / "PROOF_BLOCKERS.md")[:2000])

    # E2E details
    # e2e loaded via JS /api/e2e_list
    file_changes = _recent_file_changes()
    fc_html = "".join(
        f'<a href="/code/verifiedjs/tree/{_escape(f)}" class="file-tag{" lean" if f.endswith(".lean") else " md" if f.endswith(".md") else " js" if f.endswith(".js") else ""}" style="text-decoration:none">{_escape(f)}</a>'
        for f in file_changes
    ) or '<span class="file-tag">no recent changes</span>'

    return f"""<!DOCTYPE html>
<html><head>
<title>VerifiedJS Agent Dashboard</title>
<meta charset="utf-8">
<style>{STYLE}</style>
</head><body>
<div class="header">
  <h1>VerifiedJS</h1>
  <span class="badge sorry-badge" style="background:{sorry_color}">Sorries: {sorry}</span>
  <span class="badge" style="background:{_build_badge_color()};font-size:0.8rem">{_build_badge_text()}</span>
  <span class="badge" style="background:#161b22;border:1px solid #30363d;color:#c9d1d9;font-size:0.8rem">{e2e}</span>
  <span style="color:#8b949e;font-size:0.7rem">{total_loc:,} LOC &middot; {loc_bar}</span>
  <a href="/code/verifiedjs/" style="color:#58a6ff;font-size:0.8rem;text-decoration:none;border:1px solid #30363d;padding:4px 10px;border-radius:4px;margin-left:auto">Browse Code</a>
  <div id="specCovBar" style="width:120px;height:20px;background:#21262d;border-radius:4px;overflow:hidden;position:relative;font-size:0.65rem;line-height:20px;text-align:center;color:#c9d1d9" title="ECMA-262 spec coverage"></div>
  <span style="color:#484f58;font-size:0.75rem" id="timestamp">{now}</span>
</div>

<h2>Agents</h2>
<div class="grid">{agents_html}</div>

<div class="section" style="margin-top:10px">
  <h2 style="margin-top:0">Recent File Changes</h2>
  <div class="file-list" id="file-changes">{fc_html}</div>
</div>

<div class="grid" style="margin-top:10px">
  <div class="card">
    <h3>Test262 Conformance</h3>
    <div id="test262stats" style="font-size:0.8rem;margin-bottom:6px">{_test262_summary()}</div>
    <div id="test262treemap" style="width:100%;height:250px;background:#0d1117;border-radius:4px;overflow:hidden"></div>
    <div id="test262detail" style="font-size:0.7rem;color:#8b949e;margin-top:4px;max-height:100px;overflow-y:auto"></div>
    <details style="margin-top:6px">
      <summary style="font-size:0.75rem;color:#58a6ff;cursor:pointer">Category Breakdown</summary>
      <div class="log md" style="max-height:200px;overflow-y:auto;margin-top:4px">{_md_to_html(_read(PROJECT / "logs" / "test262_summary.md")[:2000])}</div>
    </details>
  </div>
  <div class="card">
    <h3>E2E Test Results</h3>
    <div id="e2eList" style="display:flex;flex-wrap:wrap;gap:4px;padding:6px 0"><span style="color:#484f58">loading...</span></div>
    <div id="e2eDetail" style="display:none;margin-top:8px;background:#0d1117;border:1px solid #30363d;border-radius:4px;padding:10px"></div>
  </div>
</div>

<div class="grid" style="margin-top:10px">
  <div class="card"><h3>Sorry Report</h3><div class="log md" style="overflow-y:auto;max-height:280px">{_md_to_html(_read(PROJECT / "SORRY_REPORT.md")[:1500])}</div></div>
  <div class="card"><h3>Proof Blockers</h3><div class="log md" style="overflow-y:auto;max-height:280px">{blockers}</div></div>
</div>

<div class="grid" style="margin-top:10px">
  <div class="card"><h3>Progress</h3><div class="log md" style="overflow-y:auto;max-height:400px">{progress}</div></div>
  <div class="card"><h3>Tasks</h3><div class="log md" style="overflow-y:auto;max-height:400px">{tasks}</div></div>
</div>

<div class="card" style="margin-top:10px">
  <h3>Theorems &amp; Proofs</h3>
  <div style="display:flex;flex-wrap:wrap;gap:4px;padding:6px 0">{_theorems_html()}</div>
</div>

<div class="card" style="margin-top:10px">
  <h3>Build Status</h3>
  <div style="font-size:0.8rem;margin-bottom:4px;color:{'#3fb950' if _build_status().get('status')=='PASS' else '#f85149'}">{_escape(_build_status().get("summary",""))}</div>
  <div style="font-size:0.7rem;color:#8b949e;margin-bottom:6px">Last build: {_escape(_build_status().get("latest_log_file","unknown"))} &middot; Cron: {_build_status().get("timestamp","?")}</div>
  <details ontoggle="if(this.open && !this.dataset.loaded){{fetch('/api/build_log').then(r=>r.json()).then(d=>{{document.getElementById('buildLog').textContent=d.content;this.dataset.loaded='1'}})}}">
    <summary style="font-size:0.75rem;color:#58a6ff;cursor:pointer">Show full build output</summary>
    <pre class="log" id="buildLog" style="max-height:500px">Loading...</pre>
  </details>
</div>

<div class="card" style="margin-top:10px">
  <h3>Changes</h3>
  <div id="diffFiles" style="display:flex;flex-wrap:wrap;gap:4px;padding:6px 0"></div>
  <pre id="diffContent" class="log" style="max-height:300px;display:none"></pre>
</div>

<div class="section" style="margin-top:10px">
  <h3>Failures</h3>
  <div class="log md" style="overflow-y:auto;max-height:300px">{_md_to_html(_read(PROJECT / "FAILURES.md")[:2000])}</div>
</div>

<div class="grid" style="margin-top:10px;grid-template-columns:1fr 1fr 1fr">
  <div class="card">
    <h3>Stats Over Time</h3>
    <div id="statsChart" style="width:100%;height:130px;background:#0d1117;border-radius:4px"></div>
  </div>
  <div class="card">
    <h3>ETA</h3>
    <div id="etaChart" style="width:100%;height:160px;background:#0d1117;border-radius:4px"></div>
  </div>
  <div class="card">
    <h3>Agent Gantt Chart</h3>
    <div id="ganttChart" style="width:100%;height:130px;background:#0d1117;border-radius:4px"></div>
  </div>
</div>

<div class="card" style="margin-top:10px">
  <h3>Theorem Dependency Graph</h3>
  <div style="display:flex;align-items:center;gap:8px;margin-bottom:6px;font-size:0.7rem;color:#8b949e">
    <span style="color:#3fb950">&#9679; proved</span>
    <span style="color:#d29922">&#9679; sorry</span>
    <span style="color:#484f58">&#9679; def</span>
    <span style="margin-left:auto">Snapshot:</span>
    <input type="range" id="thmSlider" min="0" max="0" value="0" style="width:200px;accent-color:#58a6ff">
    <span id="thmSliderLabel">latest</span>
  </div>
  <div id="thmGraphContainer" style="width:100%;height:500px;background:#0d1117;border-radius:4px;overflow:hidden"></div>
</div>

<script>{JS}</script>
<script>
const AGENT_COLORS = {{'jsspec':'#58a6ff','wasmspec':'#d29922','proof':'#3fb950','supervisor':'#f85149'}};
const AGENTS = ['jsspec','wasmspec','proof','supervisor'];

function parseTs(ts) {{ return new Date(ts.replace('+00:00','Z').replace('+0000','Z')).getTime(); }}

function refreshCharts() {{
fetch('/api/stats').then(r=>r.json()).then(data => {{
  // d3 Stats line chart
  const sc = document.getElementById('statsChart');
  if (sc && data.stats.length > 1 && typeof d3 !== 'undefined') {{
    sc.innerHTML = '';
    const W = sc.offsetWidth, H = 130, m = {{t:16,r:10,b:20,l:35}};
    const svg = d3.select(sc).append('svg').attr('width',W).attr('height',H);
    const stats = data.stats;
    const x = d3.scaleLinear().domain([0,stats.length-1]).range([m.l,W-m.r]);
    const yS = d3.scaleLinear().domain([0,d3.max(stats,s=>s.sorries)||1]).range([H-m.b,m.t]);
    const yE = d3.scaleLinear().domain([0,d3.max(stats,s=>s.e2e_total)||1]).range([H-m.b,m.t]);

    // Sorries line + area
    const sorryLine = d3.line().x((s,i)=>x(i)).y(s=>yS(s.sorries)).curve(d3.curveMonotoneX);
    const sorryArea = d3.area().x((s,i)=>x(i)).y0(H-m.b).y1(s=>yS(s.sorries)).curve(d3.curveMonotoneX);
    svg.append('path').datum(stats).attr('d',sorryArea).attr('fill','#d2992220');
    svg.append('path').datum(stats).attr('d',sorryLine).attr('fill','none').attr('stroke','#d29922').attr('stroke-width',2);

    // E2E tests line + area
    const e2eLine = d3.line().x((s,i)=>x(i)).y(s=>yE(s.e2e_total)).curve(d3.curveMonotoneX);
    const e2eArea = d3.area().x((s,i)=>x(i)).y0(H-m.b).y1(s=>yE(s.e2e_total)).curve(d3.curveMonotoneX);
    svg.append('path').datum(stats).attr('d',e2eArea).attr('fill','#3fb95020');
    svg.append('path').datum(stats).attr('d',e2eLine).attr('fill','none').attr('stroke','#3fb950').attr('stroke-width',2);

    // LOC line (third metric, blue)
    const yL = d3.scaleLinear().domain([0,d3.max(stats,s=>s.lean_loc)||1]).range([H-m.b,m.t]);
    const locLine = d3.line().x((s,i)=>x(i)).y(s=>yL(s.lean_loc)).curve(d3.curveMonotoneX);
    svg.append('path').datum(stats).attr('d',locLine).attr('fill','none').attr('stroke','#58a6ff').attr('stroke-width',1.5).attr('stroke-dasharray','4,2');

    // Dots on latest
    const last = stats[stats.length-1];
    svg.append('circle').attr('cx',x(stats.length-1)).attr('cy',yS(last.sorries)).attr('r',4).attr('fill','#d29922');
    svg.append('circle').attr('cx',x(stats.length-1)).attr('cy',yE(last.e2e_total)).attr('r',4).attr('fill','#3fb950');

    // Labels
    svg.append('text').attr('x',m.l+2).attr('y',m.t-2).text('sorries: '+last.sorries).attr('fill','#d29922').attr('font-size','10px').attr('font-family','monospace');
    svg.append('text').attr('x',m.l+100).attr('y',m.t-2).text('e2e: '+(last.e2e_total||'?')+' tests').attr('fill','#3fb950').attr('font-size','10px').attr('font-family','monospace');
    svg.append('text').attr('x',W-100).attr('y',m.t-2).text('LOC: '+(last.lean_loc||'?')).attr('fill','#58a6ff').attr('font-size','10px').attr('font-family','monospace');

    // Y axes
    svg.append('text').attr('x',2).attr('y',yS(0)+4).text('0').attr('fill','#484f58').attr('font-size','8px').attr('font-family','monospace');
  }}

  // d3 Gantt chart from liveness pings (pgrep-based, every minute)
  const gc = document.getElementById('ganttChart');
  if (gc && typeof d3 !== 'undefined') {{
    fetch('/api/liveness').then(r=>r.json()).then(liveness => {{
      if (!liveness || !liveness.length) return;
      gc.innerHTML = '';
      const W = gc.offsetWidth, H = 130;
      const svg = d3.select(gc).append('svg').attr('width',W).attr('height',H);
      const allTs = liveness.map(e => parseTs(e.ts)).filter(t => !isNaN(t));
      if (allTs.length < 2) return;
      const minT = Math.min(...allTs), maxT = Math.max(...allTs);
      const x = d3.scaleLinear().domain([minT,maxT]).range([80,W-10]);
      const rowH = 28;
      AGENTS.forEach((a, row) => {{
        svg.append('text').attr('x',4).attr('y',row*rowH+18).text(a)
          .attr('fill',AGENT_COLORS[a]).attr('font-size','10px').attr('font-family','monospace');
        svg.append('line').attr('x1',80).attr('x2',W-10).attr('y1',row*rowH+22).attr('y2',row*rowH+22)
          .attr('stroke','#21262d').attr('stroke-width',1);
        let barStart = null;
        for (let i = 0; i < liveness.length; i++) {{
          const alive = liveness[i][a];
          const t = parseTs(liveness[i].ts);
          if (isNaN(t)) continue;
          if (alive && !barStart) barStart = t;
          if (!alive && barStart) {{
            svg.append('rect').attr('x',x(barStart)).attr('y',row*rowH+4)
              .attr('width',Math.max(x(t)-x(barStart),2)).attr('height',rowH-8)
              .attr('rx',3).attr('fill',AGENT_COLORS[a]+'88')
              .append('title').text(a+': '+Math.round((t-barStart)/60000)+'m');
            barStart = null;
          }}
        }}
        if (barStart) {{
          svg.append('rect').attr('x',x(barStart)).attr('y',row*rowH+4)
            .attr('width',Math.max(x(maxT)-x(barStart),2)).attr('height',rowH-8)
            .attr('rx',3).attr('fill',AGENT_COLORS[a]+'cc')
            .attr('stroke',AGENT_COLORS[a]).attr('stroke-width',1.5)
            .append('title').text(a+': running ('+Math.round((maxT-barStart)/60000)+'m)');
        }}
      }});
      for (let i = 0; i <= 5; i++) {{
        const t = minT + (maxT-minT)*i/5;
        svg.append('text').attr('x',x(t)).attr('y',H-2)
          .text(new Date(t).toLocaleTimeString([],{{hour:'2-digit',minute:'2-digit'}}))
          .attr('fill','#484f58').attr('font-size','8px').attr('font-family','monospace').attr('text-anchor','middle');
      }}
    }});
  }}
}});
}}
// Wait for d3 to load, then start charts
function waitForD3() {{ if (typeof d3 !== 'undefined') {{ refreshCharts(); loadETA(); setInterval(refreshCharts, 30000); setInterval(loadETA, 60000); }} else {{ setTimeout(waitForD3, 500); }} }}
waitForD3();

// Theorem dep graph with d3 — stable positions across slider changes
(async () => {{
  const d3src = 'https://cdn.jsdelivr.net/npm/d3@7/dist/d3.min.js';
  await new Promise(r => {{ const s = document.createElement('script'); s.src = d3src; s.onload = r; document.head.appendChild(s); }});

  const snapList = await fetch('/api/thm_snapshots').then(r=>r.json());
  const slider = document.getElementById('thmSlider');
  const sliderLabel = document.getElementById('thmSliderLabel');
  if (snapList.length > 0) {{ slider.max = snapList.length - 1; slider.value = snapList.length - 1; }}

  const container = document.getElementById('thmGraphContainer');
  const W = container.offsetWidth; const H = 500;
  const groupColors = {{'Proofs':'#bc8cff','Core':'#3fb950','Flat':'#d29922','ANF':'#f0883e','Wasm':'#f85149','Source':'#58a6ff','Runtime':'#8b949e'}};
  function nodeColor(d) {{
    if (d.sorry) return '#d29922';
    if (d.kind === 'def' || d.kind === 'instance') return '#484f58';
    const parts = (d.module||'').split('.'); return groupColors[parts[1]] || '#8b949e';
  }}

  // Persistent position map across slider changes
  const posMap = {{}};
  let svg, g, sim, linkG, nodeG;

  function initGraph() {{
    container.innerHTML = '';
    svg = d3.select(container).append('svg').attr('width', W).attr('height', H)
      .call(d3.zoom().scaleExtent([0.3, 5]).on('zoom', e => g.attr('transform', e.transform)));
    g = svg.append('g');
    svg.append('defs').append('marker').attr('id','arrow').attr('viewBox','0 0 10 10')
      .attr('refX',20).attr('refY',5).attr('markerWidth',6).attr('markerHeight',6)
      .attr('orient','auto').append('path').attr('d','M 0 0 L 10 5 L 0 10 z').attr('fill','#30363d');
    linkG = g.append('g');
    nodeG = g.append('g');
  }}

  function updateGraph(data) {{
    if (!data.nodes || !data.nodes.length) return;

    // Restore saved positions
    data.nodes.forEach(n => {{
      if (posMap[n.id]) {{ n.x = posMap[n.id].x; n.y = posMap[n.id].y; }}
    }});

    // Links
    const links = linkG.selectAll('line').data(data.edges, d => d.source + '->' + d.target);
    links.exit().remove();
    links.enter().append('line').attr('stroke','#30363d').attr('stroke-width',1).attr('stroke-opacity',0.4)
      .attr('marker-end','url(#arrow)');

    // Nodes
    const nodes = nodeG.selectAll('g.node').data(data.nodes, d => d.id);
    nodes.exit().transition().duration(300).style('opacity',0).remove();

    const enter = nodes.enter().append('g').attr('class','node').style('cursor','pointer')
      .call(d3.drag()
        .on('start',(e,d)=>{{if(!e.active)sim.alphaTarget(0.1).restart();d.fx=d.x;d.fy=d.y;}})
        .on('drag',(e,d)=>{{d.fx=e.x;d.fy=e.y;}})
        .on('end',(e,d)=>{{if(!e.active)sim.alphaTarget(0);d.fx=null;d.fy=null;}}))
      .on('click',(e,d)=>window.open('/code/verifiedjs/tree/'+d.file+'#n'+d.line,'_blank'));
    enter.append('circle');
    enter.append('text').attr('dx',10).attr('dy',3).attr('font-size','9px').attr('font-family','monospace');
    enter.append('title');

    // Update all (enter + existing)
    const all = nodeG.selectAll('g.node');
    all.select('circle')
      .transition().duration(400)
      .attr('r', d => d.kind==='theorem'||d.kind==='lemma' ? 7 : 5)
      .attr('fill', d => nodeColor(d)+'44')
      .attr('stroke', nodeColor)
      .attr('stroke-width', d => d.sorry ? 2.5 : 1.5);
    all.select('text').text(d=>d.name).attr('fill',nodeColor);
    all.select('title').text(d => d.id+(d.sorry?' (SORRY)':' (proved)')+'\\n'+d.file+':'+d.line);

    // Simulation — low alpha so it barely moves
    if (sim) sim.stop();
    sim = d3.forceSimulation(data.nodes)
      .force('link', d3.forceLink(data.edges).id(d=>d.id).distance(60).strength(0.3))
      .force('charge', d3.forceManyBody().strength(-120))
      .force('center', d3.forceCenter(W/2, H/2))
      .force('collision', d3.forceCollide(18))
      .alpha(Object.keys(posMap).length > 0 ? 0.05 : 0.8)  // gentle nudge if positions exist
      .on('tick', () => {{
        linkG.selectAll('line')
          .attr('x1',d=>d.source.x).attr('y1',d=>d.source.y)
          .attr('x2',d=>d.target.x).attr('y2',d=>d.target.y);
        nodeG.selectAll('g.node').attr('transform',d=>`translate(${{d.x}},${{d.y}})`);
        // Save positions
        data.nodes.forEach(n => {{ posMap[n.id] = {{x:n.x, y:n.y}}; }});
      }});
  }}

  initGraph();
  const latest = await fetch('/api/thm_graph').then(r=>r.json());
  updateGraph(latest);

  slider.addEventListener('input', async () => {{
    const idx = parseInt(slider.value);
    if (idx >= snapList.length) {{ sliderLabel.textContent = 'latest'; updateGraph(latest); return; }}
    const snap = snapList[idx];
    sliderLabel.textContent = snap.ts.replace('_',' ');
    const data = await fetch('/api/thm_snapshot/'+snap.name).then(r=>r.json());
    updateGraph(data);
  }});
}})();

// E2E test list (background tested, cached by compiler hash)
function loadE2E() {{
  fetch('/api/e2e_list').then(r=>r.json()).then(data => {{
    const el = document.getElementById('e2eList');
    if (!el) return;
    const tests = data.results || [];
    if (data.status === 'started' || data.status === 'running') {{
      const done = tests.filter(t => t.status !== 'UNKNOWN').length;
      el.innerHTML = `<span style="color:#8b949e;font-size:0.75rem">Running e2e tests... (${{done}}/${{tests.length || '?'}})</span>`;
      setTimeout(loadE2E, 5000);
      return;
    }}
    if (!tests.length) {{ el.innerHTML = '<span style="color:#484f58">no tests</span>'; return; }}
    const pass = tests.filter(t => t.status === 'PASS').length;
    const fail = tests.filter(t => t.status === 'FAIL').length;
    const colors = {{PASS:'#3fb950',FAIL:'#f85149',UNKNOWN:'#484f58'}};
    const icons = {{PASS:'&#10003;',FAIL:'&#10007;',UNKNOWN:'?'}};
    const header = `<div style="width:100%;font-size:0.8rem;margin-bottom:4px"><span style="color:#3fb950">${{pass}} pass</span> &middot; <span style="color:#f85149">${{fail}} fail</span> &middot; ${{tests.length}} total</div>`;
    el.innerHTML = header + tests.map(t =>
      `<span onclick="showE2E('${{t.name}}')" style="color:${{colors[t.status]||'#484f58'}};font-size:0.7rem;margin:1px 4px;cursor:pointer">${{icons[t.status]||'?'}} ${{t.name}}</span>`
    ).join('');
  }});
}}
loadE2E();

// Spec coverage bar
fetch('/api/spec_coverage').then(r=>r.json()).then(d => {{
  const bar = document.getElementById('specCovBar');
  if (bar) {{
    const pct = d.coverage_pct || 0;
    bar.innerHTML = `<div style="position:absolute;left:0;top:0;height:100%;width:${{pct}}%;background:#3fb950;border-radius:4px;transition:width 0.5s"></div><span style="position:relative;z-index:1">Spec: ${{pct}}% (${{d.total_refs||0}} refs)</span>`;
  }}
}});

// Build log live streaming
(function pollBuild() {{
  fetch('/api/build_log').then(r=>r.json()).then(d => {{
    const el = document.getElementById('buildLog');
    if (el && d.content) {{
      el.textContent = d.content;
      el.scrollTop = el.scrollHeight;
    }}
    if (d.running) setTimeout(pollBuild, 3000);
    else setTimeout(pollBuild, 30000);
  }}).catch(() => setTimeout(pollBuild, 30000));
}})();

// E2E test detail view
function showE2E(name) {{
  const detail = document.getElementById('e2eDetail');
  detail.style.display = 'block';
  detail.innerHTML = '<span style="color:#8b949e">Loading ' + name + '...</span>';
  fetch('/api/e2e/' + name).then(r => r.json()).then(d => {{
    const matchColor = d.match ? '#3fb950' : '#f85149';
    const matchIcon = d.match ? '&#10003; PASS' : '&#10007; FAIL';
    detail.innerHTML = `
      <div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px">
        <strong style="color:#c9d1d9">${{d.file}}</strong>
        <span style="color:${{matchColor}};font-weight:bold">${{matchIcon}}</span>
      </div>
      <div style="display:grid;grid-template-columns:1fr 1fr 1fr;gap:8px">
        <div>
          <div style="color:#8b949e;font-size:0.7rem;margin-bottom:4px">Source</div>
          <pre style="background:#161b22;padding:6px;border-radius:4px;font-size:0.65rem;max-height:200px;overflow:auto;color:#c9d1d9">${{d.source.replace(/</g,'&lt;')}}</pre>
        </div>
        <div>
          <div style="color:#3fb950;font-size:0.7rem;margin-bottom:4px">Expected (Node.js)</div>
          <pre style="background:#0d2818;padding:6px;border-radius:4px;font-size:0.65rem;max-height:200px;overflow:auto;color:#3fb950">${{(d.expected||'(no output)').replace(/</g,'&lt;')}}</pre>
        </div>
        <div>
          <div style="color:${{matchColor}};font-size:0.7rem;margin-bottom:4px">Actual (Wasm)</div>
          <pre style="background:${{d.match ? '#0d2818' : '#2d0b0b'}};padding:6px;border-radius:4px;font-size:0.65rem;max-height:200px;overflow:auto;color:${{matchColor}}">${{(d.actual||'(no output)').replace(/</g,'&lt;')}}</pre>
        </div>
      </div>`;
  }}).catch(e => {{
    detail.innerHTML = '<span style="color:#f85149">Error: ' + e + '</span>';
  }});
}}

// Git diff view
fetch('/api/diff').then(r=>r.json()).then(data => {{
  const container = document.getElementById('diffFiles');
  const content = document.getElementById('diffContent');
  if (!data.stat && !data.untracked) {{ container.innerHTML = '<span style="color:#484f58">no changes</span>'; return; }}
  if (data.source === 'last_commit') {{
    const label = document.createElement('div');
    label.style.cssText = 'font-size:0.7rem;color:#8b949e;margin-bottom:4px;width:100%';
    label.textContent = 'Last commit: ' + (data.commit_msg || '');
    container.appendChild(label);
  }}

  // Parse stat lines
  const files = [];
  data.stat.split('\\n').forEach(line => {{
    const m = line.match(/^\s*(\S+)\s+\|\s+(\d+)\s+(\+*)([-]*)/);
    if (m) files.push({{name: m[1], changes: parseInt(m[2]), adds: m[3].length, dels: m[4].length}});
  }});
  // Add untracked
  data.untracked.split('\\n').filter(Boolean).forEach(f => {{
    files.push({{name: f, changes: 0, adds: 0, dels: 0, untracked: true}});
  }});

  if (!files.length) {{ container.innerHTML = '<span style="color:#484f58">no changes</span>'; return; }}

  files.forEach(f => {{
    const ext = f.name.split('.').pop();
    const color = f.untracked ? '#8b949e' : (f.dels > f.adds ? '#f85149' : '#3fb950');
    const bar = f.untracked ? '<span style="color:#58a6ff">new</span>' :
      '<span style="color:#3fb950">' + '+'.repeat(Math.min(f.adds, 10)) + '</span>' +
      '<span style="color:#f85149">' + '-'.repeat(Math.min(f.dels, 10)) + '</span>';
    const el = document.createElement('div');
    el.style.cssText = 'background:#161b22;border:1px solid #30363d;border-radius:4px;padding:3px 8px;font-size:0.7rem;cursor:pointer;display:inline-flex;align-items:center;gap:6px';
    el.innerHTML = '<span style="color:#c9d1d9">' + f.name.split('/').pop() + '</span> ' + bar;
    el.title = f.name + (f.untracked ? ' (new file)' : ' (+' + f.adds + ' -' + f.dels + ')');
    el.onclick = () => {{
      if (f.untracked) {{ content.textContent = 'New file: ' + f.name; content.style.display = 'block'; return; }}
      fetch('/api/diff/' + f.name).then(r=>r.json()).then(d => {{
        // Syntax highlight the diff
        let html = '';
        d.diff.split('\\n').forEach(line => {{
          if (line.startsWith('+') && !line.startsWith('+++')) html += '<span style="color:#3fb950;background:#0d2818">' + line.replace(/</g,'&lt;') + '</span>\\n';
          else if (line.startsWith('-') && !line.startsWith('---')) html += '<span style="color:#f85149;background:#2d0b0b">' + line.replace(/</g,'&lt;') + '</span>\\n';
          else if (line.startsWith('@@')) html += '<span style="color:#58a6ff">' + line.replace(/</g,'&lt;') + '</span>\\n';
          else html += line.replace(/</g,'&lt;') + '\\n';
        }});
        content.innerHTML = html;
        content.style.display = 'block';
      }});
    }};
    container.appendChild(el);
  }});
}});

// Test262 treemap
fetch('/api/test262').then(r=>r.json()).then(data => {{
  if (!data.results || !data.results.length) return;
  const container = document.getElementById('test262treemap');
  const detail = document.getElementById('test262detail');
  const W = container.offsetWidth; const H = 250;

  // Group by category
  const cats = {{}};
  data.results.forEach(r => {{
    if (!cats[r.cat]) cats[r.cat] = {{pass:0,fail:0,skip:0,xfail:0,results:[]}};
    cats[r.cat][r.status] = (cats[r.cat][r.status]||0) + 1;
    cats[r.cat].results.push(r);
  }});

  // Build treemap data
  const children = Object.entries(cats).map(([name, c]) => ({{
    name, value: c.pass+c.fail+c.skip+(c.xfail||0),
    pass: c.pass, fail: c.fail, skip: c.skip, xfail: c.xfail||0, results: c.results
  }})).sort((a,b) => b.value - a.value);

  const root = d3.hierarchy({{children}}).sum(d => d.value || 0);
  d3.treemap().size([W, H]).padding(2).round(true)(root);

  const svg = d3.select(container).append('svg').attr('width',W).attr('height',H);
  const statusColors = {{pass:'#238636',fail:'#da3633',skip:'#30363d',xfail:'#9e6a03'}};

  const cells = svg.selectAll('g').data(root.leaves()).join('g')
    .attr('transform', d => `translate(${{d.x0}},${{d.y0}})`);

  // Color by dominant status
  cells.append('rect')
    .attr('width', d => Math.max(d.x1-d.x0, 0))
    .attr('height', d => Math.max(d.y1-d.y0, 0))
    .attr('rx', 3)
    .attr('fill', d => {{
      const dd = d.data;
      if (dd.fail > dd.pass && dd.fail > dd.skip) return statusColors.fail;
      if (dd.pass > dd.fail && dd.pass > dd.skip) return statusColors.pass;
      return statusColors.skip;
    }})
    .attr('fill-opacity', 0.7)
    .attr('stroke', '#0d1117')
    .style('cursor', 'pointer');

  // Labels
  cells.append('text')
    .attr('x', 4).attr('y', 14)
    .text(d => {{
      const w = d.x1-d.x0;
      return w > 50 ? d.data.name : (w > 25 ? d.data.name.slice(0,3) : '');
    }})
    .attr('fill', '#fff').attr('font-size', '10px').attr('font-family', 'monospace');

  // Count label
  cells.append('text')
    .attr('x', 4).attr('y', 26)
    .text(d => {{
      const w = d.x1 - d.x0;
      if (w < 40) return '';
      return `${{d.data.pass}}/${{d.data.value}}`;
    }})
    .attr('fill', '#ffffffaa').attr('font-size', '9px').attr('font-family', 'monospace');

  // Click to show details
  cells.on('click', (e, d) => {{
    const dd = d.data;
    let html = `<strong>${{dd.name}}</strong>: ${{dd.pass}} pass, ${{dd.fail}} fail, ${{dd.skip}} skip<br>`;
    dd.results.filter(r => r.status === 'fail').slice(0, 10).forEach(r => {{
      const fname = r.path.split('/').pop();
      html += `<span style="color:#f85149">&#10007;</span> ${{fname}} <span style="color:#484f58">${{r.detail}}</span><br>`;
    }});
    if (dd.results.filter(r => r.status === 'fail').length > 10) {{
      html += `... and ${{dd.results.filter(r => r.status === 'fail').length - 10}} more failures`;
    }}
    detail.innerHTML = html;
  }});

  // Tooltip
  cells.append('title').text(d => `${{d.data.name}}: ${{d.data.pass}} pass, ${{d.data.fail}} fail, ${{d.data.skip}} skip`);
}});
</script>
</body></html>"""


@app.route("/api/e2e/<path:testname>")
def api_e2e_detail(testname):
    """Return test file content, expected output, and compiler output."""
    import re as _re
    if ".." in testname:
        abort(403)
    test_path = PROJECT / "tests" / "e2e" / testname
    if not test_path.exists() or not testname.endswith(".js"):
        abort(404)
    source = test_path.read_text()
    # Get expected output (node.js) — stdout only
    try:
        expected = subprocess.check_output(
            ["node", str(test_path)],
            text=True, stderr=subprocess.DEVNULL, timeout=5,
            cwd=str(PROJECT)
        ).strip()
    except subprocess.TimeoutExpired:
        expected = "(timeout)"
    except Exception as e:
        expected = f"(error: {e})"
    # Get compiler output (try using existing wasm or compile fresh)
    wasm_path = test_path.with_suffix(".wasm")
    actual = ""
    compile_ok = False
    compiler_bin = PROJECT / ".lake" / "build" / "bin" / "verifiedjs"
    try:
        compile_out = subprocess.check_output(
            [str(compiler_bin), str(test_path), "-o", str(wasm_path)],
            text=True, stderr=subprocess.STDOUT, timeout=30,
            cwd=str(PROJECT),
            env={**os.environ, "ELAN_HOME": "/opt/elan", "PATH": "/opt/elan/bin:/usr/local/bin:/usr/bin:/bin"}
        )
        compile_ok = True
    except Exception as e:
        compile_out = str(e)
    if compile_ok and wasm_path.exists():
        try:
            actual = subprocess.check_output(
                ["wasmtime", str(wasm_path)],
                text=True, stderr=subprocess.STDOUT, timeout=5
            ).strip()
        except Exception as e:
            actual = f"(wasmtime error: {e})"
    else:
        actual = "(compile failed)"
    return jsonify({
        "file": testname,
        "source": source,
        "expected": expected,
        "actual": actual,
        "compile_ok": compile_ok,
        "compile_out": compile_out[:2000] if compile_ok else compile_out[:2000],
        "match": expected == actual,
    })


_e2e_cache = {"hash": None, "results": [], "running": False}

def _run_e2e_tests():
    """Background: run all e2e tests and cache results."""
    compiler = PROJECT / ".lake" / "build" / "bin" / "verifiedjs"
    e2e_dir = PROJECT / "tests" / "e2e"
    if not compiler.exists() or not e2e_dir.exists():
        _e2e_cache["running"] = False
        return

    import hashlib
    try:
        h = hashlib.md5(compiler.read_bytes()[:4096]).hexdigest()[:12]
    except Exception:
        h = "unknown"

    js_files = sorted(e2e_dir.glob("*.js"))
    results = []
    for f in js_files:
        # Node: capture stdout only, ignore stderr
        try:
            expected = subprocess.check_output(
                ["node", str(f)], text=True, stderr=subprocess.DEVNULL, timeout=5, cwd=str(PROJECT)
            ).strip()
        except Exception:
            expected = ""

        # Compile
        wasm = Path("/tmp") / f"e2e_{f.stem}.wasm"
        status = "FAIL"
        try:
            subprocess.check_output(
                [str(compiler), str(f), "-o", str(wasm)],
                text=True, stderr=subprocess.DEVNULL, timeout=15, cwd=str(PROJECT)
            )
            # Run wasm: capture stdout only
            try:
                actual = subprocess.check_output(
                    ["wasmtime", str(wasm)], text=True, stderr=subprocess.DEVNULL, timeout=5
                ).strip()
                status = "PASS" if actual == expected else "FAIL"
            except subprocess.CalledProcessError:
                status = "FAIL"
            except subprocess.TimeoutExpired:
                status = "FAIL"
        except Exception:
            status = "FAIL"

        results.append({"name": f.name, "status": status})

    _e2e_cache["hash"] = h
    _e2e_cache["results"] = results
    _e2e_cache["running"] = False


@app.route("/api/e2e_list")
def api_e2e_list():
    """Return e2e test results, cached by compiler binary hash."""
    compiler = PROJECT / ".lake" / "build" / "bin" / "verifiedjs"
    if not compiler.exists():
        return jsonify({"results": [], "status": "no_compiler"})

    import hashlib
    try:
        h = hashlib.md5(compiler.read_bytes()[:4096]).hexdigest()[:12]
    except Exception:
        h = "unknown"

    # Cache hit
    if _e2e_cache["hash"] == h and _e2e_cache["results"]:
        return jsonify({"results": _e2e_cache["results"], "status": "ready", "hash": h})

    # Already running
    if _e2e_cache["running"]:
        return jsonify({"results": _e2e_cache.get("results", []), "status": "running", "hash": h})

    # Start background run
    _e2e_cache["running"] = True
    import threading
    threading.Thread(target=_run_e2e_tests, daemon=True).start()
    return jsonify({"results": [], "status": "started", "hash": h})


@app.route("/api/agent_prompt/<name>")
def api_agent_prompt(name):
    if name not in AGENTS:
        abort(404)
    return jsonify({"name": name, "content": _read(PROJECT / "agents" / name / "prompt.md")})


@app.route("/api/time_estimate")
def api_time_estimate():
    csv = _read(PROJECT / "logs" / "time_estimate.csv")
    entries = []
    for line in csv.strip().splitlines()[1:]:
        parts = line.split(",")
        if len(parts) >= 3:
            try:
                entries.append({"ts": parts[0], "sorries": int(parts[1]), "hours": float(parts[2])})
            except (ValueError, IndexError):
                pass
    return jsonify(entries[-100:])


@app.route("/api/spec_coverage")
def api_spec_coverage():
    try:
        return jsonify(json.loads(_read(PROJECT / "logs" / "spec_coverage.json")))
    except Exception:
        return jsonify({"coverage_pct": 0, "total_refs": 0, "sections": []})


@app.route("/api/liveness")
def api_liveness():
    """Return agent liveness data from pgrep-based tracking."""
    csv = _read(PROJECT / "logs" / "agent_liveness.csv")
    entries = []
    for line in csv.strip().splitlines()[1:]:
        parts = line.split(",")
        if len(parts) >= 5:
            entries.append({
                "ts": parts[0],
                "jsspec": int(parts[1]),
                "wasmspec": int(parts[2]),
                "proof": int(parts[3]),
                "supervisor": int(parts[4]),
            })
    return jsonify(entries[-1440:])  # last 24h at 1/min


@app.route("/api/build_log")
def api_build_log():
    """Return latest build log content and whether build is running."""
    test_logs = PROJECT / "test_logs"
    is_running = False
    try:
        subprocess.check_output(["pgrep", "-f", "lake_build_concise"], stderr=subprocess.DEVNULL)
        is_running = True
    except Exception:
        pass
    log_content = ""
    log_file = ""
    if test_logs.exists():
        logs = sorted(test_logs.glob("lake_build_*.log"))
        if logs:
            log_file = logs[-1].name
            log_content = logs[-1].read_text()
    return jsonify({"content": log_content, "file": log_file, "running": is_running})


@app.route("/api/diff")
def api_diff():
    """Return current uncommitted changes, or last commit's diff if clean."""
    try:
        diff = subprocess.check_output(
            ["/usr/bin/git.real", "diff", "--stat"],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
        )
        full_diff = subprocess.check_output(
            ["/usr/bin/git.real", "diff"],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
        )
        untracked = subprocess.check_output(
            ["/usr/bin/git.real", "ls-files", "--others", "--exclude-standard"],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
        )
        # If no uncommitted changes, show last commit
        if not diff.strip() and not untracked.strip():
            diff = subprocess.check_output(
                ["/usr/bin/git.real", "diff", "HEAD~1", "--stat"],
                cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
            )
            full_diff = subprocess.check_output(
                ["/usr/bin/git.real", "diff", "HEAD~1"],
                cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
            )
            commit_msg = subprocess.check_output(
                ["/usr/bin/git.real", "log", "-1", "--format=%s (%ar)"],
                cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
            ).strip()
            return jsonify({"stat": diff, "diff": full_diff[:50000], "untracked": "", "source": "last_commit", "commit_msg": commit_msg})
        return jsonify({"stat": diff, "diff": full_diff[:50000], "untracked": untracked, "source": "working_tree"})
    except Exception as e:
        return jsonify({"stat": "", "diff": str(e), "untracked": "", "source": "error"})


@app.route("/api/diff/<path:filepath>")
def api_diff_file(filepath):
    """Return diff for a specific file."""
    import re as _re
    if ".." in filepath:
        abort(403)
    try:
        diff = subprocess.check_output(
            ["/usr/bin/git.real", "diff", "--", filepath],
            cwd=str(PROJECT), text=True, stderr=subprocess.DEVNULL, timeout=10
        )
        return jsonify({"file": filepath, "diff": diff})
    except Exception as e:
        return jsonify({"file": filepath, "diff": str(e)})


@app.route("/api/test262")
def api_test262():
    """Return test262 results as JSON."""
    try:
        return jsonify(json.loads(_read(PROJECT / "logs" / "test262_results.json")))
    except Exception:
        return jsonify({"pass": 0, "fail": 0, "skip": 0, "total": 0, "results": []})


@app.route("/api/test262_history")
def api_test262_history():
    try:
        return jsonify(json.loads(_read(PROJECT / "logs" / "test262_history.json")))
    except Exception:
        return jsonify([])


@app.route("/api/thm_graph")
def api_thm_graph():
    """Return theorem-level dependency graph."""
    try:
        return jsonify(json.loads(_read(PROJECT / "logs" / "thm_graph.json")))
    except Exception:
        return jsonify({"nodes": [], "edges": []})


@app.route("/api/thm_snapshots")
def api_thm_snapshots():
    """List available theorem graph snapshots."""
    snap_dir = PROJECT / "logs" / "thm_snapshots"
    if not snap_dir.exists():
        return jsonify([])
    snaps = sorted(snap_dir.iterdir())
    return jsonify([{"name": s.stem, "ts": s.stem} for s in snaps if s.suffix == ".json"])


@app.route("/api/thm_snapshot/<name>")
def api_thm_snapshot(name):
    """Return a specific theorem graph snapshot."""
    import re as _re
    if not _re.match(r"^\d{8}_\d{6}$", name):
        abort(404)
    path = PROJECT / "logs" / "thm_snapshots" / f"{name}.json"
    if not path.exists():
        abort(404)
    try:
        return jsonify(json.loads(path.read_text()))
    except Exception:
        abort(500)


@app.route("/api/dep_graph")
def api_dep_graph():
    """Return module dependency graph."""
    try:
        return jsonify(json.loads(_read(PROJECT / "logs" / "dep_graph.json")))
    except Exception:
        return jsonify({"modules": []})


@app.route("/api/stats")
def api_stats():
    """Return stats CSV and agent run history as JSON."""
    stats_csv = _read(PROJECT / "logs" / "stats.csv")
    runs_csv = _read(PROJECT / "logs" / "agent_runs.csv")
    # Parse stats
    stats = []
    for line in stats_csv.strip().splitlines()[1:]:
        parts = line.split(",")
        try:
            if len(parts) >= 9:
                # Old format: ts,sorry,e2e_pass,e2e_fail,lean_files,lean_loc,thms,thms_sorry,build
                stats.append({
                    "ts": parts[0], "sorries": int(parts[1]),
                    "e2e_total": int(parts[2]) + int(parts[3]),
                    "lean_files": int(parts[4]), "lean_loc": int(parts[5]),
                    "theorems": int(parts[6]), "build": int(parts[8]),
                })
            elif len(parts) >= 7:
                # New format: ts,sorry,e2e_total,lean_files,lean_loc,thms,build
                stats.append({
                    "ts": parts[0], "sorries": int(parts[1]),
                    "e2e_total": int(parts[2]),
                    "lean_files": int(parts[3]), "lean_loc": int(parts[4]),
                    "theorems": int(parts[5]), "build": int(parts[6]),
                })
        except (ValueError, IndexError):
            pass
    # Parse agent runs
    runs = []
    for line in runs_csv.strip().splitlines()[1:]:
        parts = line.split(",")
        if len(parts) >= 3:
            runs.append({"ts": parts[0], "agent": parts[1], "event": parts[2]})

    # Cross-reference with actually running processes to fix orphaned starts
    actually_running = set()
    for a in AGENTS:
        try:
            out = subprocess.check_output(["pgrep", "-u", a, "-a"], text=True, stderr=subprocess.DEVNULL)
            if "claude" in out:
                actually_running.add(a)
        except Exception:
            pass

    return jsonify({"stats": stats[-100:], "runs": runs[-200:], "actually_running": list(actually_running)})


@app.route("/api/stream")
def api_stream():
    def generate():
        while True:
            data = {
                "sorry_count": _sorry_count(),
                "e2e": _e2e_results(),
                "agents": {},
                "timestamp": datetime.utcnow().strftime("%H:%M:%S UTC"),
                "file_changes": _recent_file_changes(),
            }
            for a in AGENTS:
                log = _read(PROJECT / "agents" / a / "log.md")
                st = _agent_status(a)
                last = _last_run(log)
                data["agents"][a] = {
                    "running": st["running"],
                    "runs": log.count("## Run:"),
                    "last_run": last,
                    "last_run_html": _md_to_html(last),
                    "latest_log": st["latest_log"][-4000:] if st["latest_log"] else "",
                }
            yield f"data: {json.dumps(data)}\n\n"
            time.sleep(5)
    return Response(generate(), mimetype="text/event-stream",
                    headers={"Cache-Control": "no-cache", "X-Accel-Buffering": "no"})


@app.route("/api/summary")
def api_summary():
    data = {"sorry_count": _sorry_count(), "e2e": _e2e_results(), "agents": {}}
    for a in AGENTS:
        log = _read(PROJECT / "agents" / a / "log.md")
        st = _agent_status(a)
        data["agents"][a] = {"running": st["running"], "runs": log.count("## Run:"), "last_run": _last_run(log)}
    return jsonify(data)


def _build_status():
    # Primary: build_status.json from cron
    try:
        bs = json.loads(_read(PROJECT / "logs" / "build_status.json"))
    except Exception:
        bs = {"status": "UNKNOWN", "errors": [], "summary": ""}
    # Just get the filename, not the content (loaded on demand via /api/build_log)
    test_logs = PROJECT / "test_logs"
    if test_logs.exists():
        logs = sorted(test_logs.glob("lake_build_*.log"))
        if logs:
            bs["latest_log_file"] = logs[-1].name
    return bs


def _build_badge_color():
    bs = _build_status()
    return "#3fb950" if bs.get("status") == "PASS" else "#f85149" if bs.get("status") == "FAIL" else "#484f58"


def _build_badge_text():
    bs = _build_status()
    return "Build: " + bs.get("status", "?")


def _test262_summary():
    """Get latest test262 stats."""
    csv = _read(PROJECT / "logs" / "test262_history.csv")
    if not csv.strip():
        return '<span style="color:#484f58">Running first batch (hourly cron)...</span>'
    lines = csv.strip().splitlines()
    if len(lines) < 2:
        return '<span style="color:#484f58">Running first batch...</span>'
    last = lines[-1].split(",")
    if len(last) < 6:
        return '<span style="color:#484f58">Parsing error</span>'
    p, f, xf, sk, t = last[1], last[2], last[3], last[4], last[5]
    return (
        f'<span style="color:#3fb950;font-weight:bold">{p}</span> pass &middot; '
        f'<span style="color:#f85149">{f}</span> fail &middot; '
        f'<span style="color:#d29922">{xf}</span> xfail &middot; '
        f'<span style="color:#484f58">{sk}</span> skip &middot; '
        f'{t} total &middot; '
        f'<span style="color:#8b949e">{last[0].split("T")[1][:5] if "T" in last[0] else ""}</span>'
    )


def _theorems():
    """Scrape all theorems/lemmas from Proofs/ and their sorry status."""
    import re
    results = []
    proofs_dir = PROJECT / "VerifiedJS" / "Proofs"
    if not proofs_dir.exists():
        return results
    for f in sorted(proofs_dir.iterdir()):
        if not f.suffix == ".lean":
            continue
        text = f.read_text()
        lines = text.splitlines()
        fname = f.name
        for i, line in enumerate(lines):
            m = re.match(r'^(private\s+)?(theorem|lemma)\s+(\S+)', line)
            if not m:
                m2 = re.match(r'^--\s*(theorem|lemma)\s+(\S+)', line)
                if m2:
                    results.append({"name": m2.group(2), "file": fname, "line": i + 1, "status": "todo", "kind": m2.group(1)})
                continue
            name = m.group(3)
            kind = m.group(2)
            private = bool(m.group(1))
            block = "\n".join(lines[i:min(i + 20, len(lines))])
            status = "sorry" if "sorry" in block else "proved"
            results.append({"name": name, "file": fname, "line": i + 1, "status": status, "kind": kind, "private": private})
    return results


FILEBROWSER_STYLE = """
* { margin:0; padding:0; box-sizing:border-box; }
body { font-family:"JetBrains Mono","SF Mono",monospace; background:#0d1117; color:#c9d1d9; padding:16px; }
a { color:#58a6ff; text-decoration:none; }
a:hover { text-decoration:underline; }
.breadcrumb { font-size:0.85rem; margin-bottom:12px; color:#8b949e; }
.breadcrumb a { color:#58a6ff; }
.file-list { background:#161b22; border:1px solid #30363d; border-radius:8px; overflow:hidden; }
.file-row { display:flex; align-items:center; padding:8px 14px; border-bottom:1px solid #21262d; font-size:0.8rem; }
.file-row:last-child { border-bottom:none; }
.file-row:hover { background:#1c2128; }
.file-icon { margin-right:8px; width:16px; text-align:center; }
.file-name { flex:1; }
.file-size { color:#484f58; font-size:0.75rem; width:80px; text-align:right; }
.file-owner { color:#484f58; font-size:0.75rem; width:80px; text-align:center; }
.code-view { background:#161b22; border:1px solid #30363d; border-radius:8px; overflow:auto; }
.code-view pre { margin:0; padding:12px; font-size:0.75rem; line-height:1.5; }
.code-view .highlight { background:transparent !important; }
.code-view .highlight pre { background:transparent !important; color:#c9d1d9; }
.back-link { display:inline-block; margin-bottom:10px; font-size:0.85rem; }
.file-meta { font-size:0.75rem; color:#484f58; margin-bottom:8px; }
.linenodiv pre { color:#484f58 !important; background:transparent !important; text-align:right; padding-right:8px; border-right:1px solid #30363d; margin-right:8px; }
.linenodiv a { color:#484f58 !important; text-decoration:none; }
.highlighttable { width:100%; border-collapse:collapse; }
.highlighttable td { padding:0; vertical-align:top; }
.highlighttable td.code { width:100%; }
"""


@app.route("/files/")
@app.route("/files/<path:filepath>")
def file_browser(filepath=""):
    from pygments import highlight as pyg_highlight
    from pygments.lexers import get_lexer_for_filename, TextLexer
    from pygments.formatters import HtmlFormatter

    # Resolve and sanitize path
    base = PROJECT
    target = (base / filepath).resolve()
    # Prevent directory traversal
    if not str(target).startswith(str(base.resolve())):
        abort(403)
    # Skip .git and .lake internals
    rel = str(target.relative_to(base))
    if rel.startswith(".git") or "node_modules" in rel:
        abort(404)

    if target.is_dir():
        # Directory listing
        entries = []
        try:
            for item in sorted(target.iterdir(), key=lambda x: (not x.is_dir(), x.name.lower())):
                name = item.name
                if name.startswith(".git") or name == "node_modules" or name == ".cache":
                    continue
                rel_path = str(item.relative_to(base))
                is_dir = item.is_dir()
                size = ""
                owner = ""
                if not is_dir:
                    try:
                        st = item.stat()
                        size = f"{st.st_size:,}" if st.st_size < 1_000_000 else f"{st.st_size / 1_000_000:.1f}M"
                        import pwd
                        owner = pwd.getpwuid(st.st_uid).pw_name
                    except Exception:
                        pass
                icon = "📁" if is_dir else "📄"
                if name.endswith(".lean"):
                    icon = "🔷"
                elif name.endswith(".js"):
                    icon = "🟡"
                elif name.endswith(".md"):
                    icon = "📝"
                elif name.endswith(".sh"):
                    icon = "⚙️"
                display = name + "/" if is_dir else name
                entries.append(
                    f'<div class="file-row">'
                    f'<span class="file-icon">{icon}</span>'
                    f'<a class="file-name" href="/files/{rel_path}{"/" if is_dir else ""}">{_escape(display)}</a>'
                    f'<span class="file-owner">{_escape(owner)}</span>'
                    f'<span class="file-size">{size}</span>'
                    f'</div>'
                )
        except PermissionError:
            abort(403)

        # Breadcrumb
        parts = filepath.rstrip("/").split("/") if filepath else []
        bc = '<a href="/files/">root</a>'
        accumulated = ""
        for p in parts:
            if not p:
                continue
            accumulated += p + "/"
            bc += f' / <a href="/files/{accumulated}">{_escape(p)}</a>'

        return f"""<!DOCTYPE html>
<html><head><title>VerifiedJS — /{_escape(filepath)}</title><meta charset="utf-8">
<style>{FILEBROWSER_STYLE}</style></head><body>
<a class="back-link" href="/">← Dashboard</a>
<div class="breadcrumb">{bc}</div>
<div class="file-list">{"".join(entries) or '<div class="file-row" style="color:#484f58">(empty directory)</div>'}</div>
</body></html>"""

    elif target.is_file():
        # File view
        try:
            raw = target.read_text(errors="replace")
        except PermissionError:
            abort(403)

        # Syntax highlight
        try:
            if target.suffix == ".lean":
                from pygments.lexers import get_lexer_by_name
                lexer = get_lexer_by_name("lean4")
            else:
                lexer = get_lexer_for_filename(target.name)
        except Exception:
            lexer = TextLexer()
        formatter = HtmlFormatter(style="monokai", nowrap=False, cssclass="highlight", linenos="table", lineanchors="L")
        highlighted = pyg_highlight(raw, lexer, formatter)
        pygments_css = formatter.get_style_defs(".highlight")

        # Breadcrumb
        parts = filepath.split("/")
        bc = '<a href="/files/">root</a>'
        accumulated = ""
        for i, p in enumerate(parts):
            if not p:
                continue
            if i < len(parts) - 1:
                accumulated += p + "/"
                bc += f' / <a href="/files/{accumulated}">{_escape(p)}</a>'
            else:
                bc += f" / {_escape(p)}"

        # File metadata
        try:
            st = target.stat()
            import pwd
            owner = pwd.getpwuid(st.st_uid).pw_name
            meta = f"{st.st_size:,} bytes · owned by {owner} · {oct(st.st_mode)[-3:]}"
        except Exception:
            meta = ""

        parent = "/".join(filepath.split("/")[:-1])
        lines = len(raw.splitlines())

        return f"""<!DOCTYPE html>
<html><head><title>VerifiedJS — {_escape(filepath)}</title><meta charset="utf-8">
<style>{FILEBROWSER_STYLE}
{pygments_css}
.highlight {{ background:#0d1117 !important; }}
.highlight pre {{ background:#0d1117 !important; color:#c9d1d9; }}
</style></head><body>
<a class="back-link" href="/files/{parent}/">← back</a>
<div class="breadcrumb">{bc}</div>
<div class="file-meta">{_escape(meta)} · {lines} lines</div>
<div class="code-view">{highlighted}</div>
</body></html>"""

    else:
        abort(404)


if __name__ == "__main__":
    app.run(host="127.0.0.1", port=5001)
