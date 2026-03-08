#!/usr/bin/env python3
from __future__ import annotations

import json
import os
import re
import subprocess
import time
from datetime import datetime, timezone
from pathlib import Path
from typing import Dict, List

from flask import Flask, Response, jsonify, request

ROOT = Path(os.environ.get("VERIFIEDJS_ROOT", Path(__file__).resolve().parents[2]))
AGENT_LOGS_DIR = ROOT / "agent_logs"
LOCKS_DIR = ROOT / ".agent_locks"
WORKTREES_DIR = ROOT / ".worktrees"
TASKS_FILE = ROOT / "TASKS.md"

AGENT_LOG_RE = re.compile(
    r"^agent_(\d{8}_\d{6})_r(\d+)_a(\d+)_\d+\.log$"
)


app = Flask(__name__)


def iso(ts: float) -> str:
    return datetime.fromtimestamp(ts, tz=timezone.utc).isoformat()


def tail_lines(path: Path, limit: int = 80) -> List[str]:
    if not path.exists():
        return []
    with path.open("r", encoding="utf-8", errors="replace") as fh:
        lines = fh.readlines()
    return [line.rstrip("\n") for line in lines[-limit:]]


def parse_tasks() -> Dict[str, object]:
    items: List[Dict[str, str]] = []
    current_section = "Uncategorized"
    if TASKS_FILE.exists():
        with TASKS_FILE.open("r", encoding="utf-8", errors="replace") as fh:
            for raw in fh:
                line = raw.rstrip("\n")
                if line.startswith("## "):
                    current_section = line[3:].strip()
                    continue
                if line.startswith("- [ ] ") or line.startswith("- [x] "):
                    done = line.startswith("- [x] ")
                    text = line[6:].strip()
                    items.append(
                        {
                            "section": current_section,
                            "state": "done" if done else "todo",
                            "text": text,
                        }
                    )
    phase_map: Dict[str, Dict[str, object]] = {}
    for item in items:
        sec = item["section"]
        if sec not in phase_map:
            phase_map[sec] = {"section": sec, "total": 0, "done": 0, "todo": 0}
        phase_map[sec]["total"] += 1
        if item["state"] == "done":
            phase_map[sec]["done"] += 1
        else:
            phase_map[sec]["todo"] += 1

    phases = list(phase_map.values())
    phases.sort(key=lambda p: p["section"])

    return {
        "items": items,
        "total": len(items),
        "done": sum(1 for i in items if i["state"] == "done"),
        "todo": sum(1 for i in items if i["state"] == "todo"),
        "phases": phases,
        "todos": [i for i in items if i["state"] == "todo"],
    }


def parse_lock_meta(lock_dir: Path) -> Dict[str, str]:
    meta_path = lock_dir / "meta.txt"
    data: Dict[str, str] = {}
    if meta_path.exists():
        with meta_path.open("r", encoding="utf-8", errors="replace") as fh:
            for row in fh:
                row = row.strip()
                if "=" in row:
                    k, v = row.split("=", 1)
                    data[k] = v
    return data


def read_locks() -> List[Dict[str, object]]:
    if not LOCKS_DIR.exists():
        return []
    rows = []
    for entry in sorted(LOCKS_DIR.iterdir()):
        if not entry.is_dir():
            continue
        meta = parse_lock_meta(entry)
        rows.append(
            {
                "id": entry.name,
                "meta": meta,
                "mtime": iso(entry.stat().st_mtime),
            }
        )
    return rows


def partition_locks(locks: List[Dict[str, object]]) -> Dict[str, List[Dict[str, object]]]:
    active: List[Dict[str, object]] = []
    completed: List[Dict[str, object]] = []
    pending_merge: List[Dict[str, object]] = []
    for lock in locks:
        status = lock.get("meta", {}).get("status", "").strip()
        if status in {"done", "completed"}:
            completed.append(lock)
        elif status == "pending_merge":
            pending_merge.append(lock)
            active.append(lock)
        else:
            active.append(lock)
    return {"active": active, "completed": completed, "pending_merge": pending_merge}


def list_agent_logs(limit: int = 25) -> List[Dict[str, object]]:
    if not AGENT_LOGS_DIR.exists():
        return []
    entries = []
    for path in AGENT_LOGS_DIR.glob("agent_*.log"):
        st = path.stat()
        m = AGENT_LOG_RE.match(path.name)
        run = None
        if m:
            run = {"stamp": m.group(1), "round": int(m.group(2)), "agent": int(m.group(3))}
        last_line = ""
        lines = tail_lines(path, limit=1)
        if lines:
            last_line = lines[0]
        entries.append(
            {
                "name": path.name,
                "size": st.st_size,
                "mtime": iso(st.st_mtime),
                "run": run,
                "last_line": last_line,
            }
        )
    entries.sort(key=lambda x: x["mtime"], reverse=True)
    return entries[:limit]


def list_supervisor_logs(limit: int = 10) -> List[Dict[str, object]]:
    if not AGENT_LOGS_DIR.exists():
        return []
    entries = []
    for path in AGENT_LOGS_DIR.glob("supervisor_round_*.log"):
        st = path.stat()
        lines = tail_lines(path, limit=1)
        entries.append(
            {
                "name": path.name,
                "size": st.st_size,
                "mtime": iso(st.st_mtime),
                "last_line": lines[0] if lines else "",
            }
        )
    entries.sort(key=lambda x: x["mtime"], reverse=True)
    return entries[:limit]


def infer_supervisor_phase(
    tasks: Dict[str, object], lock_parts: Dict[str, List[Dict[str, object]]]
) -> str:
    if lock_parts["pending_merge"]:
        return "pending_merge_resolution"
    running = [
        l
        for l in lock_parts["active"]
        if l.get("meta", {}).get("status", "in_progress") == "in_progress"
    ]
    if running:
        return "agents_running"
    if tasks.get("todo", 0) == 0:
        return "all_tasks_validated"
    return "waiting_for_next_round"


def git_status_short() -> List[str]:
    try:
        out = subprocess.check_output(
            ["git", "-C", str(ROOT), "status", "--short", "--branch"],
            text=True,
            stderr=subprocess.DEVNULL,
        )
        return out.splitlines()
    except Exception:
        return []


def snapshot() -> Dict[str, object]:
    tasks = parse_tasks()
    locks = read_locks()
    lock_parts = partition_locks(locks)
    agents_running = len(
        [
            l
            for l in lock_parts["active"]
            if l.get("meta", {}).get("status", "in_progress") == "in_progress"
        ]
    )
    pending_merge = len(lock_parts["pending_merge"])
    return {
        "timestamp": iso(time.time()),
        "paths": {
            "root": str(ROOT),
            "agent_logs": str(AGENT_LOGS_DIR),
            "locks": str(LOCKS_DIR),
            "worktrees": str(WORKTREES_DIR),
        },
        "tasks": tasks,
        "locks": locks,
        "locks_partition": lock_parts,
        "agent_logs": list_agent_logs(limit=30),
        "supervisor_logs": list_supervisor_logs(limit=12),
        "git_status": git_status_short(),
        "metrics": {
            "agents_running": agents_running,
            "pending_merge_count": pending_merge,
            "supervisor_phase": infer_supervisor_phase(tasks, lock_parts),
        },
    }


@app.after_request
def add_cors_headers(resp):
    resp.headers["Access-Control-Allow-Origin"] = "*"
    resp.headers["Access-Control-Allow-Headers"] = "Content-Type"
    return resp


@app.get("/api/health")
def health():
    return jsonify({"ok": True, "timestamp": iso(time.time())})


@app.get("/")
def root():
    return jsonify(
        {
            "service": "verifiedjs-monitor-backend",
            "ui": "http://127.0.0.1:5174",
            "endpoints": ["/api/health", "/api/snapshot", "/api/stream", "/api/log/<name>"],
        }
    )


@app.get("/api/snapshot")
def api_snapshot():
    return jsonify(snapshot())


@app.get("/api/log/<path:name>")
def api_log(name: str):
    lines = int(request.args.get("lines", "120"))
    lines = max(20, min(lines, 2000))
    safe = Path(name).name
    path = AGENT_LOGS_DIR / safe
    if not path.exists():
        return jsonify({"error": "log not found", "name": safe}), 404
    return jsonify(
        {
            "name": safe,
            "mtime": iso(path.stat().st_mtime),
            "size": path.stat().st_size,
            "lines": tail_lines(path, limit=lines),
        }
    )


@app.get("/api/stream")
def api_stream():
    def generate():
        while True:
            payload = json.dumps(snapshot(), separators=(",", ":"))
            yield f"event: snapshot\ndata: {payload}\n\n"
            time.sleep(2)

    return Response(generate(), mimetype="text/event-stream")


if __name__ == "__main__":
    host = os.environ.get("MONITOR_HOST", "127.0.0.1")
    port = int(os.environ.get("MONITOR_PORT", "5001"))
    app.run(host=host, port=port, debug=True, threaded=True)
