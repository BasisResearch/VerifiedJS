#!/usr/bin/env python3
"""Spawn claude interactively to refresh OAuth token."""
import pty
import os
import sys
import time
import select

def refresh_claude_auth():
    master, slave = pty.openpty()
    pid = os.fork()

    if pid == 0:
        os.setsid()
        os.dup2(slave, 0)
        os.dup2(slave, 1)
        os.dup2(slave, 2)
        os.close(master)
        os.close(slave)
        os.execvp("claude", ["claude"])

    os.close(slave)
    output = b""
    start = time.time()
    sent_trust = False
    sent_hi = False
    sent_exit = False

    while time.time() - start < 45:
        r, _, _ = select.select([master], [], [], 0.5)
        if r:
            try:
                data = os.read(master, 4096)
                if not data:
                    break
                output += data
                text = output.decode("utf-8", errors="replace")
                # Strip ANSI codes for matching
                import re
                clean = re.sub(r'\x1b\[[0-9;]*[a-zA-Z]|\x1b\][^\x07]*\x07|\x1b[^[a-zA-Z]', '', text)

                print(f"[{time.time()-start:.1f}s] Got {len(data)} bytes, clean: {repr(clean[-200:])}", file=sys.stderr)

                if not sent_trust and ("trust" in clean.lower() or "Yes," in clean):
                    time.sleep(0.5)
                    os.write(master, b"\r")  # Enter = confirm default (yes)
                    sent_trust = True
                    output = b""
                    print("[SENT] trust confirmation", file=sys.stderr)
                    continue

                if not sent_hi and any(x in clean for x in ["How can", "help", "Claude", "❯"]):
                    time.sleep(1)
                    os.write(master, b"hi\r")
                    sent_hi = True
                    output = b""
                    print("[SENT] hi", file=sys.stderr)
                    continue

                if sent_hi and not sent_exit and len(clean) > 10:
                    # Wait for response
                    time.sleep(2)
                    os.write(master, b"/exit\r")
                    sent_exit = True
                    print("[SENT] /exit", file=sys.stderr)
                    time.sleep(1)
                    break

            except OSError:
                break

    os.close(master)
    try:
        os.waitpid(pid, 0)
    except:
        pass
    print("Done", file=sys.stderr)

if __name__ == "__main__":
    refresh_claude_auth()
