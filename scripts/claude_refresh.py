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
        # Child: become the claude process
        os.setsid()
        os.dup2(slave, 0)
        os.dup2(slave, 1)
        os.dup2(slave, 2)
        os.close(master)
        os.close(slave)
        os.execvp("claude", ["claude"])

    # Parent: interact with claude
    os.close(slave)
    output = b""
    start = time.time()

    while time.time() - start < 30:
        r, _, _ = select.select([master], [], [], 1.0)
        if r:
            try:
                data = os.read(master, 4096)
                output += data
                text = output.decode("utf-8", errors="replace")

                # Trust dialog
                if "trust" in text.lower() and ("yes" in text.lower() or "1." in text):
                    time.sleep(0.5)
                    os.write(master, b"1\n")  # Select "Yes, I trust"
                    output = b""
                    continue

                # Claude is ready (shows prompt or greeting)
                if any(x in text for x in ["Claude", "How can", "help you", "❯", ">"]):
                    time.sleep(0.5)
                    os.write(master, b"hi\n")
                    time.sleep(2)
                    # Read response
                    r2, _, _ = select.select([master], [], [], 5)
                    if r2:
                        resp = os.read(master, 4096).decode("utf-8", errors="replace")
                        print(f"Response: {resp[:100]}")
                    os.write(master, b"/exit\n")
                    time.sleep(1)
                    break

            except OSError:
                break

    os.close(master)
    os.waitpid(pid, 0)
    print("Done - token should be refreshed")

if __name__ == "__main__":
    refresh_claude_auth()
