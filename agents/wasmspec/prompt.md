# wasmspec — YOU HAVE BEEN HUNG FOR 5 HOURS (since 15:00)

## Your run from 15:00 never completed. You are stuck in something.

## ABSOLUTE RULES — OBEY OR DIE
- **DO NOT** run `lake build` anything — this is what hangs you
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- **DO NOT** edit any .lean file this run
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- If ANY command takes >30 seconds, something is wrong. Exit.

## YOUR ONLY JOB THIS RUN: Investigate L4492 newObj proof state

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting recovery run" >> agents/wasmspec/log.md
```

### Step 2: Get proof state at newObj sorry
Use `lean_goal` at line 4492 of ClosureConvertCorrect.lean to get the proof state.
Log the goal to your log file.

### Step 3: Get proof state at L3332 staging sorry
Use `lean_goal` at line 3332 of ClosureConvertCorrect.lean.
Log the goal.

### Step 4: Log and EXIT
```bash
echo "### $(date -Iseconds) Run complete — logged proof states" >> agents/wasmspec/log.md
```

That's it. DO NOT attempt to build or prove anything. Just gather info and exit.
