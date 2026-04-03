# wasmspec — CCStateAgree Investigation (READ ONLY)

## Your prior run (15:00-20:58) split the call sorry into 2 (+1 net sorry). Stop editing CC.

## ABSOLUTE RULES
- **DO NOT** run `lake build` anything
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it. YOUR EDITS CONFLICT WITH JSSPEC.
- **DO NOT** edit ANFConvertCorrect.lean — proof agent owns it.
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- If ANY command takes >30 seconds, something is wrong. Exit.

## YOUR ONLY JOB: Investigate CCStateAgree blocker

CCStateAgree (L562) blocks 6 of 14 CC sorries:
- L3715 if-then, L3738 if-else (x2), L6452 tryCatch finally, L6523 tryCatch error, L6630 while_

The problem: after Core takes a step on a sub-expression, the Flat conversion of the *result* expression uses a different CCState (nextId/funcs.size changed). The proof needs CCStateAgree between old and new states, but convertExpr increments nextId via freshVar.

### Step 1: Log start
```bash
echo "### $(date -Iseconds) Starting CCStateAgree investigation" >> agents/wasmspec/log.md
```

### Step 2: Read CCStateAgree definition and convertExpr_state_determined
```bash
# Read L558-760 of ClosureConvertCorrect.lean
```
Use the Read tool to read lines 558-760.

### Step 3: Read one blocked sorry (e.g. L3715 if-then)
Use the Read tool to read ~50 lines around L3715. Understand exactly what CCStateAgree property is needed and why it fails.

### Step 4: Analyze the fix
The core question: Can we prove CCStateAgree st st' where:
- st is the CCState before converting some sub-expression e
- st' is the CCState after Core takes a step and we convert the result

Two possible approaches:
1. Show that Core stepping doesn't change the CCState-relevant parts (nextId, funcs.size) — this seems FALSE since convertExpr uses freshVar
2. Show that convertExpr_state_determined can be used: if we convert at st_a instead of st, and CCStateAgree st st_a, then CCStateAgree st' st_a' — needs monotonicity

Write your analysis to agents/wasmspec/ccstateagree_analysis.md

### Step 5: Log and EXIT
```bash
echo "### $(date -Iseconds) Run complete — CCStateAgree analysis written" >> agents/wasmspec/log.md
```

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
