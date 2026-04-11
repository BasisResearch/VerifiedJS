# jsspec — CCStateAgree Path A: position-based naming

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T19:05
- CC: 12 real sorries. Total: **49** (ANF 37 + CC 12).
- proof agent is crushing it — closed 6 ANF sorries since 18:05.
- CONTINUE Path A investigation.

## REMAINING CC SORRY CLASSIFICATION (12 total):
1. **Multi-step simulation gap** (3): L5509, L6814, L6825
2. **CCStateAgree** (5): L5957, L5983, L8869, L8946, L9062
3. **CCStateAgree + tryCatch finally** (1): L8872
4. **Axiom/semantic mismatch** (1): L7465 (getIndex string) — UNPROVABLE
5. **FuncsCorr/functionDef** (1): L8712
6. **Multi-step (call)** (1): L6606

## YOUR MISSION: Investigate + implement CCStateAgree Path A

### WARNING: Monotone approach was REJECTED on 2026-03-31
**DO NOT** try simple monotone weakening.

### Path A: Position-based naming (HIGHEST IMPACT)
Make `convertExpr` state-independent for variable naming by using **position-based names** in `freshVar` instead of a global `nextId` counter.

#### Investigation steps (DO THIS FIRST if not already done):
1. Read `freshVar` in `Flat/ClosureConvert.lean` — current implementation
2. Read `CCState` definition — what fields?
3. Read `CCStateAgree` definition in ClosureConvertCorrect.lean — what does it require?
4. Count callers of `freshVar` — scope the change
5. Check if `convertExpr` threads CCState ONLY for `freshVar`, or also for func table

#### If freshVar is the ONLY reason for state threading:
- Change `freshVar` to use position encoding instead of counter
- `CCStateAgree` becomes trivially true
- **This eliminates 5+ sorries at once**

#### If CCState also tracks func table:
- Keep func table threading, but make variable naming position-based
- `CCStateAgree` only needs to track func table (simpler)

### Path B (fallback): Lazy conversion
Instead of converting both branches eagerly, change `convertExpr` for if/while to only convert the taken branch. More invasive.

### DO THIS RUN:
1. If investigation done: REPORT findings and start implementing
2. If not done: complete investigation, then start implementation if feasible
3. Even partial progress on Path A (e.g., changing freshVar) is valuable

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L5509, L6606, L6814, L6825) — needs framework redesign
- L7465 — semantic mismatch axiom
- L8712 — functionDef needs multi-step + FuncsCorr

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgree Path A" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
