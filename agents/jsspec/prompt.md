# jsspec — WIRE FuncsCorr INTO CC_SimRel (CONTINUING)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 15 real sorries. ANF: 34. Total: 49.
- FuncsCorr DEFINED and filled at L1455-1483 (2 sorries closed last run — great work!).
- You're currently wiring FuncsCorr into CC_SimRel. CONTINUE THIS WORK.

## P0: ADD FuncsCorr TO CC_SimRel (CONTINUE)

CC_SimRel is defined at ~L1488. Add `FuncsCorr injMap sc.funcs sf.funcs ccFuncs` as a conjunct.

**KEY STRATEGY — DO IT INCREMENTALLY:**
1. Add FuncsCorr to CC_SimRel definition
2. This will break ALL ~30 case proofs in `closureConvert_step_simulation`
3. Fix ONE simple case first (e.g., `lit` or `var`) — just carry `hfuncCorr` through
4. For cases that don't change funcs: `exact hfuncCorr` (or destructure from hypothesis)
5. Use `sorry` for complex cases (functionDef, call) while fixing simple ones
6. Verify each case compiles before moving to next

**DO NOT try to fix all 30 cases at once.** Fix simple ones, sorry complex ones.

## P1: USE FuncsCorr TO CLOSE L5930 (call non-consoleLog)

After P0 is done and FuncsCorr is available in the simulation relation:
1. Extract matching Flat.FuncDef from FuncsCorr
2. Show the Flat call steps to the correct function
3. Establish CC_SimRel for the post-call state

## P2: L8042 (functionDef) — May need multi-step, possibly still blocked

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5327, L5353, L8199, L8202, L8276, L8392: CCStateAgree (6 total)
- L4978, L6138, L6149: multi-step simulation gap (3 total)
- L5146, L5245, L5484: error structural mismatch (3 total)
- L6789: semantic mismatch (UNPROVABLE)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr wiring into CC_SimRel" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
