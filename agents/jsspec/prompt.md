# jsspec — WIRE FuncsCorr INTO CC_SimRel

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 14 real sorries. ANF: 40. Total: 54.
- FuncsCorr DEFINED at L1455-1483 (well done — 2 sorries closed last run).
- ALL 14 remaining CC sorries are architecturally blocked.
- Most impactful unblock: wire FuncsCorr into CC_SimRel → unblocks L5930 + L8042 = -2 sorries.

## P0: ADD FuncsCorr TO CC_SimRel (L1488)

CC_SimRel is defined at ~L1488. It currently does NOT include FuncsCorr.

**DO THIS:**
1. Run `lean_goal` or `lean_hover_info` on `CC_SimRel` at L1488 to see its current fields
2. Add `FuncsCorr injMap sc.funcs sf.funcs ccFuncs` as a conjunct (you'll need ccFuncs from the closure conversion output — check how `t.funcs` relates to the CC state)
3. For every existing case in `closureConvert_step_simulation` that constructs a `CC_SimRel` witness, add the FuncsCorr proof:
   - Most cases don't change funcs, so `exact hfuncCorr` works (where `hfuncCorr` is destructured from the hypothesis)
   - The `functionDef` case (L8036) and `call` case (L5923) are the ones that actually USE FuncsCorr

**KEY**: Start small. First just add FuncsCorr to CC_SimRel. Then fix ONE case that breaks (pick a simple one like `lit` or `var`). Verify it compiles. Then do the rest.

**WARNING**: Adding a field to CC_SimRel will break ALL ~30 case proofs. Fix them one at a time, starting with the simplest. Use `sorry` for complex cases while you work through them. Do NOT try to fix all 30 at once.

## P1: USE FuncsCorr TO CLOSE L5930 (call non-consoleLog)

After P0, L5930 has FuncsCorr available. The proof should:
1. Extract matching Flat.FuncDef from FuncsCorr
2. Show the Flat call steps to the correct function
3. Establish CC_SimRel for the post-call state

## P2: USE FuncsCorr TO CLOSE L8042 (functionDef)

After P0, L8042 needs to show FuncsCorr is maintained when adding a new function. This also needs multi-step simulation, so it may still be partially blocked.

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5327, L5353, L8199, L8202, L8276, L8392: CCStateAgree (6 total)
- L4978, L6138, L6149: multi-step simulation gap (3 total)
- L5146, L5245, L5484: error structural mismatch (3 total)
- L6789: semantic mismatch (UNPROVABLE)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr wiring into CC_SimRel" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
