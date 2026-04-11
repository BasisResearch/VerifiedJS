# jsspec — CLOSE FuncsCorr INIT + PRESERVATION, THEN CALL CASE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 17 real sorries. ANF: 31. Total: 48.
- FuncsCorr wired into CC_SimRel (great work!).
- L1519: FuncsCorr init sorry (NEW from wiring)
- L4959: FuncsCorr preservation sorry (NEW from wiring)
- L5935 call case now has `hfuncCorr` in scope — READY TO CLOSE

## P0: CLOSE L1519 (FuncsCorr initial state)

FuncsCorr needs to hold for the initial state. The initial funcs array should be empty or match trivially. Run `lean_goal` at L1519 to see what's needed. If initial funcs are `#[]`, then FuncsCorr should be trivially true (`Array.get?` returns `none` for empty arrays).

## P1: CLOSE L4959 (FuncsCorr preservation)

After a step, funcs may or may not change. For most cases (not functionDef), funcs don't change, so `hfuncCorr' = hfuncCorr`. For functionDef, you need to show the new function entry maintains FuncsCorr.

**Strategy**: Case split on whether step changes funcs:
- Most steps: `sf'.funcs = sf.funcs` → `exact hfuncCorr`
- FunctionDef: new func added → extend FuncsCorr with the new entry

## P2: CLOSE L5935 (call non-consoleLog)

Now that `hfuncCorr` is available:
1. Extract the matching Flat.FuncDef from `hfuncCorr`
2. Show Flat call steps to the correct function body
3. Establish CC_SimRel for post-call state

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5335, L5361, L8203, L8206, L8280, L8396: CCStateAgree (6 total)
- L4986, L6143, L6154: multi-step simulation gap (3 total)
- L5154, L5253, L5492: error structural mismatch (3 total)
- L6794: semantic mismatch (UNPROVABLE)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr init L1519" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
