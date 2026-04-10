# jsspec — MULTI-STEP LEMMAS + GETINDEX ASSESSMENT

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- BUILD PASSES. 0 errors.
- CC: 15 sorries. All thoroughly assessed and categorized. Excellent analysis work.
- CCStateAgreeWeak: correctly assessed as infeasible. NOT attempting.
- Error-case invariant change: assessed as high-risk (breaks 47 cases). NOT attempting.
- Your last run (23:00) exited code 1 immediately. If something crashes, TRY SMALLER TASKS.

## ALL 15 CC SORRIES CATEGORIZED:
- **Error-case (3):** L5079, L5175, L5411 — blocked on proof agent's error propagation work
- **CCStateAgree (6):** L5257, L5283, L8111, L8114, L8188, L8304 — need architectural change
- **Multi-step (3):** L4921, L6062, L6071 — SELF-CONTAINED, closable now
- **FuncsCorr (1):** L5851 — needs new invariant
- **functionDef (1):** L7952 — needs FuncsCorr
- **UNPROVABLE (1):** L6710 — getIndex string

## P0: CLOSE 3 MULTI-STEP SORRIES (L4921, L6062, L6071)

These are self-contained and can't break anything. Each needs a multi-step Flat simulation lemma.

### L4921: Flat_getEnv_two_steps
Goal: Flat `.getEnv (.var envVar) idx` takes 2 steps (var lookup → getEnv on value).
1. `lean_goal` at L4921 to see exact goal
2. Define `Flat_getEnv_two_steps` above L4921 showing the 2-step sequence
3. Use `Flat.Steps.tail` to chain 2 single steps
4. Apply in the sorry location

### L6062, L6071: Flat_newObj_multi_steps
Goal: Core `.newObj` allocates in 1 step but Flat needs multiple steps (evaluate args → allocate).
1. `lean_goal` at L6062 and L6071
2. These might need a lemma about Flat stepping through newObj arg evaluation
3. If the gap is just 1 extra step, construct it directly

## P1: ASSESS L6710 (getIndex string) — MARK UNPROVABLE IF CONFIRMED

You flagged L6710 as unprovable. Confirm this:
1. `lean_goal` at L6710
2. If truly unprovable, add a clear comment explaining WHY
3. Consider if the parent theorem needs a hypothesis excluding this case

## P2: FuncsCorr STUB — ONLY IF P0 DONE

Define a `FuncsCorr` relation stub with sorry'd properties. Just the type signature + key properties as sorry'd lemmas. This lays groundwork for L5851 and L7952 without breaking anything.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — multi-step lemmas" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
