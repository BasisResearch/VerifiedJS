# jsspec — FUNCCORR INVARIANT DEFINITION + ERROR-CASE PREP

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: Your last 2 runs exited code 1 or completed with 0 closures. KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 15 sorries. All thoroughly assessed and categorized. EXCELLENT analysis work.
- Multi-step sorries (L4921, L6062, L6071): Confirmed architecturally blocked — need N-to-M simulation.
- CCStateAgreeWeak: Correctly assessed as infeasible.
- Error-case sorries: Blocked on proof agent's Flat error propagation work (now DONE in Flat/Semantics.lean).
- **YOUR LAST RUN confirmed 0 closable sorries. Good analysis, nothing wasted.**

## ALL 15 CC SORRIES — CONFIRMED BLOCKED:
- **Error-case (3):** L5079, L5175, L5411 — blocked until error propagation extended to ANF proofs
- **CCStateAgree (6):** L5257, L5283, L8111, L8114, L8188, L8304 — architectural
- **Multi-step (3):** L4921, L6062, L6071 — need multi-step simulation
- **FuncsCorr (1):** L5851 — needs new invariant
- **functionDef (1):** L7952 — needs FuncsCorr
- **UNPROVABLE (1):** L6710 — getIndex string

## P0: DEFINE FuncsCorr INVARIANT STUB

L5851 and L7952 both need a `FuncsCorr` invariant relating Core function definitions to Flat closure representations. Define this as a sorry'd relation:

1. `lean_goal` at L5851 to see what the proof needs
2. Define `FuncsCorr` somewhere above L5851 as a relation between:
   - `Core.Env` (or the function table)
   - `Flat.State.funcs` (the Flat function array)
   - `CC.State` (the conversion state)
3. Key property: if Core calls function `f`, the corresponding Flat closure at `funcs[idx]` has the right body
4. Mark all properties as `sorry` — just establish the TYPE SIGNATURE
5. Use `lean_diagnostic_messages` to verify it compiles

This doesn't close any sorries but lays groundwork. If L5851's goal becomes clearer with the type, document what FuncsCorr needs to provide.

## P1: PREPARE ERROR-CASE INFRASTRUCTURE

The 3 error-case sorries (L5079, L5175, L5411) will become closable once the proof agent fixes the compound error cases in ANF. Prepare by:

1. `lean_goal` at L5079, L5175, L5411 to document the EXACT current goal shape
2. Write comments explaining what each needs from the ANF side
3. If any became closable due to error propagation changes, try to close them

## P2: COMMENT CLEANUP

Update the outdated "BLOCKED" comments on all 15 sorries with accurate current status from your analysis. This helps future agents.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr stub + error prep" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
