# jsspec — ERROR-CASE ASSESSMENT + FUNCCORR GROUNDWORK

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 15 sorries. All thoroughly assessed and categorized. EXCELLENT analysis work.
- Supervisor removed 4 dead-code sorries from ANF. Total: 56 (was 60).
- Error propagation IS DONE in Flat/Semantics.lean — compound expressions now DROP wrapper on error.

## ALL 15 CC SORRIES — CATEGORIZED:
- **Error-case (3):** L5079, L5175, L5411 — MAY be closable now that error propagation is done
- **CCStateAgree (6):** L5257, L5283, L8111, L8114, L8188, L8304 — architectural
- **Multi-step (3):** L4921, L6062, L6071 — need multi-step simulation
- **FuncsCorr (1):** L5851 — needs new invariant
- **functionDef (1):** L7952 — needs FuncsCorr
- **UNPROVABLE (1):** L6710 — getIndex string

## P0: RE-ASSESS ERROR-CASE SORRIES (L5079, L5175, L5411)

Error propagation is DONE. For all compound expressions, `Flat.step?` now drops the compound wrapper when a sub-expression produces `.error`. This means:

When `.seq (.throw (.lit v)) b` steps with error, result is `{expr := .lit .undefined}` NOT `{expr := .seq (.lit .undefined) b}`.

**Check if this unblocks L5079, L5175, L5411:**
1. `lean_goal` at each to see current goal shape
2. Try `lean_multi_attempt` with simple tactics
3. If any become closable, close them

## P1: DEFINE FuncsCorr INVARIANT STUB

L5851 and L7952 both need a `FuncsCorr` invariant. Define the type signature:
1. `lean_goal` at L5851 to see what's needed
2. Define `FuncsCorr` as a sorry'd relation above L5851
3. Key property: Core function → corresponding Flat closure at `funcs[idx]` has right body
4. Verify it compiles with `lean_diagnostic_messages`

## P2: COMMENT CLEANUP

Update outdated "BLOCKED" comments on the 15 sorries with accurate status.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — error-case reassessment" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
