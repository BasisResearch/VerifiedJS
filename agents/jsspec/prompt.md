# jsspec — ERROR-CASE CONVERTEXPR LEMMA + MULTI-STEP INFRASTRUCTURE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- BUILD PASSES. 0 errors.
- CC: 15 sorries. All assessed and categorized. Good work on the analysis.
- CCStateAgreeWeak: correctly assessed as infeasible (would break 47 cases for 6). NOT attempting.
- Error-case root cause identified: Flat unwraps .let/.assign/.seq on error but Core doesn't.

## P0: CLOSE 3 ERROR-CASE SORRIES WITH OBSERVABLE TRACE EQUIVALENCE (L5079, L5175, L5411)

Your root cause analysis was correct: after error, Flat gives `sf'.expr = sa.expr` (unwrapped) while Core gives `sc'.expr` still wrapped in .let/.assign/.seq. The `convertExpr` mismatch is real.

**NEW APPROACH**: The simulation relation should hold at the TRACE level, not expression level. After an error event:
- Both Flat and Core produce `.error msg` in the trace
- The remaining expression doesn't matter for observable behavior (program terminates with error)
- The CC simulation invariant should allow error-state divergence

**Concretely**: In the suffices block around L4886, the invariant currently requires `convertExpr sf'.expr ... = sc'.expr`. For the error case, weaken to: if the event was `.error msg`, then we only need trace equivalence, not expression correspondence.

This is a NARROWER change than CCStateAgreeWeak — it only affects the error case, not all cases.

Steps:
1. Read L4880-4930 to see the exact suffices invariant
2. Add a disjunction: `(convertExpr sf'.expr ... = sc'.expr) ∨ (∃ msg, t = .error msg ∧ <trace equivalence>)`
3. The non-error branch is exactly what exists now (no changes to 47 working cases)
4. The error branch: provided by the error-case code at L5079/L5175/L5411
5. Check if callers of the suffices result can handle the new disjunction

**WARNING**: This changes the main simulation invariant. Be VERY careful. If ANY working case breaks, revert immediately.

## P1: MULTI-STEP SIMULATION — IF P0 DONE OR BLOCKED

If the invariant change is too risky, switch to multi-step:
- L4921: Define `Flat_getEnv_two_steps` lemma
- L6062/L6071: Define `Flat_newObj_multi_steps` lemma
These are self-contained and can't break anything.

## P2: FuncsCorr STUB — ONLY IF TIME

If P0+P1 are both done, start defining the `FuncsCorr` relation as a stub with sorry'd properties. This lays groundwork for L5851 and L7952.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — error-case invariant OR multi-step" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
