# proof — COMPOUND ERROR CASES (error propagation is DONE)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Your last 3 runs exited code 1. Do ONE small task, verify, log, exit. Do NOT attempt multi-file edits or read huge file ranges.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 45 sorries. CC: 15. Lower: 0. Total: 60.
- Error propagation DONE in Flat/Semantics.lean.
- **Your last 3 runs crashed (code 1).** KEEP TASKS SMALL.

## KEY DISCOVERY: COMPOUND ERROR SORRIES ARE NOW PROVABLE

The comments at L11803-L11811 say "Flat.step? does not propagate error events" — this is OUTDATED. Error propagation WAS ADDED to Flat/Semantics.lean. Every compound case in `step?` now has:
```lean
match t with
| .error _ => let s' := pushTrace { s with expr := si.expr, ... } t; some (t, s')
| _ => let s' := pushTrace { s with expr := .compound si.expr ..., ... } t; some (t, s')
```

This means when a sub-expression produces `.error`, the compound context IS dropped and `s'.expr = si.expr` (not wrapped in the compound).

## P0: TEST AND FIX L11812 (compound HasThrowInHead)

This is the `| _ =>` catch-all in `normalizeExpr_throw_step_sim` at L11795-11812.

1. `lean_goal` at L11812 to see the exact goal
2. The proof needs to show: for compound `e` inside `.throw e`, Flat steps produce the right trace
3. With error propagation, stepping `.throw (compound e)` now propagates inner errors correctly
4. Try `lean_multi_attempt` at L11812 with:
   ```
   ["simp_all [Flat.step?, Flat.pushTrace]",
    "exact normalizeExpr_throw_compound_case _ env heap trace funcs cs arg n m hnorm' hewf hna"]
   ```
5. If the goal shape changed due to error propagation, the old proof approach at L11654-11659 (HasThrowInHead absurdity) and the trivialChain approach may apply differently now.

## P1: IF L11812 WORKS — Apply same pattern to L11969, L12142, L12300

These are the same pattern in different theorems:
- L11969: compound HasReturnInHead in `normalizeExpr_return_step_sim`
- L12142: compound HasAwaitInHead in `normalizeExpr_await_step_sim`
- L12300: compound HasYieldInHead in `normalizeExpr_yield_step_sim`

## P2: IF P1 WORKS — Try L11963, L12136, L12294 (compound inner_val)

These are the companion sorries for the `| _ => sorry -- compound inner_val` cases:
- L11963: return compound inner_val
- L12136: await compound inner_arg
- L12294: yield compound inner_val

## SKIP: Do NOT work on these
- L2983, L3004, L3025, L3046 — dead code (Steps_*_pres theorems have zero callers)
- L14100, L14648 — hasAbruptCompletion/NoNestedAbrupt (deprioritized, complex)
- L13188, L13228 — if_branch (K-mismatch blocked)
- labeled_branch sorries — wasmspec owns these

## CONCURRENCY
- wasmspec works on labeled_branch (L10333-L10706)
- jsspec works on ClosureConvertCorrect.lean only
- YOU own everything else in ANFConvertCorrect.lean

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — compound error cases" >> agents/proof/log.md`
2. Read L11795-L11812. `lean_goal` at L11812.
3. Try fixes. If one works, apply and verify with `lean_diagnostic_messages`.
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
5. EXIT. Do not continue to other tasks if P0 succeeds — save for next run.
