# jsspec — INTEGRATE LABELED INVERSION INTO ANF, CLOSE BREAK/CONTINUE

## STATUS: 63 grep sorries. Labeled inversion COMPLETE (all 32 cases ✓). EXCELLENT WORK.

## PRIORITY 0: Write `break_step_sim` and `continue_step_sim` helpers

The ANF break/continue sorries at ANFConvertCorrect.lean:L1948-1950 are the HIGHEST VALUE
targets you can enable. The labeled case (L1925) is already proved using
`normalizeExpr_labeled_step_sim`. Write the analogous helper for break/continue.

Your `anf_break_sim.lean` already has the base case analysis. The fundamental difficulty
you identified (dead code after break in seq context) is REAL. But the solution is:

**Break/continue ONLY appear at ANF level** (normalizeExpr produces them as `.break`/`.continue`
directly). The ANF `step?` for break/continue simply emits `.error ("break:" ++ label)`.
On the Flat side, `normalizeExpr (.break label) k = .break label` (you proved this).

So the proof needs to show:
1. If `sa.expr = .break label`, then `ANF.step?` produces `(.error ("break:" ++ label), terminal_state)`
2. The Flat state steps to produce the same observable trace
3. The key: what is `sf.expr` when `sa.expr = .break label`?
   - From SimRel: `normalizeExpr sf.expr k = sa.expr` up to some relationship
   - If `sf.expr = .break label` directly, Flat steps once producing `.error` ✓
   - If `sf.expr` is compound containing break in head position: use break inversion

Write the helper in staging, then provide exact theorem statement + proof to proof agent.

```lean
theorem normalizeExpr_break_step_sim
    (sf : Flat.State) (k : ...) (n m : Nat) (label : String)
    (hk_triv : ...) (hnorm : ...) (hewf : ...) :
    ∃ evs sf', Flat.steps? sf evs sf' ∧
      observableTrace [.error ("break:" ++ label)] = observableTrace evs ∧
      ... -- SimRel for terminal state
```

## PRIORITY 1: Close remaining 5 break inversion cases

Still need: call, newObj, makeEnv, objectLit, arrayLit in `normalizeExpr_break_or_k`.

You already designed the `normalizeExprList_break_or_k` helper. Write it and close all 5.

## PRIORITY 2: Stage ANF exfalso proofs using labeled inversion

Your labeled inversion enables closing ANF sorries via exfalso for constructors that
CANNOT produce `.labeled` output. The proof agent needs these as ready-to-paste code.

Write in staging: for each of the ANF constructors that have sorry (throw L1916, tryCatch L1918,
return L1920, yield L1922, await L1924), show which ones can be closed via
`normalizeExpr_not_labeled_of_no_head_no_k` + exfalso if the ANF step assumes labeled output.

Wait — check first: do any of these ANF cases ASSUME labeled output? Read L1905-1924 carefully.
The throw case at L1916 uses `all_goals sorry` after case splitting on `evalTrivial`. These
are about throw stepping, not about labeled. So labeled inversion may not apply directly here.

Focus: which ANF sorries CAN be closed with your inversion lemmas? Document precisely.

## FILES: `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging), `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md
