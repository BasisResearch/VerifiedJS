# proof — INTEGRATE STAGING LEMMAS + CLOSE ANF HELPER SORRIES

## CURRENT STATE: 13 ANF sorries. Target: ≤8 this run.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

## PRIORITY 0: INTEGRATE STAGING LEMMAS INTO Convert.lean

**YOU own Convert.lean** (proof user). jsspec CANNOT write to it. You MUST integrate their staging lemmas.

1. Read `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` (12KB of verified lemmas)
2. Read `VerifiedJS/ANF/Convert.lean` and find `end VerifiedJS.ANF`
3. Copy ALL lemmas from ConvertHelpers.lean into Convert.lean BEFORE `end VerifiedJS.ANF`
4. Build: `lake build VerifiedJS.ANF.Convert`
5. Fix any issues

These lemmas include `bindComplex_not_labeled`, `normalizeExpr_*_not_labeled`, continuation no-confusion lemmas (`let_k_not_labeled`, `if_k_not_labeled`, `bindComplex_k_not_labeled`), etc.

## PRIORITY 1: CLOSE HELPER SORRIES (normalizeExpr_labeled_step_sim)

3 sorries at L1563, L1595, L1612. jsspec discovered the correct approach:

**L1563 and L1595 (`| _ => sorry` in return-some/yield-some labeled cases):**
These are the non-labeled sub-expression cases for `val` in `return (some val)` / `yield (some val) delegate`.
The val is NOT `.labeled`, so normalizeExpr on val with the trivial continuation CANNOT produce `.labeled`.

The approach: for each non-labeled val constructor, show normalizeExpr produces something other than .labeled:
- Trivial values (var/lit/this): k produces `.trivial`, not `.labeled` (use `hk_triv`)
- Simple compounds (return none, yield none, break, continue): use `normalizeExpr_*_not_labeled` from staging lemmas
- Complex compounds (let, seq, if): these recurse. Need well-founded induction on `Flat.Expr.depth`.

**CRITICAL INSIGHT from jsspec**: Compound cases (let, seq, if) CAN produce `.labeled` if a sub-expression is labeled. The proof needs **induction on expression depth**, not simple exfalso.

**Recommended refactor for L1612 (`| _ => sorry -- remaining compound cases and seq`):**
This handles the remaining Flat.Expr constructors for `normalizeExpr_labeled_step_sim`.

For compound expressions: normalizeExpr recurses. If the expression itself IS the labeled case, we're already handled (the labeled case above). For non-labeled expressions, normalizeExpr decomposes into sub-expressions, and we need to show the result structure.

Try restructuring with well-founded induction:
```lean
-- Replace the | _ => sorry with individual cases:
  | var name => exfalso; ... (use normalizeExpr_var_not_labeled + hk_triv)
  | this => exfalso; ... (similar)
  | lit _ => exfalso; ... (similar)
  | «let» n r b => ... (needs induction or separate lemma)
  | seq a b => ...
  | «if» c t e => ...
  | throw _ => exfalso; ... (use throw_k_not_labeled from staging)
  | await _ => exfalso; ... (use await_k_not_labeled from staging)
  | «return» _ => ... (none case: use normalizeExpr_return_none_not_labeled; some case: recurse)
  | yield _ _ => ... (none case: use normalizeExpr_yield_none_not_labeled; some case: recurse)
  | «break» _ => exfalso; (use normalizeExpr_break_not_labeled')
  | «continue» _ => exfalso; (use normalizeExpr_continue_not_labeled')
  | call _ _ => exfalso; (uses bindComplex_not_labeled)
  | getProp _ _ => exfalso; (uses bindComplex_not_labeled)
  | getIndex _ _ => exfalso; (uses bindComplex_not_labeled)
  | assign _ _ => exfalso; (uses bindComplex_not_labeled)
  | while_ _ _ => exfalso; (already proved — copy from L1596-1600)
  | tryCatch _ _ _ _ => exfalso; (already proved — copy from L1601-1611)
  | forIn | forOf | newObj _ _ | setProp _ _ _ | setIndex _ _ _ | objectLit _ | arrayLit _ | functionDef _ _ _ _ _ => exfalso; (use no-confusion)
```

## PRIORITY 2: MAIN THEOREM STRUCTURAL CASES

After helper sorries are closed, work on `anfConvert_step_star`:
- L1692 (let): Use the var-found case (L1654-1684) as template
- L1694 (seq): If a is value → skip to b. If a steps → inner step.
- L1696 (if): Branch on condition trivial value

## SKIP: L1738 (break), L1740 (continue) — semantic mismatch, leave as sorry

## WORKFLOW
1. Integrate staging lemmas into Convert.lean → build
2. Use `lean_goal` at sorry lines → `lean_multi_attempt` → edit
3. Build after each change: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
4. Log progress to agents/proof/log.md
