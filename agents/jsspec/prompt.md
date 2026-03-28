# jsspec — INTEGRATE STAGING LEMMAS INTO SOURCE FILES

## STATUS: Your lemmas are stuck in `.lake/_tmp_fix/` — they are USELESS there. The proof agent CANNOT import them.

## CRITICAL: BUILD IS BROKEN
`EmitCorrect.lean:60` has a type mismatch — the proof agent is fixing this. DO NOT touch Proofs/*.lean files. Focus on your own deliverables.

## PRIORITY 0: Move no-confusion lemmas into VerifiedJS/ANF/Convert.lean

Your lemmas from `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` need to go into `VerifiedJS/ANF/Convert.lean` BEFORE `end VerifiedJS.ANF`.

Key lemmas to integrate:
- `bindComplex_not_labeled`
- `normalizeExpr_return_none_not_labeled`
- `normalizeExpr_yield_none_not_labeled`
- `normalizeExpr_break_not_labeled'`
- `normalizeExpr_continue_not_labeled'`
- `normalizeExpr_var_not_labeled`
- `normalizeExpr_this_not_labeled`
- `normalizeExpr_lit_not_labeled`
- `return_some_k_not_labeled`
- `throw_k_not_labeled`
- `await_k_not_labeled`
- `yield_some_k_not_labeled`
- `bindComplex_produces_let`
- All the `normalizeExpr_*'` simp lemmas

**Steps:**
1. Read `VerifiedJS/ANF/Convert.lean` to find `end VerifiedJS.ANF`
2. Read `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` to get the lemma code
3. Insert all lemmas BEFORE `end VerifiedJS.ANF`
4. Build: `lake build VerifiedJS.ANF.Convert`
5. Fix any issues

## PRIORITY 1: ExprWellFormed inversion lemma

The proof agent needs:
```lean
theorem ExprWellFormed.return_some_inner {v : Flat.Expr} {env : Flat.Env}
    (h : ExprWellFormed (.return (some v)) env) : ExprWellFormed v env
```

Find where `ExprWellFormed` is defined (probably in `Flat/Semantics.lean` or similar), then add this inversion lemma there.

## PRIORITY 2: Compound normalizeExpr no-confusion lemmas

Write these compound cases that the proof agent needs (or they may already be in your staging):
```lean
@[simp] theorem normalizeExpr_let_not_labeled ...
@[simp] theorem normalizeExpr_seq_not_labeled ...
@[simp] theorem normalizeExpr_if_not_labeled ...
@[simp] theorem normalizeExpr_throw_not_labeled ...
@[simp] theorem normalizeExpr_await_not_labeled ...
```

Use the same pattern from your staging file.

## DO NOT edit ANFConvertCorrect.lean or ClosureConvertCorrect.lean or EmitCorrect.lean or EndToEnd.lean
## You CAN edit: VerifiedJS/ANF/Convert.lean, VerifiedJS/Flat/Semantics.lean, VerifiedJS/Core/*.lean
## Log to agents/jsspec/log.md
