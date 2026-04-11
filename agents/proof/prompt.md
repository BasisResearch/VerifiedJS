# proof — FIX TERMINATION IN hasAbruptCompletion, THEN UNCOMMENT NoNestedAbrupt

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, exit.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 40 real sorries. CC: 15. Total: 55.
- hasAbruptCompletion_step_preserved UNCOMMENTED (good!) but has **3 ERRORS**:
  1. **TERMINATION FAILURE** at L13962: Lean cannot infer structural recursion. 42 recursive calls, only 7 proved decreasing.
  2. **Eq.refl constructor** at L14270 and L14302: "Insufficient number of fields for ⟨...⟩ constructor: Constructor Eq.refl does not have explicit fields, but 2 were provided"

## P0: FIX TERMINATION IN hasAbruptCompletion_step_preserved (L13962)

The proof makes recursive calls where `sf'.expr` (from `hstep`) is NOT syntactically a sub-term of `e`. Lean can't prove termination.

**FIX APPROACH — well-founded recursion on sizeOf:**

Add after line 13968 (after `: hasAbruptCompletion sf'.expr = false := by`):
```
termination_by sizeOf e
```

Then for each recursive call where Lean complains, add a `have` proving `sizeOf target < sizeOf e`. After `cases e with | seq lhs rhs => ...`, when you recursively call on a sub-expression extracted from `hstep`, show:
```lean
have hdec : sizeOf sub_expr < sizeOf (Flat.Expr.seq lhs rhs) := by
  simp [Flat.Expr.sizeOf_eq]; omega
```

**ALTERNATIVE if sizeOf is hard**: Use `decreasing_by` with explicit proofs:
```lean
termination_by sizeOf e
decreasing_by all_goals (simp_all [Flat.Expr]; omega)
```

If even that fails, TEMPORARILY use:
```lean
termination_by sizeOf e
decreasing_by all_goals sorry
```
This adds sorries but unblocks the rest. Count: note how many `decreasing_by sorry` instances.

## P0b: FIX Eq.refl ERRORS (L14270, L14302)

These are `⟨rfl, rfl⟩` constructions where the anonymous constructor doesn't match. Replace `⟨rfl, rfl⟩` with explicit `Eq.refl` or use `exact ⟨rfl, rfl⟩` → `constructor <;> rfl` or `simp`.

Run `lean_goal` at L14270 to see what the goal type is, then fix the constructor usage.

## P1: UNCOMMENT NoNestedAbrupt_step_preserved (L14414)

After P0 is fixed, uncomment the proof at L14414-L14920 (same pattern as hasAbruptCompletion):
1. Delete the `sorry` at L14414
2. Change `/-obtain` at L14415 to `obtain`
3. Delete the closing `-/` (find it with search)

**WARNING**: This proof will have the SAME termination issue. Apply the same `termination_by sizeOf` fix immediately.

## P2: COMPOUND ERROR PROP (L11832, L11838, L12005, L12011, L12163, L12169) — only after P0+P1

## SKIP: labeled_branch (blocked), CC, while/tryCatch, if_branch, anfConvert_step_star

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — fix termination L13962" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
