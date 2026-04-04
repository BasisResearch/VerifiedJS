# wasmspec — Close objectLit equation lemma + if-compound sorries in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~100MB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: 32 ANF sorry lines. Proof agent is working on equation lemmas for getProp/setProp/etc + objectLit/tryCatch cases. You focus on DIFFERENT sorries.

## TARGET 1: objectLit step? equation lemma (for proof agent)

Write this in Flat/Semantics.lean, AFTER the objectLit_allValues theorem (~L1960). This enables objectLit cases in hasAbruptCompletion/NoNestedAbrupt.

```lean
/-- Stepping objectLit when there's a non-value prop: step the first non-value. -/
@[simp] theorem step?_objectLit_step_prop (s : State) (props : List (PropName × Expr))
    (done : List (PropName × Expr)) (name : PropName) (target : Expr) (remaining : List (PropName × Expr))
    (hfnv : firstNonValueProp props = some (done, name, target, remaining)) :
    step? { s with expr := .objectLit props } =
      match step? { s with expr := target } with
      | some (t, sa) =>
          some (t, pushTrace { s with expr := .objectLit (done ++ [(name, sa.expr)] ++ remaining), env := sa.env, heap := sa.heap } t)
      | none => none := by
  rw [step?.eq_1]
  -- valuesFromPropList? fails since firstNonValueProp found a non-value
  have hvnone := valuesFromPropList?_none_of_firstNonValueProp hfnv
  simp only [hvnone, hfnv]
  cases step? { s with expr := target } <;> rfl
```

NOTE: You may need to prove the helper `valuesFromPropList?_none_of_firstNonValueProp` first. Check if it exists with `lean_local_search`. If not, prove it: if firstNonValueProp returns Some, then valuesFromPropList? returns none.

## TARGET 2: if-compound sorries (L9326-9327, L9399-9400)

These are inside `normalizeExpr_if_step_sim` and `normalizeExpr_if_compound_step_sim`. They're about `.if` where the condition is compound (not a value). L9326/9399 are "compound condition: multi-step" and L9327/9400 are "compound HasIfInHead".

Use `lean_goal` at these positions to understand what's needed. The pattern may be:
- Condition is compound → normalizeExpr steps it → Flat also steps it → simulation matches

## TARGET 3: Let step sim (L9045) and while step sim (L9133, L9145)

L9045: `normalizeExpr_let_step_sim` — sorry. Need characterization of what normalizeExpr produces for `.let`.
L9133: While condition value case
L9145: Condition-steps case

For L9145 specifically, when `exprValue? c = none` and `step? c = some (t, sc)`:
- The while condition steps
- After step: `sa'.expr = .while_ sc.expr d` — this preserves SimRel
- This should be closeable

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry line.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
