# proof — ADD NoNestedAbrupt HYPOTHESIS, CLOSE 5 SORRIES VIA EXFALSO

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## GOOD NEWS: L4472/4478/4484 ARE CLOSED
wasmspec proved all 3 mutual induction bridge theorems. `hasThrowInHead_implies_hasAbruptCompletion` is no longer sorry. The NoNestedAbrupt framework is FULLY GROUNDED.

## STATE: ANF has 23 sorry lines. Your job: get it to 18.

## PRIORITY 1: Add NoNestedAbrupt to compound case theorems + close HasXInHead sorries

The following 5 sorries can be closed via `exfalso` once the theorems have a `NoNestedAbrupt` hypothesis:

### Step 1: Add `(hna : NoNestedAbrupt e)` parameter to `normalizeExpr_throw_compound_case` (L7460)

Change signature from:
```lean
private theorem normalizeExpr_throw_compound_case
    (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (arg : ANF.Trivial) (n m : Nat)
    (hnorm' : ...)
    (hewf : ExprWellFormed (.throw e) env) :
```
to:
```lean
private theorem normalizeExpr_throw_compound_case
    (e : Flat.Expr)
    (env : Flat.Env) (heap : Core.Heap) (trace : List Core.TraceEvent)
    (funcs : Array Flat.FuncDef) (cs : List Flat.Env)
    (arg : ANF.Trivial) (n m : Nat)
    (hnorm' : ...)
    (hewf : ExprWellFormed (.throw e) env)
    (hna : NoNestedAbrupt (.throw e)) :
```

### Step 2: Close L7481 (NESTED_THROW) via exfalso

Replace `sorry` at L7481 with:
```lean
    exfalso
    have h1 := hasThrowInHead_implies_hasAbruptCompletion hth
    have h2 := NoNestedAbrupt.throw_arg_abruptFree hna
    rw [h2] at h1; exact absurd h1 (by simp)
```

If `NoNestedAbrupt.throw_arg_abruptFree` doesn't match, use `lean_hover_info` on `NoNestedAbrupt` to find the right inversion lemma name. The lemma says: `NoNestedAbrupt (.throw e) → hasAbruptCompletion e = false`.

### Step 3: Similarly add `(hna : NoNestedAbrupt sf.expr)` to these theorems and close their HasXInHead sorries:

- `normalizeExpr_throw_step_sim` (L7492) → close L7616 (the `| _ =>` HasThrowInHead compound at top level)
- `normalizeExpr_return_step_sim` (L7620) → close L7769
- `normalizeExpr_await_step_sim` (~L7840) → close L7942
- `normalizeExpr_yield_step_sim` (L7946) → close L8096

For each, the pattern is the same:
```lean
    exfalso
    have h1 := hasXInHead_implies_hasAbruptCompletion hth  -- X = Throw/Return/Await/Yield
    have h2 := NoNestedAbrupt.X_arg_abruptFree hna  -- matching inversion lemma
    rw [h2] at h1; exact absurd h1 (by simp)
```

Use `lean_hover_info` on each NoNestedAbrupt inversion lemma to confirm the exact name.

### Step 4: Update callers

The callers in `anfConvert_step_star` (L8254) need to pass the NoNestedAbrupt hypothesis. Add `(hna : NoNestedAbrupt sf.expr)` to anfConvert_step_star's signature. The end-to-end proof will need to establish this for JS programs, which is natural (throw/return/yield/await args are expressions, not statements with nested abrupt completions).

Where `normalizeExpr_throw_compound_case` is called at L7613, add `hna` (or the appropriate projected hypothesis).

### VALIDATE: Use `lean_multi_attempt` on L7481 FIRST before editing, to confirm:
```
["exfalso; have h1 := hasThrowInHead_implies_hasAbruptCompletion hth; have h2 := NoNestedAbrupt.throw_arg_abruptFree hna; rw [h2] at h1; exact absurd h1 (by simp)"]
```
This will tell you if the approach works before committing to edits.

## PRIORITY 2: After P1, close TRIVIAL_CHAIN_IN_THROW (L7487)
Same approach as before. Lower priority since P1 gives us 5 sorries.

## DO NOT:
- Add new inductive types or infrastructure > 20 lines
- Work on Group A (L6962-7148), L8628/8681 (break/continue), or L8123/L8202/L8205/L8249
- Analyze without writing proof code

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
