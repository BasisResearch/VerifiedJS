# proof — Close NESTED_THROW (L8204) via NoNestedAbrupt exfalso

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

## GREAT JOB closing TRIVIAL_CHAIN_IN_THROW last run. Now: NoNestedAbrupt.

## STATE: ANF has 22 sorry lines. Your job: close L8204 + L8339 via NoNestedAbrupt.

## YOUR ONE PRIORITY: Close NESTED_THROW sorry at L8204

L8204 is the `HasThrowInHead e` branch of `normalizeExpr_throw_compound_case`. The `¬HasThrowInHead` branch is DONE (you proved it via trivialChain_throw_steps). Now close the `HasThrowInHead e` branch.

### The plan: add NoNestedAbrupt hypothesis, derive contradiction

`NoNestedAbrupt` is fully grounded — all bridge theorems are proved (L4472/4478/4484 closed by wasmspec). The key insight: if `HasThrowInHead e` is true AND `NoNestedAbrupt (.throw e)` is true, that's a contradiction because NoNestedAbrupt says `.throw e` has no abrupt completions nested in its argument `e`.

### Step 1: Check what lemmas exist

Use `lean_local_search` for:
- `NoNestedAbrupt`
- `hasThrowInHead_implies_hasAbruptCompletion`
- `throw_arg_abruptFree` or similar
- `AbruptFree`

The pattern should be:
```lean
exfalso
have h1 := hasThrowInHead_implies_hasAbruptCompletion hth
-- h1 : HasAbruptCompletion e
have h2 : AbruptFree e := NoNestedAbrupt.throw_inv hna  -- or similar destructor
exact absurd h1 h2  -- or use simp/contradiction
```

Use `lean_hover_info` on `NoNestedAbrupt` to see its constructors and what inversion lemma gives you `AbruptFree e` from `NoNestedAbrupt (.throw e)`.

### Step 2: Add `(hna : NoNestedAbrupt sf.expr)` to the theorem

Add `hna` to `normalizeExpr_throw_compound_case` (around L8170). Then at L8204:
```lean
  · -- NESTED_THROW: e itself contains a throw in head position
    exfalso
    have h_abrupt := hasThrowInHead_implies_hasAbruptCompletion hth
    have h_free := ... -- get AbruptFree e from hna
    exact absurd h_abrupt h_free
```

Use `lean_multi_attempt` at L8204 to test tactics BEFORE editing.

### Step 3: Propagate hna to callers

`normalizeExpr_throw_compound_case` is called from `normalizeExpr_throw_step_sim` (L8336). Add `hna` there too, and pass it through. Then `normalizeExpr_throw_step_sim` is called from `anfConvert_step_star` — add `hna` to the main theorem signature.

### Step 4: Close L8339 (compound throw dispatch)

L8339 is in the `| _ =>` branch of `normalizeExpr_throw_step_sim`. After Step 2, this should dispatch to the updated `normalizeExpr_throw_compound_case` with `hna`. If L8339 is a different sorry pattern, use `lean_goal` to understand it.

### Step 5: Apply same pattern to return (L8489/8492), yield (L8816/8819)

Same exfalso pattern with `HasReturnInHead`, `HasYieldInHead` etc. Each needs `NoNestedAbrupt` → `AbruptFree` → contradiction.

### VALIDATE with lean_multi_attempt BEFORE editing

Test each tactic at the sorry position. If names don't match, use `lean_hover_info` and `lean_local_search` to find correct names.

## DO NOT:
- Work on trivialChain — DONE
- Work on Group A (L7516-7702) eval context lifting — PARKED
- Work on L8846 (let step sim), L8894 (while step sim), L8925/8928 (if step sim) — wasmspec handles these
- Work on L8972 (tryCatch), L9351/9404 (break/continue) — DEFERRED
- Add new infrastructure > 20 lines (the framework exists, just USE it)

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
