# proof — STOP WORKING ON TRIVIALCHAIN. DO P1: NoNestedAbrupt exfalso closures.

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

## YOU HAVE BEEN WORKING ON TRIVIALCHAIN FOR 2+ RUNS. STOP.

The trivialChain seq case (L7711) is blocked on a normalizeExpr passthrough lemma. This is hard. **DO NOT continue working on it.** wasmspec will handle trivialChain.

## STATE: ANF has ~24 sorry lines. Your job: close 5 via NoNestedAbrupt exfalso.

## YOUR ONE PRIORITY: Add NoNestedAbrupt hypothesis and close HasXInHead sorries

The NoNestedAbrupt framework is FULLY GROUNDED (wasmspec proved all bridge theorems). You can now use it.

### Step 1: Add `(hna : NoNestedAbrupt sf.expr)` to `normalizeExpr_throw_step_sim`

Find the theorem (around L7770). Change its signature to include `(hna : NoNestedAbrupt sf.expr)`.

Then find the `| _ =>` case that dispatches to `normalizeExpr_throw_compound_case`. That compound case helper also needs `(hna : NoNestedAbrupt (.throw e))`. Add it.

### Step 2: Close the NESTED_THROW sorry (L7756)

In `normalizeExpr_throw_compound_case`, after `rcases Classical.em (HasThrowInHead e)`, the `hth` branch (L7756) should be:
```lean
    exfalso
    have h1 := hasThrowInHead_implies_hasAbruptCompletion hth
    have h2 := throw_arg_abruptFree hna  -- or NoNestedAbrupt.throw_arg_abruptFree
    simp [h2] at h1
```

Use `lean_hover_info` on `NoNestedAbrupt` and `throw_arg_abruptFree` to confirm exact names. Use `lean_multi_attempt` at L7756 to test before editing.

### Step 3: Similarly close L8044 (HasReturnInHead), L8217 (HasAwaitInHead), L8371 (HasYieldInHead)

Add `(hna : NoNestedAbrupt sf.expr)` to:
- `normalizeExpr_return_step_sim` → close HasReturnInHead sorry
- `normalizeExpr_await_step_sim` → close HasAwaitInHead sorry
- `normalizeExpr_yield_step_sim` → close HasYieldInHead sorry

For each, the pattern is:
```lean
    exfalso
    have h1 := hasXInHead_implies_hasAbruptCompletion hth
    have h2 := X_arg_abruptFree hna
    simp [h2] at h1
```

### Step 4: Update callers in anfConvert_step_star to pass hna

Add `(hna : NoNestedAbrupt sf.expr)` to `anfConvert_step_star`'s signature. Pass it through to the step sim calls.

### VALIDATE with lean_multi_attempt BEFORE editing

Test each tactic at the sorry position first. If it doesn't work, use `lean_goal` + `lean_hover_info` to debug.

## DO NOT:
- Work on trivialChain (L7711, L7762) — wasmspec handles this
- Work on Group A (L7077-7263), L8903/8956 (break/continue), L8398/L8446/L8477/L8480/L8524
- Add new infrastructure > 20 lines
- Analyze without writing proof code

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
