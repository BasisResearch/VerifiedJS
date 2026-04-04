# proof — NoNestedAbrupt propagation (L9303) is THE blocker

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

## PROGRESS: You closed NESTED_THROW (L8204) via NoNestedAbrupt exfalso. Well done. But you generated a replacement sorry at L9303. NET ZERO. Close L9303 NOW.

## STATE: ANF has 24 sorry lines. Your ONE target this run: L9303.

## TASK 1 (DO THIS FIRST, DO NOT SKIP): Close L9303

L9303 is:
```lean
all_goals have hna_sf : NoNestedAbrupt sf.expr := sorry -- TODO: propagate NoNestedAbrupt invariant
```

Inside `anfConvert_step_star`. You need:

### Step 1: Write NoNestedAbrupt_step_preserved
```lean
theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  -- unfold Flat.step? at hstep, cases on sf.expr
  -- Each case: sub-expressions are NoNestedAbrupt by inversion of hna
  -- Produced expressions: either sub-expressions (NoNestedAbrupt by IH) or .lit (trivially NoNestedAbrupt)
  sorry
```

This is ~30-80 lines: `cases` on the Flat.step? definition, then for each case use `NoNestedAbrupt` inversions. Key patterns:
- `.seq (lit v) b` steps to `b` → `hna` gives `NoNestedAbrupt b` by inversion
- `.var name` steps to `.lit v` → `NoNestedAbrupt.lit`
- `.throw e` steps to error → produced expr is `.lit .undefined`, trivially NoNestedAbrupt
- etc.

Use `lean_hover_info` on `Flat.step?` to see all cases. Use `lean_multi_attempt` to test each case.

### Step 2: Add hna to anfConvert_step_star signature
Add `(hna : NoNestedAbrupt sf.expr)` parameter. Replace `sorry` at L9303 with `hna`.

### Step 3: Update anfConvert_steps_star
The caller that invokes `anfConvert_step_star` in a loop. Add `hna` parameter. After each step, use `NoNestedAbrupt_step_preserved` to get `hna'` for the next state.

### Step 4: Update compiler_correct (top-level)
The top-level theorem needs to provide initial `hna`. If normalizeExpr produces NoNestedAbrupt output, this should follow from the compiler pipeline. If it's hard, use sorry here temporarily — it's a MUCH better sorry than L9303 because it's at the top level where we know the input is well-formed.

## TASK 2 (ONLY IF TASK 1 IS DONE): Apply trivialChain pattern to return/await/yield

L8493/8496, L8666/8669, L8820/8823 — same pattern as throw. Write `trivialChain_return_steps`, `trivialChain_await_steps`, `trivialChain_yield_steps` analogous to the existing `trivialChain_throw_steps`. Each is ~130 lines following the same structure.

## DO NOT:
- Work on Group A (L7516-7702) — PARKED
- Work on L8850 (let), L8898 (while), L9063/9064/9129/9130 (if) — wasmspec handles
- Work on L8343 (compound throw dispatch) — DEFERRED until after return/await/yield
- Work on L9174 (tryCatch) — DEFERRED
- Work on L9554/L9607 (break/continue) — PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
