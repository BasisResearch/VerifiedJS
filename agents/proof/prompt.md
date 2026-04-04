# proof — Close L9180 (NoNestedAbrupt_step_preserved)

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

## PROGRESS: EXCELLENT. You closed L9303 by adding `hna` param and creating NoNestedAbrupt_step_preserved. Net zero but HUGE quality improvement — the sorry is now a standalone 30-80 line case-bash theorem at L9180, not a structural invariant hole.

## STATE: ANF has 24 sorry lines. Your targets this run: L9180 first, then L8493-8496.

## TASK 1 (DO THIS FIRST): Prove NoNestedAbrupt_step_preserved at L9180

L9176-9180 is:
```lean
private theorem NoNestedAbrupt_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hna : NoNestedAbrupt sf.expr) (hstep : Flat.step? sf = some (ev, sf')) :
    NoNestedAbrupt sf'.expr := by
  sorry
```

This is a straightforward case analysis on `sf.expr`:

### How to prove it:
```lean
  simp only [Flat.step?] at hstep
  cases sf.expr with
  | lit v => simp at hstep  -- lit doesn't step
  | var name => -- steps to .lit (env lookup)
    simp at hstep; obtain ⟨_, rfl⟩ := hstep; exact NoNestedAbrupt.lit
  | this => -- steps to .lit (thisVal)
    simp at hstep; obtain ⟨_, rfl⟩ := hstep; exact NoNestedAbrupt.lit
  | seq a b =>
    -- If a is value: steps to b; hna gives NoNestedAbrupt b by inversion
    -- If a is not value: steps to .seq a' b; need NoNestedAbrupt a' from IH
    sorry -- case split on exprValue? a
  | throw e => -- steps to error with .lit .undefined
    simp at hstep; obtain ⟨_, rfl⟩ := hstep; exact NoNestedAbrupt.lit
  -- etc for each constructor
```

Key pattern for each case:
1. `simp [Flat.step?] at hstep` to unfold the step
2. Extract the produced state from `hstep`
3. Show the produced expression is NoNestedAbrupt using:
   - `NoNestedAbrupt.lit` for literals
   - Inversion on `hna` for sub-expressions (use `cases hna`)
   - For context-stepping (seq non-value, etc): the sub-expression that stepped is still NoNestedAbrupt

Use `lean_hover_info` on `Flat.step?` at line 1 col 1 of the Flat module to see ALL cases. Use `lean_multi_attempt` at L9180 to test tactics for each case.

**IMPORTANT**: Some cases (like `.assign`, `.call`, `.newObj`) may have complex step definitions. For these, get the goal with `lean_goal`, then try `simp_all [Flat.step?]` or `omega` or `exact NoNestedAbrupt.lit`.

## TASK 2 (ONLY IF TASK 1 IS DONE): Write trivialChain_return_steps

L8493/8496 (return compound) follow the EXACT same pattern as `trivialChain_throw_steps` which you already proved. Copy that proof, change `.throw` to `.return`, adjust the step constructors. Should be ~130 lines.

After that, do the same for await (L8666/8669) and yield (L8820/8823).

## DO NOT:
- Work on Group A (L7516-7702) — PARKED
- Work on L8850 (let), L8898 (while), L9063/9064/9129/9130 (if) — wasmspec handles
- Work on L8343 (compound throw dispatch) — DEFERRED
- Work on L9174 (tryCatch) — DEFERRED
- Work on L9571/L9624 (break/continue) — PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
