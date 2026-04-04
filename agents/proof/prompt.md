# proof — Close L7791 (EndToEnd param) + hasAbruptCompletion_step_preserved + list helper lemmas

## RULES
- Edit: ANFConvertCorrect.lean AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build EndToEnd: `lake build VerifiedJS.Proofs.EndToEnd`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## TASK 1 (PRIORITY): Close L7791 in ClosureConvertCorrect.lean via EndToEnd.lean

L7791 in ClosureConvertCorrect.lean is:
```lean
  have h_supp : s.body.supported = true := sorry
```
inside `closureConvert_correct`. The fix requires TWO coordinated edits:

### Step A: Add param to closureConvert_correct (ClosureConvertCorrect.lean)

Change the theorem signature from:
```lean
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (hnofor : ...) :
```
to:
```lean
theorem closureConvert_correct (s : Core.Program) (t : Flat.Program)
    (h : Flat.closureConvert s = .ok t)
    (h_wf : noCallFrameReturn s.body = true)
    (h_addr_wf : ExprAddrWF s.body 1)
    (h_supp : s.body.supported = true)
    (hnofor : ...) :
```
And DELETE the sorry line `have h_supp : s.body.supported = true := sorry`.

### Step B: Update EndToEnd.lean callsite

In `flat_to_wasm_correct`, add `(h_supp_core : core.body.supported = true)` after `h_addr_wf`, and pass it at the callsite on L70:
```lean
    obtain ⟨coreTrace, hcoreb, heq⟩ := closureConvert_correct core flat hcc h_wf h_addr_wf h_supp_core hnofor flatTrace hflatb
```

Build BOTH files after.

## TASK 2: Close hasAbruptCompletion_step_preserved (L9209)

L9209: `sorry -- SEPARATE THEOREM: prove later by same induction pattern`

This theorem says: if `hasAbruptCompletion expr = false` and `Flat.step?` succeeds, then the result also has `hasAbruptCompletion = false`. It follows the EXACT same induction-on-depth structure as `NoNestedAbrupt_step_preserved`. Each case: unfold step?, split on exprValue?, value case → .lit (hasAbruptCompletion false by def), sub-step case → recursive call.

The `hasAbruptCompletion` function returns true only for break/continue/return/throw/yield/await with nested abrupt. For all other constructors, it recurses on sub-expressions. Use the same `ih` pattern.

## TASK 3: Write firstNonValueExpr_reconstruct helper lemma

The remaining 6 NoNestedAbrupt list cases (call, newObj, makeEnv, objectLit, arrayLit, tryCatch) all need this lemma:

```lean
theorem firstNonValueExpr_reconstruct {l : List Flat.Expr} {done target rest}
    (h : Flat.firstNonValueExpr l = some (done, target, rest)) :
    l = done ++ [target] ++ rest := by
  induction l generalizing done target rest with
  | nil => simp [Flat.firstNonValueExpr] at h
  | cons e tl ih =>
    unfold Flat.firstNonValueExpr at h
    split at h
    · -- e = .lit _
      split at h
      · next heq => simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; simp; exact ih heq
      · simp at h
    · -- e is not lit
      simp at h; obtain ⟨rfl, rfl, rfl⟩ := h; rfl
```

Place this near `firstNonValueExpr_depth` in Flat/Syntax.lean or ANFConvertCorrect.lean (whichever compiles). Then use it to prove the call case:

```lean
    | call f fenv args =>
      cases hna with | call hf henv hargs =>
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- f not value → step f
        split at hstep
        next ev' sf hsf => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
          exact NoNestedAbrupt.call (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ hf hsf) henv hargs
        next => simp at hstep
      next =>  -- f is value
        split at hstep
        next =>  -- env not value → step env
          split at hstep
          next ev' se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
            exact NoNestedAbrupt.call hf (ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ henv hse) hargs
          next => simp at hstep
        next envVal =>  -- env is value
          split at hstep
          next argVals =>  -- all args values
            -- All call dispatch cases produce .lit or function body (need NNA for body separately)
            sorry  -- function call dispatch: produces .lit or wrapped tryCatch
          next =>  -- some arg not value
            split at hstep
            next done target remaining hfnve =>
              split at hstep
              next ev' sa hsa =>
                simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr]
                have hrec := firstNonValueExpr_reconstruct hfnve
                have htarget_na : NoNestedAbrupt target := by
                  have : target ∈ args := by rw [hrec]; simp
                  exact hargs _ this
                exact NoNestedAbrupt.call hf henv (fun e he => by
                  simp [List.mem_append] at he
                  rcases he with hmem | rfl | hmem
                  · have : e ∈ args := by rw [hrec]; simp [List.mem_append]; left; left; exact hmem
                    exact hargs _ this
                  · exact ih _ (by simp [Flat.Expr.depth] at hd; have := firstNonValueExpr_depth hfnve; omega) _ _ _ _ _ _ htarget_na hsa
                  · have : e ∈ args := by rw [hrec]; simp [List.mem_append]; right; right; exact hmem
                    exact hargs _ this)
              next => simp at hstep
            next => simp at hstep
```

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
