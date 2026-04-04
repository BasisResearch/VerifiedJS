# proof — Close hasAbruptCompletion value-matching (6 easy) + NoNestedAbrupt list (6 hard)

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

## STATUS: L7791 IS DONE ✓ — Great work!

The h_supp sorry is gone from CC. Now focus ALL effort on closing sorry cases.

## TASK 1 (HIGHEST PRIORITY): Close 6 easy hasAbruptCompletion cases

In `hasAbruptCompletion_step_preserved` (succ branch), these 6 cases are mechanical copies of the already-proved patterns. Replace each sorry with the exact code below.

### getProp (L9418) — copy of typeof pattern:
```lean
    | getProp obj prop =>
      unfold hasAbruptCompletion at hac
      unfold Flat.step? at hstep
      split at hstep
      next v hv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
      next hv =>
        split at hstep
        next ev' so hso => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]; exact ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hac hso
        next => simp at hstep
```

### deleteProp (L9422) — same as getProp:
```lean
    | deleteProp obj prop =>
      unfold hasAbruptCompletion at hac
      unfold Flat.step? at hstep
      split at hstep
      next v hv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
      next hv =>
        split at hstep
        next ev' so hso => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]; exact ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hac hso
        next => simp at hstep
```

### getEnv (L9434) — same pattern (single sub-expression):
```lean
    | getEnv envExpr idx =>
      unfold hasAbruptCompletion at hac
      unfold Flat.step? at hstep
      split at hstep
      next v hv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
      next hv =>
        split at hstep
        next ev' se hse => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]; exact ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hac hse
        next => simp at hstep
```

### setProp (L9419) — copy of NoNestedAbrupt setProp pattern but with Bool:
```lean
    | setProp obj prop val =>
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      obtain ⟨hobj, hval⟩ := hac
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- obj not value → step obj
        split at hstep
        next ev' so hso => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hobj hso, hval��
        next => simp at hstep
      next addr =>  -- obj = .object addr
        split at hstep
        next vv =>  -- val is value
          simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
        next =>  -- val not value → step val
          split at hstep
          next ev' sv hsv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hval hsv⟩
          next => simp at hstep
      next =>  -- obj = some other value
        split at hstep
        next vv =>  -- val is value
          simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
        next =>  -- val not value → step val
          split at hstep
          next ev' sv hsv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hval hsv⟩
          next => simp at hstep
```

### getIndex (L9420) — 2 sub-expressions, follow NoNestedAbrupt getIndex:
```lean
    | getIndex obj idx =>
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      obtain ⟨hobj, hidx⟩ := hac
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- obj not value → step obj
        split at hstep
        next ev' so hso => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hobj hso, hidx⟩
        next => simp at hstep
      next addr =>  -- obj = .object addr
        split at hstep
        next iv =>  -- idx is value
          simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
        next =>  -- idx not value → step idx
          split at hstep
          next ev' si hsi => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hidx hsi⟩
          next => simp at hstep
      next str =>  -- obj = .string str
        split at hstep
        next iv =>  -- idx is value
          simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
        next =>  -- idx not value → step idx
          split at hstep
          next ev' si hsi => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hidx hsi⟩
          next => simp at hstep
      next =>  -- obj = some other value
        split at hstep
        next iv =>  -- idx is value
          simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
        next =>  -- idx not value → step idx
          split at hstep
          next ev' si hsi => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hidx hsi��
          next => simp at hstep
```

### setIndex (L9421) — 3 sub-expressions, follow NoNestedAbrupt setIndex:
```lean
    | setIndex obj idx val =>
      simp only [hasAbruptCompletion, Bool.or_eq_false_iff] at hac
      obtain ⟨⟨hobj, hidx⟩, hval⟩ := hac
      unfold Flat.step? at hstep
      split at hstep
      next =>  -- obj not value → step obj
        split at hstep
        next ev' so hso => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨⟨ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hobj hso, hidx⟩, hval⟩
        next => simp at hstep
      next addr =>  -- obj = .object addr
        split at hstep
        next =>  -- idx not value → step idx
          split at hstep
          next ev' si hsi => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hidx hsi⟩, hval���
          next => simp at hstep
        next idxVal =>  -- idx is value
          split at hstep
          next =>  -- val not value → step val
            split at hstep
            next ev' sv hsv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨⟨by simp [hasAbruptCompletion], by simp [hasAbruptCompletion]⟩, ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hval hsv⟩
            next => simp at hstep
          next valVal =>  -- all values → dispatch
            simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
      next =>  -- obj = some other value
        split at hstep
        next =>  -- idx not value → step idx
          split at hstep
          next ev' si hsi => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨⟨by simp [hasAbruptCompletion], ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hidx hsi⟩, hval⟩
          next => simp at hstep
        next idxVal =>  -- idx is value
          split at hstep
          next =>  -- val not value → step val
            split at hstep
            next ev' sv hsv => simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp only [Flat.State.expr, hasAbruptCompletion, Bool.or_eq_false_iff]; exact ⟨⟨by simp [hasAbruptCompletion], by simp [hasAbruptCompletion]⟩, ih _ (by simp [Flat.Expr.depth] at hd; omega) _ _ _ _ _ _ _ hval hsv⟩
            next => simp at hstep
          next valVal =>  -- all values → dispatch
            simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]
```

**NOTE**: If `split at hstep` generates different goals than expected (e.g., 3 goals instead of 2 for getProp due to object/string/other), use `lean_goal` to check and adapt. The `simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Flat.State.expr, hasAbruptCompletion]` pattern handles ALL value branches since they all produce `.lit something`.

**If any case doesn't compile**: Use `lean_multi_attempt` at the sorry position with these tactics:
- `unfold hasAbruptCompletion at hac; unfold Flat.step? at hstep; simp_all [Flat.State.expr, hasAbruptCompletion]`
- `simp_all [hasAbruptCompletion, Flat.step?, Flat.State.expr]`

## TASK 2: NoNestedAbrupt list cases (6 remaining)

After closing TASK 1, move to the 6 list cases in NoNestedAbrupt_step_preserved:
- call (L9625), newObj (L9626), makeEnv (L9644), objectLit (L9657), arrayLit (L9658), tryCatch (L9659)

These need `firstNonValueExpr_reconstruct` helper. Write it near `firstNonValueExpr` definitions, then use it for call pattern (see previous prompt for template).

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
