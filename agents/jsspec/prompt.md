# jsspec — normalizeExpr INVERSION LEMMAS (ANF CRITICAL PATH)

## STATUS: proof agent is working on ANF. It NEEDS inversion lemmas to make progress.

## PRIORITY 0: normalizeExpr inversion lemmas (URGENT)

The proof agent needs to invert `hnorm : StateT.run (ANF.normalizeExpr sf.expr k) n = Except.ok (result, m)` to determine what `sf.expr` is from the shape of `result`.

Look at `VerifiedJS/ANF/Convert.lean:36-136`. Key observation: each normalizeExpr case produces output with a UNIQUE top-level constructor. So the result constructor determines the input constructor.

Write these lemmas in `VerifiedJS/Proofs/ANFConvertCorrect.lean` as `private theorem` (before `anfConvert_step_star`):

### 1. labeled inversion (MOST URGENT)
```lean
-- normalizeExpr only produces .labeled from .labeled input
private theorem normalizeExpr_labeled_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (label : Option String) (body_anf : ANF.Expr)
    (h : (ANF.normalizeExpr e k).run n = .ok (.labeled label body_anf, m)) :
    ∃ body_flat, e = .labeled label body_flat ∧
      (ANF.normalizeExpr body_flat k).run n = .ok (body_anf, m) := by
  -- Proof: case split on e. For every constructor except .labeled,
  -- normalizeExpr produces a different constructor, contradiction.
  cases e <;> simp [ANF.normalizeExpr] at h
  -- Only .labeled case survives
  case labeled label' body' =>
    -- h : (.labeled label' bodyExpr, m') = (.labeled label body_anf, m)
    exact ⟨body', rfl, h⟩
```

### 2. return inversion
```lean
private theorem normalizeExpr_return_none_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.return none, m)) :
    e = .return none := by
  cases e <;> simp [ANF.normalizeExpr] at h
```

### 3. break/continue inversion (for future use)
```lean
private theorem normalizeExpr_break_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (label : Option String)
    (h : (ANF.normalizeExpr e k).run n = .ok (.break label, m)) :
    e = .break label := by
  cases e <;> simp [ANF.normalizeExpr] at h

private theorem normalizeExpr_continue_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (label : Option String)
    (h : (ANF.normalizeExpr e k).run n = .ok (.continue label, m)) :
    e = .continue label := by
  cases e <;> simp [ANF.normalizeExpr] at h
```

### 4. throw inversion
```lean
private theorem normalizeExpr_throw_inv (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (n m : Nat) (arg : ANF.Trivial)
    (h : (ANF.normalizeExpr e k).run n = .ok (.throw arg, m)) :
    ∃ arg_flat, e = .throw arg_flat := by
  cases e <;> simp [ANF.normalizeExpr] at h
  case throw a => exact ⟨a, rfl⟩
```

## HOW TO PROVE THESE

The key tactic pattern is:
1. `cases e` — split on all Flat.Expr constructors
2. For each non-matching case, `simp [ANF.normalizeExpr]` at h produces contradiction (the output constructor doesn't match)
3. For the matching case, extract the relationship

**IMPORTANT**: `simp [ANF.normalizeExpr]` may not fully unfold the recursive cases. You may need `unfold ANF.normalizeExpr` or `simp only [ANF.normalizeExpr]` with equation lemmas. If `simp` fails for a case, use `lean_goal` to see what's left and try `contradiction` or `exact absurd h (by ...)`.

## VERIFY EACH LEMMA

After writing each lemma:
1. `lean_goal` at the `by` to check no unsolved goals
2. `lean_diagnostic_messages` to check no errors

## PRIORITY 1: Flat.step? lemmas for labeled/return

```lean
-- What does Flat.step? do for .labeled and .return?
-- Check VerifiedJS/Flat/Semantics.lean
-- Write @[simp] lemmas if they don't already exist
```

## DO NOT:
- Edit the main theorem cases (those are for proof agent)
- Run full `lake build`
- Touch CC or Wasm files

## Log progress to agents/jsspec/log.md
