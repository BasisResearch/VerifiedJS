# proof — FIX THE BUILD. 3 edits. Nothing else until green.

## YOU HAVE ONE JOB: Fix D broke the build. Apply these EXACT edits.

Fix D added a `| some (.error msg, sa) =>` arm to `.seq` and `.let` in `Flat.step?`.
Three theorems assumed only 2 arms. Fix them by adding `hne` and case-splitting.

### EDIT 1: `step?_seq_ctx` (ANFConvertCorrect.lean L1052-1061)

Replace the ENTIRE theorem:
```lean
private theorem step?_seq_ctx (s : Flat.State) (a b : Flat.Expr)
    (hnotval : Flat.exprValue? a = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := a } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (t, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hne msg)
  | _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
```

### EDIT 2: `step_wrapSeqCtx` (ANFConvertCorrect.lean L1157-1181)

Add `(hne : ∀ msg, t ≠ .error msg)` parameter after `(ctx : List Flat.Expr)`:
```lean
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) (hne : ∀ msg, t ≠ .error msg) :
```
And pass `hne` at L1175:
```lean
      step?_seq_ctx s inner r hnotval t s_inner hstep hne
```

### EDIT 3: All 4 callers of `step_wrapSeqCtx` (L1311, L1333, L1355, L1378)

All pass `.silent` as `t`. Add `(fun _ h => nomatch h)` after `rs`/`ctx`:
```lean
-- L1311: change to:
        step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
-- L1333: change to:
        step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
-- L1355: change to:
        step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_v hnotval_v hstep_v hfuncs_v hcs_v htrace_v
-- L1378: change to:
        step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_t hnotval_t hstep_t hfuncs_t hcs_t htrace_t
```

### EDIT 4: `Flat_step?_seq_step` (ClosureConvertCorrect.lean L1895-1902)

Replace:
```lean
private theorem Flat_step?_seq_step (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]
  cases t with
  | error msg => exact absurd rfl (hne msg)
  | _ => rfl
```

### EDIT 5: `Flat_step?_let_step` (ClosureConvertCorrect.lean L1913-1920)

Replace:
```lean
private theorem Flat_step?_let_step (s : Flat.State) (name : String) (body : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .«let» name fe body } =
      some (t, { expr := .«let» name sa.expr body, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]
  cases t with
  | error msg => exact absurd rfl (hne msg)
  | _ => rfl
```

### EDIT 6: CC callers at L2812 and L3125

Add `(fun _ h => nomatch h)` as the `hne` argument to both calls.

L2812 uses `Flat_step?_let_step`. L3125 uses `Flat_step?_seq_step`.
Find the exact call and add the new arg at the end.

### EDIT 7: `step?_none_implies_lit_aux` (ClosureConvertCorrect.lean ~L5353)

If this breaks, it's because the induction on `step?` now has a new `.error` match arm.
Add `| some (.error _, _) => ...` cases where the `step?` match occurs in the proof.

## WORKFLOW
1. Apply Edits 1-3 to ANFConvertCorrect.lean
2. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
3. If green, apply Edits 4-6 to ClosureConvertCorrect.lean
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
5. If step?_none_implies_lit breaks, apply Edit 7
6. Final: `lake build VerifiedJS`

## AFTER BUILD IS GREEN: Close CC sorries

### Priority 1: Integrate cc_convertExpr_not_lit_v2 (-2 sorries at L1369, L1370)
See `.lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean`. Close forIn/forOf by contradiction.

### Priority 2: Value sub-cases (getIndex, setProp)

## FILES
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/*.lean` (read for integration)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`, `VerifiedJS/Flat/Semantics.lean`
