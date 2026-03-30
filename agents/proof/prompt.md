# proof — BUILD IS BROKEN. Fix it FIRST, then close CC sorries. Target: build green + -2 sorries.

## EMERGENCY: BUILD BROKEN BY FIX D

Fix D added error propagation to `Flat.step?` for `.seq` and `.let`. This broke 3 lemmas that assume the match resolves without case-splitting on the trace event. **FIX THESE FIRST.**

**FULL GUIDE**: `.lake/_tmp_fix/fix_d_breakage_guide.lean` has EVERY fix with exact code. READ IT FIRST.

### Fix 1: `step?_seq_ctx` in ANFConvertCorrect.lean (L1052)

**Current** (BROKEN):
```lean
private theorem step?_seq_ctx (s : Flat.State) (a b : Flat.Expr)
    (hnotval : Flat.exprValue? a = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := a } = some (t, sa)) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (t, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
```

**Fix** — add `hnoerr` hypothesis and case-split on `t`:
```lean
private theorem step?_seq_ctx (s : Flat.State) (a b : Flat.Expr)
    (hnotval : Flat.exprValue? a = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hstep : Flat.step? { s with expr := a } = some (t, sa))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    ∃ s', Flat.step? { s with expr := .seq a b } = some (t, s') ∧
      s'.expr = .seq sa.expr b ∧ s'.env = sa.env ∧ s'.heap = sa.heap ∧
      s'.funcs = s.funcs ∧ s'.callStack = s.callStack ∧
      s'.trace = s.trace ++ [t] := by
  simp only [Flat.step?, hnotval, hstep]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | silent => exact ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
```

### Fix 1b: `step_wrapSeqCtx` (L1157) — add same `hnoerr` hypothesis

Add `(hnoerr : ∀ msg, t ≠ .error msg)` as a parameter. Pass it to `step?_seq_ctx` at L1175:
```lean
      step?_seq_ctx s inner r hnotval t s_inner hstep hnoerr
```

### Fix 1c: All callers of `step_wrapSeqCtx` (L1311, L1333, L1355, L1378)

All pass `.silent` as `t`. Add `(fun _ h => nomatch h)` or `(by intro msg h; exact nomatch h)` as the `hnoerr` argument. Example:
```lean
        step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval hstep_i hfuncs_i hcs_i htrace_i
```
Wait — `step_wrapSeqCtx` takes `t` as its 2nd arg. So it becomes:
```lean
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) (hnoerr : ∀ msg, t ≠ .error msg) :
```
And callers: `step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) ...`

### Fix 2: `Flat_step?_seq_step` in ClosureConvertCorrect.lean (L1895)

Add `(hnoerr : ∀ msg, t ≠ .error msg)` and fix proof:
```lean
private theorem Flat_step?_seq_step (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hnoerr : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp only [Flat.step?, hnv, hss]
  cases t with
  | error msg => exact absurd rfl (hnoerr msg)
  | log _ => rfl
  | silent => rfl
```

Fix caller at L3125: add `(fun _ h => nomatch h)` or appropriate noerror proof.

### Fix 3: `Flat_step?_let_step` in ClosureConvertCorrect.lean (L1913)

Same pattern — add `hnoerr`, case-split. Fix caller at L2812.

## AFTER BUILD IS GREEN: Close CC sorries

### Priority 1: Integrate cc_convertExpr_not_lit_v2 (-2 sorries at L1369, L1370)

See `.lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean`. Add `convertExpr_not_value_supported` after existing `convertExpr_not_value` (~L1181). Then close forIn/forOf cases by contradiction with `hsupp`.

### Priority 2: Close getIndex string (L4027)

See `.lake/_tmp_fix/cc_getIndex_object_proof.lean` for the pattern. String case is simpler.

### Priority 3: Value sub-cases (L4199, L4521, L4619)

Use HeapInj infrastructure.

## WORKFLOW
1. Fix the 3 broken lemmas (ANF + CC). Build after EACH fix.
2. Then integrate staged CC files.
3. `lake build VerifiedJS.Proofs.ANFConvertCorrect` and `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/*.lean` (read for integration)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`, `VerifiedJS/Flat/Semantics.lean`
