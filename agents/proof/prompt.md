# proof — FIX THE BUILD. 7 edits. Nothing else until green.

## CRITICAL: MEMORY IS TIGHT (7.7GB total, no swap)
- **NEVER run `lake build VerifiedJS`** (full build). It spawns 3 parallel Lean processes and OOMs.
- Build ONE module at a time: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building, kill any stale lean processes: `pkill -u proof -f "lean.*\.lean"`
- Wait 10 seconds between builds for memory to free

## YOU HAVE ONE JOB: Fix D broke the build. Apply these EXACT edits.

Fix D added a `| some (.error msg, sa) =>` arm to `.seq` and `.let` in `Flat.step?`.
Three theorems assumed only 2 arms. Fix them by adding `hne` and case-splitting.

### EDIT 1: `step?_seq_ctx` (ANFConvertCorrect.lean L1052-1061)

Replace the ENTIRE theorem (L1052-1061):
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

### EDIT 2: `step_wrapSeqCtx` (ANFConvertCorrect.lean L1157-1158)

Change signature from:
```lean
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) :
```
To:
```lean
private theorem step_wrapSeqCtx (s : Flat.State) (t : Core.TraceEvent)
    (ctx : List Flat.Expr) (hne : ∀ msg, t ≠ .error msg) :
```
And at L1175, pass `hne`:
```lean
      step?_seq_ctx s inner r hnotval t s_inner hstep hne
```

### EDIT 3: All 4 callers of `step_wrapSeqCtx` (L1311, L1333, L1355, L1378)

All pass `.silent` as `t`. Insert `(fun _ h => nomatch h)` after `rs`/`ctx`:
```
L1311:  step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval ...
L1333:  step_wrapSeqCtx sf .silent rs (fun _ h => nomatch h) _ s_i hnotval ...
L1355:  step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_v hnotval_v ...
L1378:  step_wrapSeqCtx sf .silent ctx (fun _ h => nomatch h) _ s_t hnotval_t ...
```

### BUILD CHECK 1
```bash
pkill -u proof -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Proofs.ANFConvertCorrect
```

### EDIT 4: `Flat_step?_seq_step` (ClosureConvertCorrect.lean L1895-1902)

Replace entire theorem:
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

Replace entire theorem:
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

Add `(fun _ h => nomatch h)` as the last argument to `Flat_step?_let_step` (L2812) and `Flat_step?_seq_step` (L3125).

### EDIT 7: `step?_none_implies_lit_aux` (~L5353)

If build fails here: the induction proof has new match arms from Fix D.
Add `| some (.error _, _) => ...` arms. These should be `simp [Flat.step?]` or `contradiction`.

### BUILD CHECK 2
```bash
pkill -u proof -f "lean.*\.lean" 2>/dev/null; sleep 5
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```

## AFTER BUILD IS GREEN: Close CC sorries

### Priority 1: Integrate cc_convertExpr_not_lit_v2 (-2 sorries)
See `.lake/_tmp_fix/cc_convertExpr_not_lit_v2.lean`.

## FILES
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/*.lean` (read for integration)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`, `VerifiedJS/Flat/Semantics.lean`
