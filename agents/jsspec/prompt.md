# jsspec — Fix CC Flat.step? breakage + CCStateAgreeWeak

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: CC is broken because proof agent changed Flat.step? to propagate errors through seq/let/assign.

## ===== P0: FIX CC BUILD — THIS IS BLOCKING EVERYTHING =====

Three theorems need `hnoerr` (non-error) hypothesis added:

### Fix 1: Flat_step?_assign_step (~L1961)
The new Flat.step? for `.assign name init` now matches on `t` (the trace event from stepping `init`). If `t = .error msg`, it propagates the error directly. Otherwise it wraps as before.

**Add hypothesis and split**:
```lean
private theorem Flat_step?_assign_step (s : Flat.State) (name : Flat.VarName) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :  -- ADD THIS
    ... := by
  simp [Flat.step?, hss, hnv]
  split <;> simp_all [Flat.exprValue?]
  · rename_i msg heq; exact absurd rfl (hne msg)
```

### Fix 2: Flat_step?_seq_step (~L2204)
Same pattern as assign:
```lean
    (hne : ∀ msg, t ≠ .error msg) :  -- ADD THIS
```
And add the split/absurd proof.

### Fix 3: Flat_step?_let_step (~L2222)
Same pattern.

### Fix callers
After adding `hne` to all three, EVERY caller will need to provide the non-error proof. Each caller should be in a context where the trace event is known (e.g., `.silent`). Add `(by intro msg h; simp at h)` or `(by intro msg h; exact Core.TraceEvent.noConfusion h)` depending on the event type.

Use `lean_diagnostic_messages` after each fix to find broken callers.

### Add error-propagation companions
Also add these companion theorems for use by other proofs:
```lean
private theorem Flat_step?_seq_error (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none) (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
```
(And similarly for let_error, assign_error.)

## ===== P1: CCStateAgreeWeak (only after P0 is clean) =====

Same as before — add CCStateAgreeWeak and the monotonicity lemmas. See previous prompt version for details. Target sorries: L5267, L5834, L8094, L8097, L8170, L8280.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
