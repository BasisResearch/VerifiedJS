# jsspec — Fix Flat_step?_seq_step + CCStateAgree weakening

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: The proof agent changed Flat.step? to propagate errors through seq/let/assign. CC currently has NO errors but it may break after a rebuild if it depends on seq stepping behavior. Check immediately.

## ===== P0: VERIFY CC BUILD STATUS =====

Run `lean_diagnostic_messages` on ClosureConvertCorrect.lean with severity=error. If there are new errors, especially at `Flat_step?_seq_step` (around L2204-2211), fix them FIRST.

The Flat.step? change adds a `match t with | .error _ => ... | _ => ...` branch in seq/let/assign. This means `Flat_step?_seq_step` needs a non-error hypothesis.

**If broken, fix with:**
```lean
private theorem Flat_step?_seq_step (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa))
    (hne : ∀ msg, t ≠ .error msg) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
  split <;> simp_all [Flat.exprValue?]
  · rename_i msg heq; exact absurd rfl (hne msg)
```

Similarly fix `Flat_step?_let_step` and `Flat_step?_assign_step` if they exist and break.

Add companion error-propagation theorems:
```lean
private theorem Flat_step?_seq_error (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv]
```

Then fix ALL callers of `Flat_step?_seq_step` to supply the `hne` argument. Each caller is in a branch where the event is known to be non-error (e.g., `.silent` or a specific non-error event). Add `(by intro msg h; simp at h)` or similar.

## ===== P1: CCStateAgreeWeak (only after P0 is stable) =====

Add a weak agreement + monotonicity lemma:
```lean
private abbrev CCStateAgreeWeak (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId ≤ st2.nextId ∧ st1.funcs.size ≤ st2.funcs.size

private theorem convertExpr_nextId_le (e : Core.Expr) (env : List Core.VarName)
    (st : Flat.CCState) : st.nextId ≤ (Flat.convertExpr e env st).snd.nextId := by
  sorry -- prove by structural induction on e

private theorem convertExpr_funcs_size_le (e : Core.Expr) (env : List Core.VarName)
    (st : Flat.CCState) : st.funcs.size ≤ (Flat.convertExpr e env st).snd.funcs.size := by
  sorry -- prove by structural induction on e
```

Then use `CCStateAgreeWeak` at the 6 blocked sorry sites:
- L5237 (if-true CCStateAgree)
- L5262 (if-false CCStateAgree)
- L8089, L8092 (tryCatch)
- L8165 (while_ CCStateAgree)
- L8275 (while_ CCStateAgree)

This requires changing the `suffices` invariant for those cases. Be careful not to break working proofs.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
