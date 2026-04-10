# jsspec — CCStateAgree weakening + Flat_step?_seq_step fix

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: CC has 12 sorry tactics. 6 blocked by CCStateAgree being too strong. STOP ANALYZING AND START EDITING.

## ===== P0: FIX Flat_step?_seq_step (may be needed after proof agent changes Flat.step?) =====

**Check first**: Run `lean_diagnostic_messages` on ClosureConvertCorrect.lean. If there are NEW errors at L2204-2211 (the `Flat_step?_seq_step` theorem), the proof agent changed Flat.step? to propagate errors through seq.

If so, fix the theorem by adding a non-error hypothesis:

**Current** (L2204-2211):
```lean
private theorem Flat_step?_seq_step (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (t : Core.TraceEvent) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (t, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (t, { expr := .seq sa.expr b, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [t], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]
```

**Replace with**:
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

The caller at L5392 provides non-error events (it's in the cond-stepping branch where cond steps to a sub-expression, not an error). Add `(by intro msg h; simp at h)` or find the appropriate discharge.

Also add a companion theorem for the error case:
```lean
private theorem Flat_step?_seq_error (s : Flat.State) (b : Flat.Expr) (fe : Flat.Expr)
    (hnv : Flat.exprValue? fe = none)
    (msg : String) (sa : Flat.State)
    (hss : Flat.step? { s with expr := fe } = some (.error msg, sa)) :
    Flat.step? { s with expr := .seq fe b } =
      some (.error msg, { expr := sa.expr, env := sa.env, heap := sa.heap,
                 trace := s.trace ++ [.error msg], funcs := s.funcs, callStack := s.callStack }) := by
  simp [Flat.step?, hss, hnv, Flat.pushTrace]
```

## ===== P1: WEAKEN CCStateAgree =====

**Definition** (L562-563):
```lean
private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size
```

The 6 sorry sites need a weaker notion. The safest approach: DON'T change CCStateAgree itself. Instead:

### Option A (preferred): Add a new weak agreement
```lean
private abbrev CCStateAgreeWeak (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId ≤ st2.nextId ∧ st1.funcs.size ≤ st2.funcs.size
```

Then change the sorry sites to use CCStateAgreeWeak where needed. This avoids breaking ANY existing proof.

### Option B: Prove convertExpr monotonicity
The key property: `(convertExpr e ... st).snd.nextId ≥ st.nextId` and same for funcs.size. This lets you close the gap.

### L5237 sorry specifically:
The tuple `⟨st, (convertExpr then_ ... st).snd, [eq], ⟨rfl, rfl⟩, sorry⟩` — the sorry needs to prove some state agreement between `(convertExpr then_ ... st).snd` and the overall conversion output state. The output state is `(convertExpr else_ ... (convertExpr then_ ... st).snd).snd`. You need `CCStateAgree (convertExpr then_ ... st).snd (convertExpr else_ ... (convertExpr then_ ... st).snd).snd` or the weak version.

If using weak: `CCStateAgreeWeak (convertExpr then_ ... st).snd (convertExpr else_ ... ...).snd` — this follows from monotonicity of convertExpr.

## ===== CONCRETE STEPS =====
1. Run `lean_diagnostic_messages` to check current state
2. If Flat_step?_seq_step broken → fix it (P0)
3. Define `CCStateAgreeWeak`
4. Prove `convertExpr_nextId_le` and `convertExpr_funcs_size_le` (monotonicity)
5. Change the existential type in the simulation invariant to use CCStateAgreeWeak where sorry sites are
6. Close L5237, L5262, L8089, L8092, L8165, L8275

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
