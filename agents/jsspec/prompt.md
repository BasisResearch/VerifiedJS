# jsspec — Fix 3 hne callers + CCStateAgree

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS: 15 sorries in CC. 3 are NEW error-propagation sorries.

## P0: FIX 3 ERROR-PROPAGATION SORRIES (BLOCKING)

These 3 sorries at L5090, L5182, L5420 were added for the `hne` argument to `Flat_step?_let_step`, `Flat_step?_assign_step`, `Flat_step?_seq_step`:

### L5090, L5182, L5420 — hne for let/assign/seq

These need `t ≠ .error msg` where `t` is the event from `Flat.step? { sf with expr := convertExpr e ... }`.

**Approach A (restructure — RECOMMENDED)**: Instead of using `Flat_step?_let_step` which requires `hne`, branch on whether `t` is an error:
```lean
match hm : Flat.step? { sf with expr := ... } with
| some (t, sa) =>
  match ht : t with
  | .error msg =>
    -- Error case: use Flat_step?_let_error / seq_error / assign_error
    -- This propagates the error through the compound expression
    have heq := Flat_step?_let_error sf name body _ hfnv msg sa (by rw [← ht]; exact hm)
    rw [heq] at hstep; simp at hstep
    obtain ⟨rfl, hsf'eq⟩ := hstep
    -- Now ev = .error msg, need to show simulation still holds
    sorry -- may need error-event simulation lemma
  | _ =>
    -- Non-error case: use existing Flat_step?_let_step
    have hne : ∀ msg, t ≠ .error msg := by cases t <;> simp_all [ht]
    have heq := Flat_step?_let_step sf name body _ hfnv t sa hm hne
    -- rest as before
```

**Approach B (quick sorry)**: If the error case can't arise for well-formed converted expressions (because `convertExpr` of a supported expression shouldn't produce error events on sub-stepping), prove a helper:
```lean
private theorem convertExpr_step_no_error (e : Core.Expr) (hsupp : e.supported = true) ...
    (hstep : Flat.step? { sf with expr := (Flat.convertExpr e ...).fst } = some (t, sa)) :
    ∀ msg, t ≠ .error msg
```

Use `lean_goal` at L5090 to check available hypotheses. Check if `Flat_step?_let_error` / `Flat_step?_seq_error` / `Flat_step?_assign_error` exist (they should, after the error propagation changes).

## P1: CCStateAgree (only after P0 is done)

Target sorries: L5261, L5287, L8115, L8192, L8308
These are all blocked by CCStateAgree (Blocker P). The viable fix is Path A: make `convertExpr` state-independent via position-based naming. This requires editing `ClosureConvert.lean` definitions — check with supervisor before attempting.

## Remaining CC sorries (12 total after P0):
- L4927: multi-step gap (Blocker T) — BLOCKED
- L5261, L5287: CCStateAgree if-branch — BLOCKED (Blocker P)
- L5855: FuncsCorr invariant — BLOCKED (Blocker Q)
- L6066, L6075: multi-step newObj gap — BLOCKED
- L6714: getIndex string — UNPROVABLE
- L7956: functionDef — BLOCKED (Blocker S)
- L8115, L8118: tryCatch — BLOCKED (Blocker P)
- L8192: CCStateAgree — BLOCKED (Blocker P)
- L8308: while_ CCState — BLOCKED (Blocker P)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run — fixing 3 hne callers" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
