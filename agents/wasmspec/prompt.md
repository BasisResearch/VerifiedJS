# wasmspec — noCallFrameReturn PRESERVATION + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T14:05
- YOUR sorries: L18163, L19377, L32642, L32673 = **4 sorry lines**
- All in ANFConvertCorrect.lean

## P1: noCallFrameReturn for source (L32673) — START HERE, EASIEST

```lean
have hncfr_init : noCallFrameReturn (Flat.initialState s).expr = true :=
  sorry /- noCallFrameReturn for source program -/
```

`Flat.initialState s` has `.expr = s.main` (see Flat/Semantics.lean:1213).
So the goal is: `noCallFrameReturn s.main = true`.

**This needs a precondition on the source program.** Check if `anfConvert_correct` (L32659) already has one. Currently it has:
- `hna_prog : NoNestedAbrupt s.main`
- `hfuncs_na_prog`, `hfuncs_ac_prog`

**It does NOT have `noCallFrameReturn s.main = true`.**

**Fix:** Add a new precondition to `anfConvert_correct`:
```lean
theorem anfConvert_correct (s : Flat.Program) (t : ANF.Program)
    (h : ANF.convert s = .ok t)
    (hwf_prog : ExprWellFormed s.main (Flat.initialState s).env)
    (hna_prog : NoNestedAbrupt s.main)
    (hncfr_prog : noCallFrameReturn s.main = true)  -- ADD THIS
    (hfuncs_na_prog : ∀ (i : Nat) (fd : Flat.FuncDef), s.functions[i]? = some fd → NoNestedAbrupt fd.body)
    (hfuncs_ac_prog : ∀ (i : Nat) (fd : Flat.FuncDef), s.functions[i]? = some fd → hasAbruptCompletion fd.body = false) :
```

Then L32673 becomes `exact hncfr_prog`.

**IMPORTANT:** After adding this precondition, check that ALL callers of `anfConvert_correct` can provide it. Search for callers:
```
lean_local_search query="anfConvert_correct" file="VerifiedJS/Proofs/ANFConvertCorrect.lean"
```
Also check EndToEnd.lean for callers.

## P0: noCallFrameReturn preservation (L32642) — MEDIUM DIFFICULTY

```lean
have hncfr2 : noCallFrameReturn sf2.expr = true := sorry
```

**Need a new theorem:** `noCallFrameReturn_step_preserved`

Follow the EXACT pattern of `NoNestedAbrupt_step_preserved` (L27239):
```lean
private theorem noCallFrameReturn_step_preserved (sf sf' : Flat.State) (ev : Core.TraceEvent)
    (hncfr : noCallFrameReturn sf.expr = true)
    (hfuncs_ncfr : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → noCallFrameReturn fd.body = true)
    (hstep : Flat.step? sf = some (ev, sf')) :
    noCallFrameReturn sf'.expr = true := by
  obtain ⟨e, env, heap, trace, funcs, cs⟩ := sf
  simp only [] at hncfr hfuncs_ncfr hstep ⊢
  -- Case split on e, unfold step?, check that no case introduces "__call_frame_return__"
  sorry
```

Then lift to Steps:
```lean
private theorem noCallFrameReturn_steps_preserved {sf sf' : Flat.State} {evs : List Core.TraceEvent}
    (hncfr : noCallFrameReturn sf.expr = true)
    (hfuncs_ncfr : ∀ (i : Nat) (fd : Flat.FuncDef), sf.funcs[i]? = some fd → noCallFrameReturn fd.body = true)
    (hsteps : Flat.Steps sf evs sf') :
    noCallFrameReturn sf'.expr = true := by
  induction hsteps with
  | refl => exact hncfr
  | tail hstep _ ih =>
    have hfuncs_eq := Flat.step_preserves_funcs hstep
    exact ih (noCallFrameReturn_step_preserved _ _ _ hncfr hfuncs_ncfr hstep)
      (fun i fd h => hfuncs_ncfr i fd (hfuncs_eq ▸ h))
```

**KEY INSIGHT:** The only place `"__call_frame_return__"` is introduced in Flat.step? is during call evaluation (the call frame mechanism). `noCallFrameReturn` is designed to detect these. If the initial expression satisfies `noCallFrameReturn`, stepping preserves it because:
1. Sub-expression stepping preserves noCallFrameReturn by structural recursion
2. Call evaluation introduces `__call_frame_return__` BUT only in tryCatch wrappers that are internal to the call step — the RESULT expression after call-return won't have it if the function body doesn't

**WARNING:** The call case is the hard part. When Flat.step? processes `.call f env args`, it wraps the body in `tryCatch body "__call_frame_return__" ...`. This means `noCallFrameReturn` is NOT preserved through call steps!

**Alternative approach:** If call steps break preservation, then `noCallFrameReturn` might need the `hfuncs_ncfr` precondition to guarantee function bodies don't have it, AND the preservation might need to track that the tryCatch wrapper with `__call_frame_return__` only appears transiently during call execution.

Check `Flat.step?` for the call case:
```
lean_hover_info file="VerifiedJS/Flat/Semantics.lean" line=1100 column=0
```

## P2: HasNonCallFrameTryCatch (L18163, L19377) — HARD, DO AFTER P0/P1

These depend on P0. Skip until P0 and P1 are done.

## EXECUTION ORDER:
1. **P1 (L32673)** — Add precondition to anfConvert_correct, verify callers can provide it
2. **P0 (L32642)** — Write noCallFrameReturn_step_preserved, following NoNestedAbrupt_step_preserved pattern
3. **P2 (L18163, L19377)** — Only after P0/P1 done

## Also needed: `hfuncs_ncfr` precondition
When you add `noCallFrameReturn_steps_preserved`, you'll also need `anfConvert_correct` to have:
```lean
(hfuncs_ncfr_prog : ∀ (i : Nat) (fd : Flat.FuncDef), s.functions[i]? = some fd → noCallFrameReturn fd.body = true)
```
Add this alongside `hncfr_prog`.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
