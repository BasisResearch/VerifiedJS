# wasmspec — noCallFrameReturn PRESERVATION + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T15:30
- YOUR sorries: L19375, L32638 = **2 sorry lines** (was 4; you closed L18163 + L32673)
- L19375: HasNonCallFrameTryCatchInHead (was L19377) — needs approach A/B/C from comment
- L32638: noCallFrameReturn preservation in anfConvert_step_star_ncfr
- All in ANFConvertCorrect.lean

## P1: DONE ✓ (closed 2026-04-12T14:25)
L32673 precondition added. L18163 restructured into `suffices` proof.

## P0: noCallFrameReturn preservation (L32638) — MEDIUM DIFFICULTY

```lean
sorry -- in anfConvert_step_star_ncfr, needs case analysis mirroring anfConvert_step_star
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

## P2: HasNonCallFrameTryCatch (L19375) — HARD, DO AFTER P0

This is the `sorry` at L19375 passed to `HasReturnInHead_Steps_steppable_core`.
The comment at L19375-19389 lists 3 viable approaches (A/B/C).
**Approach A** (thread noCallFrameReturn as precondition) aligns with your P1 work.
Now that `noCallFrameReturn` precondition is threaded through `anfConvert_correct`,
check if it's available in the context at L19375 and can close this sorry.

## EXECUTION ORDER:
1. ~~P1 (L32673)~~ — DONE ✓
2. **P0 (L32638)** — noCallFrameReturn preservation in anfConvert_step_star_ncfr
3. **P2 (L19375)** — HasNonCallFrameTryCatchInHead, try Approach A with noCallFrameReturn precondition

## Also needed: `hfuncs_ncfr` precondition
When you add `noCallFrameReturn_steps_preserved`, you'll also need `anfConvert_correct` to have:
```lean
(hfuncs_ncfr_prog : ∀ (i : Nat) (fd : Flat.FuncDef), s.functions[i]? = some fd → noCallFrameReturn fd.body = true)
```
Add this alongside `hncfr_prog`.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
