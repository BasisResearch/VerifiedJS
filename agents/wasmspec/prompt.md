# wasmspec — noCallFrameReturn PRESERVATION + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T16:05
- YOUR sorries: L18163, L19377, L32640 = **3 sorry lines**
- L18163: `exact sorry` — commented-out proof has 39 tactic errors (proof agent taking P4 on this)
- L19377: HasNonCallFrameTryCatchInHead — needs approach A/B/C from comment
- L32640: noCallFrameReturn preservation in anfConvert_step_star_ncfr
- All in ANFConvertCorrect.lean

## IMPORTANT: L18163 IS NOW PROOF AGENT'S JOB
The proof agent has P4 to fix the 39 tactic errors in the commented-out proof at L18163.
**DO NOT** work on L18163. Focus on L32640 and L19377.

## P0: noCallFrameReturn preservation (L32640) — START HERE

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
  cases e <;> simp [Flat.step?, noCallFrameReturn] at hncfr hstep ⊢ <;> sorry
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

**KEY INSIGHT:** General flat-step preservation is FALSE (call introduces tryCatch "__call_frame_return__"). BUT `anfConvert_step_star_ncfr` only applies to ANF-simulation flat steps (a BATCH that resolves the call frame). So you need to prove preservation for the SPECIFIC step sequence produced by the simulation, not for arbitrary flat steps.

**Alternative approach:** Instead of proving general step preservation, prove that anfConvert_step_star's output expression satisfies ncfr by examining each case of the simulation. This mirrors the structure of anfConvert_step_star itself.

1. `lean_goal` at L32640 to get exact context
2. Case split on the ANF expression (mirroring anfConvert_step_star)
3. For each case, show the resulting flat expression preserves noCallFrameReturn

## P2: HasNonCallFrameTryCatch (L19377) — AFTER P0

This sorry passes `¬HasNonCallFrameTryCatchInHead a` to `HasReturnInHead_Steps_steppable_core`.

**Approach A** (thread noCallFrameReturn as precondition):
Now that `noCallFrameReturn` precondition is available in `anfConvert_correct`:
1. `lean_goal` at L19377 to see what hypotheses are available
2. Check if `hncfr_prog` or similar gives `noCallFrameReturn` for the expression
3. Prove that `noCallFrameReturn e = true → ¬HasNonCallFrameTryCatchInHead e`
4. This works because noCallFrameReturn forbids ALL tryCatch with "__call_frame_return__",
   and HasNonCallFrameTryCatchInHead looks for tryCatch that are NOT "__call_frame_return__"
   Wait — that's the OPPOSITE direction. Re-check the definitions.

**Check definitions first:**
```
lean_hover_info file="VerifiedJS/Proofs/ANFConvertCorrect.lean" line=<noCallFrameReturn_def> column=0
lean_hover_info file="VerifiedJS/Proofs/ANFConvertCorrect.lean" line=<HasNonCallFrameTryCatchInHead_def> column=0
```

## EXECUTION ORDER:
1. **P0 (L32640)** — noCallFrameReturn preservation (simulation-specific)
2. **P2 (L19377)** — HasNonCallFrameTryCatchInHead, try Approach A

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
