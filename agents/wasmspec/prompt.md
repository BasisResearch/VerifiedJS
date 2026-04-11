# wasmspec — CLOSE PRESERVATION SORRIES + COMPOUND HasReturnInHead

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## ⚠️ YOUR LAST RUN CRASHED (exit code 1 at 06:34). Check state before continuing.

## STATUS
- Total: 47 sorries (ANF 32, CC 15).
- Your architecture from the 04:15 run is in place (Steps_compound_error_lift, hasReturnInHead_return_steps)
- hasAbruptCompletion_step_preserved: PROVED (by proof agent)
- NoNestedAbrupt_step_preserved: PROVED (by proof agent)

## P0: CLOSE 3 PRESERVATION SORRIES (L13312, L13328, L13344)

These are in `hasReturnInHead_return_steps`, seq_left case. Each needs:
```lean
∀ smid evs1, Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs1 smid →
    evs1.length ≤ evs.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1
```

### APPROACH: Prove a `Steps_preserves` lemma

Add this in the proof file (near `Steps_compound_error_lift`):

```lean
/-- Each Flat.step? preserves funcs, and appends exactly one event to trace.
    callStack is preserved when NoNestedAbrupt holds. -/
private theorem step?_preserves_funcs_trace
    (sf : Flat.State) (t : Flat.Event) (sf' : Flat.State)
    (hstep : Flat.step? sf = some (t, sf')) :
    sf'.funcs = sf.funcs ∧ sf'.trace = sf.trace ++ [t] := by
  cases sf with | mk e env heap trace funcs cs =>
  simp only [Flat.step?] at hstep
  sorry -- fill by cases on e, each is rfl/rfl
```

Then prove `Steps_preserves_funcs_trace` by induction on Steps:
```lean
private theorem Steps_preserves_funcs_trace
    (sf : Flat.State) (evs : List Flat.Event) (sf' : Flat.State)
    (hsteps : Flat.Steps sf evs sf') :
    sf'.funcs = sf.funcs ∧ sf'.trace = sf.trace ++ evs := by
  induction hsteps with
  | refl => simp
  | tail hsteps hstep ih =>
    obtain ⟨hf1, ht1⟩ := ih
    obtain ⟨hf2, ht2⟩ := step?_preserves_funcs_trace _ _ _ hstep.h
    exact ⟨hf2.trans hf1, by rw [ht2, ht1]; simp [List.append_assoc]⟩
```

For callStack preservation, you need the NoNestedAbrupt + HasReturnInHead context. Under these conditions, no function calls COMPLETE, so step? never modifies callStack.

### STEP-BY-STEP:
1. Search: `lean_local_search "step?_preserves"` — check if helpers exist
2. Prove `step?_preserves_funcs_trace` by exhaustive case analysis on `sf.expr`
3. Prove `Steps_preserves_funcs_trace` by induction on Steps
4. For callStack: prove `step?_preserves_callStack` under NoNestedAbrupt (no call return)
5. Apply to L13312, L13328, L13344 — replace each sorry with the lemma

### CONCRETE APPLICATION at L13312:
```lean
have hpres : ∀ smid evs1, Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs1 smid →
    evs1.length ≤ evs.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1 := by
  intro smid evs1 hsteps _
  obtain ⟨hf, ht⟩ := Steps_preserves_funcs_trace _ _ _ hsteps
  exact ⟨hf, Steps_preserves_callStack _ _ _ hsteps hna_sub, ht⟩
```

## P1: CLOSE REMAINING COMPOUND CASES (L13353)

After P0, expand `| _ => sorry` at L13353 into explicit constructor matches. Each follows the SAME pattern as the seq_left case (L13296-L13352):
1. Decompose normalizeExpr for the compound form
2. Get depth bound for sub-expression
3. Apply IH on sub-expression
4. Lift through compound wrapper via Steps_compound_error_lift
5. Apply the preservation lemma from P0

Do 5-6 constructors at a time. Verify after each batch.

## P2: COMPOUND HasAwaitInHead + HasYieldInHead (L13709, L13882)

Same architecture as HasReturnInHead. Apply the same pattern from P0-P1.

## P3: REMAINING (L12969, L13938, L13942, L13943)

Run `lean_goal` on each (or read context). Use same compound lifting approach.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — Steps preservation + compound expansion" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
