# proof — FIX BROKEN BUILD THEN CLOSE ANF SORRIES

## PRIORITY 0: BUILD IS BROKEN — FIX IMMEDIATELY

`EmitCorrect.lean:60` has a type mismatch. `IR.EmitSimRel.init` now takes 5 args:
`EmitSimRel.init s t hemit hmem_pos hmem_nomax`

### Fix EmitCorrect.lean (exact replacement for lines 54-61):
```lean
/-- Emit preserves behavior: every IR trace maps to a Wasm trace. -/
theorem emit_behavioral_correct (s : IR.IRModule) (t : Wasm.Module)
    (h : emit s = .ok t)
    (hmem_pos : 0 < s.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : MemType),
      s.memories[i]? = some mt → mt.lim.max = none) :
    ∀ trace, IR.IRBehaves s trace →
      Wasm.Behaves t (IR.traceListToWasm trace) := by
  intro trace ⟨sf, hsteps, hhalt⟩
  obtain ⟨w', hwsteps, hrel'⟩ := emit_sim_steps s t h _ _ _ _
    (IR.EmitSimRel.init s t h hmem_pos hmem_nomax) hsteps
  exact ⟨w', hwsteps, IR.EmitSimRel.halt_sim s t _ _ hrel' hhalt⟩
```

### Then fix EndToEnd.lean line 61 — propagate preconditions:
Add to `flat_to_wasm_correct` signature (after `hwf_flat`):
```lean
    (hmem_pos : 0 < ir.memories.size)
    (hmem_nomax : ∀ (i : Nat) (mt : Wasm.MemType),
      ir.memories[i]? = some mt → mt.lim.max = none) :
```
And on line 61, change:
```lean
    exact emit_behavioral_correct ir wasm hemit _
```
to:
```lean
    exact emit_behavioral_correct ir wasm hemit hmem_pos hmem_nomax _
```

**Build after fixing: `lake build VerifiedJS`. It MUST pass before doing anything else.**

## PRIORITY 1: CLOSE ANF HELPER SORRIES (normalizeExpr_labeled_step_sim)

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean`

The proof agent log at 04:30 identified the correct approach. The 3 helper sorries (L1253, L1285, L1302) need **depth induction**, not simple case analysis.

**Recommended refactor**: Replace the `cases e` in `normalizeExpr_labeled_step_sim` with:
```lean
  induction e using Flat.Expr.depth.lt_wfRel.wf.induction with
  | ind e ih => cases e with ...
```

For compound cases (let, seq, if, throw, await, return some, yield some):
1. Unfold normalizeExpr
2. Show the `.labeled` must come from a sub-expression (the continuation k never produces .labeled since k is trivial-preserving)
3. Apply IH on the sub-expression (smaller depth)

The jsspec agent has written no-confusion lemmas in `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` — check if they exist and integrate them into `Convert.lean` BEFORE `end VerifiedJS.ANF`.

## PRIORITY 2: CLOSE STRUCTURAL CASES (let, seq, if)

After helper sorries are done:
- L1382 (let): `normalizeExpr (.let n r b) k` = `bindComplex r (fun fresh => normalizeExpr (.seq (.assign fresh r) b) k)`. ANF step evaluates rhs, extends env, continues with body.
- L1384 (seq): `normalizeExpr (.seq a b) k` = `normalizeExpr a (fun _ => normalizeExpr b k)`. If a is value → skip to b. If a steps → inner step.
- L1386 (if): Branch on condition trivial value. Each branch evaluates to normalizeExpr of then_/else_.

Use the var-found case (around L1229-1265) as a template for constructing SimRel witnesses.

## CASES TO SKIP
- L1422 (break), L1424 (continue): semantic mismatch, leave as sorry

## WORKFLOW
1. Fix EmitCorrect.lean and EndToEnd.lean FIRST
2. `lake build VerifiedJS` — verify it passes
3. Then work on ANF sorries
4. `lean_goal` at sorry → `lean_multi_attempt` → edit → build

## Log progress to agents/proof/log.md
