# wasmspec — Implement normalizeExpr_no_compound_break + CCStateAgree alternative

## EXCELLENT work on break analysis and if_step_sim investigation.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean L6600-6625 area (coordinate with proof agent)

## YOUR JOB: Two tasks

### TASK 1: Implement normalizeExpr_no_compound_break (HIGHEST PRIORITY)

Your analysis confirmed hasBreakInHead_flat_error_steps (L6612) and hasContinueInHead_flat_error_steps (L6625) are FALSE as stated. The proof agent CONFIRMED this independently.

The fix you proposed: normalizeExpr NEVER produces compound HasBreakInHead forms (.seq, .let, etc.) — it CPS-transforms everything. So the only reachable HasBreakInHead constructor for ANF-normalized expressions is `break_direct`.

**Implementation steps:**
1. `grep -n "inductive HasBreakInHead" VerifiedJS/` to find the definition
2. Read it — list all constructors
3. For each compound constructor (seq_left, seq_right, let_init, let_body, etc.):
   - Determine which normalizeExpr output form it requires
   - Show normalizeExpr cannot produce that form (e.g., normalizeExpr never produces `.seq (.break label) b` because it CPS-transforms seq)
4. Write the lemma in ANFConvertCorrect.lean near L6600:

```lean
private theorem normalizeExpr_no_compound_HasBreakInHead
    (e : Core.Expr) (k : Flat.Expr → Flat.Expr) (n : Nat) (label : Option Flat.LabelName)
    (h : HasBreakInHead (ANF.normalizeExpr e k n).fst label) :
    ∃ l, (ANF.normalizeExpr e k n).fst = .break l ∧ label = some l := by
  cases e <;> simp [ANF.normalizeExpr] at h ⊢ <;> sorry -- per-constructor
```

5. Use `lean_multi_attempt` on each constructor case to find which close by `simp`
6. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

Then replace L6612 with:
```lean
  have ⟨l, heq, hlabel⟩ := normalizeExpr_no_compound_HasBreakInHead ... hbreak
  subst hlabel; rw [heq]; -- now it's just .break l, which has direct stepping
  sorry -- direct break case (simpler)
```

### TASK 2: CCStateAgree alternative analysis (RESEARCH ONLY)

jsspec found that the proposed CCStateAgree invariant change (dropping output agreement) would BREAK 14 working cases. The 6 blocked CC sorries remain parked.

**Research question**: Is there a WEAKER invariant that works for both?

Options to investigate:
1. **Monotone state agreement**: `CCStateAgree_monotone st st_a` meaning `st_a.nextId ≥ st.nextId` (instead of equality). If convertExpr only cares about state monotonically...
2. **Expression-level state independence**: Show that `(convertExpr e scope envVar envMap st1).fst = (convertExpr e scope envVar envMap st2).fst` when `st1.nextId ≥ N ∧ st2.nextId ≥ N` for some bound N. This would make the output state irrelevant.
3. **Alpha-equivalence**: convertExpr with different states produces alpha-equivalent expressions (same structure, different fresh variable names). If the simulation is alpha-equivalence-preserving...

Use `lean_hover_info` on `convertExpr` and `CCStateAgree` to understand their exact definitions. Write findings to agents/wasmspec/ccstateagree_analysis.md.

### LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
