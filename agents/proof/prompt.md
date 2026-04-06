# proof — Close second-position sorries in labeled_branch_step

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~2.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13593-13627 and L14523-14557 zones (if_branch individual cases)
- jsspec may work on list cases (L9919, L9944-9947)
- **YOU** own L9822-9918 and L9943 (second-position + newObj_env)
- DO NOT touch wasmspec or jsspec zones

## ===== YOUR 8 SORRIES (all second-position) =====

These are at lines: L9822 (seq_right), L9823 (binary_rhs), L9846 (setProp_val), L9869 (getIndex_idx), L9893 (setIndex_idx), L9894 (setIndex_val), L9918 (call_env), L9943 (newObj_env).

## ===== EXACT TEMPLATE: seq_right at L13155-13226 =====

The if_branch_step `seq_right` case at L13155-13226 is the EXACT pattern. Adapt it:
- Replace `HasIfInHead` with `HasLabeledInHead`
- Replace `no_if_head_implies_trivial_chain` with `no_labeled_head_implies_trivial_chain` (L9201)
- Replace `cond then_ else_ v` parameters with `label body` parameters
- The trivialChain machinery is identical

### Pattern for seq_right (L9822):
```lean
    | seq_right h_right =>
      rename_i a b  -- b=left (seq first), a=right (has label)
      simp only [ANF.normalizeExpr_seq'] at hnorm
      rcases Classical.em (HasLabeledInHead b label) with h_b_lab | h_b_nolab
      · -- HasLabeledInHead b: IH on b, wrap in .seq · a
        have hb_depth : b.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
        obtain ⟨sf_b, evs_b, hsteps_b, hsil_b, henv_b, hheap_b, hfuncs_b, hcs_b,
          htrace_b, hpres_b, ⟨n_b, m_b, hnorm_b⟩, hewf_b⟩ :=
          ih b hb_depth label h_b_lab env heap trace funcs cs _ n m body
            hnorm (fun x hfx => hewf x (VarFreeIn.seq_l _ _ _ hfx))
        obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
          Steps_seq_ctx_b a hsteps_b
            (fun ev hev msg => by rw [hsil_b ev hev]; exact Core.TraceEvent.noConfusion)
            hpres_b
        refine ⟨ws, evs_b, hwsteps, hsil_b, hwenv.trans henv_b, hwheap.trans hheap_b,
          hwfuncs, hwcs, by rw [hwtrace, htrace_b], ?_, ?_, ?_⟩
        · exact Steps_ctx_lift_pres (.seq · a)
            (fun s inner hv t si hs he => step?_seq_ctx s inner a hv t si hs he)
            hsteps_b (fun ev hev msg => by rw [hsil_b ev hev]; exact Core.TraceEvent.noConfusion) hpres_b
        · exact ⟨n_b, m_b, by rw [hwexpr]; simp only [ANF.normalizeExpr_seq']; exact hnorm_b⟩
        · rw [hwexpr, hwenv, henv_b]; exact fun x hfx => by
            cases hfx with
            | seq_l _ _ _ h => exact henv_b ▸ hewf_b x h
            | seq_r _ _ _ h => exact hewf x (VarFreeIn.seq_r _ _ _ h)
      · -- ¬HasLabeledInHead b: b is trivialChain, eval → value, discard, IH on a
        have htc_b := no_labeled_head_implies_trivial_chain b.depth b (Nat.le_refl _)
          (fun _ => ...) label body n m hnorm h_b_nolab
        -- ADAPT rest from L13181-13226 (if_branch seq_right ¬HasIfInHead case)
        sorry
```

### Pattern for binary_rhs (L9823):
Same as seq_right but:
- Expression is `.binary op lhs rhs` where `lhs` must eval to value first
- `Classical.em (HasLabeledInHead lhs label)` — if lhs has it, IH + `Steps_binary_lhs_ctx_b`
- If ¬HasLabeledInHead lhs: `no_labeled_head_implies_trivial_chain` → lhs is trivialChain → `trivialChain_eval_value` → get `.lit v` → discard → IH on rhs with `Steps_binary_rhs_ctx_b`

### Pattern for setProp_val (L9846):
- Expression is `.setProp obj prop val` — obj evals to value first
- `Classical.em (HasLabeledInHead obj label)` — same split
- `Steps_setProp_obj_ctx_b` for lhs, discard step for `.setProp (.lit v) prop val → ???`, then IH on val with `Steps_setProp_val_ctx_b`

### For ALL second-position cases:
1. `lean_goal` at the sorry line to see exact proof state
2. `simp only [ANF.normalizeExpr] at hnorm` to unfold
3. `Classical.em (HasLabeledInHead <first_sub> label)` to split
4. HasLabeledInHead case: IH + Steps_*_ctx_b (same as first-position)
5. ¬HasLabeledInHead case: trivialChain → eval → discard → IH on second sub
6. Wire up existentials following L13200-13226

## APPROACH
1. Start with seq_right (L9822) — most infrastructure already in L13155-13226
2. Then binary_rhs (L9823) — similar
3. Then single-valued: setProp_val, getIndex_idx, setIndex_idx, setIndex_val
4. Then call_env, newObj_env (needs funcExpr→value first)

## DO NOT TOUCH (other agents):
- L9919, L9944-L9947 (list cases — jsspec)
- L13593-13627, L14523-14557 (if_branch — wasmspec)
- L11194-L11849 (compound cases — defer)
- L15398+ (blocked cases)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
