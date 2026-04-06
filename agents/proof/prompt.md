# proof — Close second-position sorries in labeled_branch_step

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~2.3GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13671-13705 and L14601-14635 zones (if_branch individual cases)
- jsspec may work on list cases (L9997, L10022-10025)
- **YOU** own L9901-L9996 (second-position cases)
- DO NOT touch wasmspec or jsspec zones

## ===== YOUR 6 SORRIES (all second-position) =====

These are at lines:
- L9901: `binary_rhs h_rhs => sorry`
- L9924: `setProp_val h_val => sorry`
- L9947: `getIndex_idx h_idx => sorry`
- L9971: `setIndex_idx h_idx => sorry`
- L9972: `setIndex_val h_val => sorry`
- L9996: `call_env h_env => sorry`

## ===== EXACT TEMPLATE: seq_right ¬HasIfInHead case at L13256-13304 =====

This is the EXACT pattern for second-position. The if_branch seq_right at L13256-13304 shows how:
1. `no_X_head_implies_trivial_chain` to get trivialChain for first sub
2. `normalizeExpr_trivialChain_passthrough` to recover IH normalizeExpr for second sub
3. `trivialChain_eval_value` to get the first sub's value
4. `Steps_*_ctx_b` to lift through the context
5. Construct the discard step (e.g., `.seq (.lit v) a → a`)
6. IH on second sub
7. `Steps.append` + `Steps_pres_append` to compose

### For binary_rhs (L9901):
Replace `HasIfInHead` with `HasLabeledInHead`, `cond then_ else_ v` with `label body`:
```lean
    | binary_rhs h_rhs =>
      rename_i lhs rhs op  -- CHECK order with lean_goal!
      simp only [ANF.normalizeExpr] at hnorm
      rcases Classical.em (HasLabeledInHead lhs label) with h_lhs_lab | h_lhs_nolab
      · -- HasLabeledInHead lhs: IH + Steps_binary_lhs_ctx_b
        have hlhs_depth : lhs.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
        obtain ⟨sf_lhs, evs_lhs, hsteps_lhs, hsil_lhs, henv_lhs, hheap_lhs, hfuncs_lhs, hcs_lhs,
          htrace_lhs, hpres_lhs, ⟨n_lhs, m_lhs, hnorm_lhs⟩, hewf_lhs⟩ :=
          ih lhs hlhs_depth label h_lhs_lab env heap trace funcs cs _ n m body
            hnorm (fun x hfx => hewf x (VarFreeIn.binary_lhs _ _ _ _ hfx))
        obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
          Steps_binary_lhs_ctx_b op rhs hsteps_lhs
            (fun ev hev msg => by rw [hsil_lhs ev hev]; exact Core.TraceEvent.noConfusion) hpres_lhs
        refine ⟨ws, evs_lhs, hwsteps, hsil_lhs, hwenv.trans henv_lhs, hwheap.trans hheap_lhs,
          hwfuncs, hwcs, by rw [hwtrace, htrace_lhs], ?_, ?_, ?_⟩
        · exact Steps_ctx_lift_pres (.binary op · rhs)
            (fun s inner hv t si hs he => step?_binary_lhs_ctx s op inner rhs hv t si hs he)
            hsteps_lhs (fun ev hev msg => by rw [hsil_lhs ev hev]; exact Core.TraceEvent.noConfusion) hpres_lhs
        · exact ⟨n_lhs, m_lhs, by rw [hwexpr]; simp only [ANF.normalizeExpr]; exact hnorm_lhs⟩
        · rw [hwexpr, hwenv, henv_lhs]; exact fun x hfx => by
            cases hfx with
            | binary_lhs _ _ _ _ h => exact henv_lhs ▸ hewf_lhs x h
            | binary_rhs _ _ _ _ h => exact hewf x (VarFreeIn.binary_rhs _ _ _ _ h)
      · -- ¬HasLabeledInHead lhs: trivialChain → value → discard → IH on rhs
        -- ADAPT L13256-13304 pattern: replace HasIfInHead→HasLabeledInHead, seq→binary
        have htc_lhs := no_labeled_head_implies_trivial_chain lhs.depth lhs (Nat.le_refl _)
          (fun _ => ANF.normalizeExpr rhs K) label body n m hnorm h_lhs_nolab
        have hnorm_rhs : (ANF.normalizeExpr rhs K).run n = .ok (.labeled label body, m) := by
          rwa [normalizeExpr_trivialChain_passthrough lhs.depth lhs (Nat.le_refl _) htc_lhs] at hnorm
        obtain ⟨v_lhs, evs_lhs, hsteps_lhs, hnoerr_lhs, _, hpres_lhs⟩ :=
          trivialChain_eval_value (trivialChainCost lhs) lhs env heap trace funcs cs
            htc_lhs (Nat.le_refl _) (fun x hfx => hewf x (VarFreeIn.binary_lhs _ _ _ _ hfx))
        obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
          Steps_binary_lhs_ctx_b op rhs hsteps_lhs (fun ev hev msg => hnoerr_lhs ev hev msg)
            (fun smid evs1 h _ => hpres_lhs smid evs1 h)
        -- Then: discard step (.binary op (.lit v_lhs) rhs → ???)
        -- Check what Flat.step? does with .binary op (.lit v_lhs) rhs
        -- If rhs is not a value: step into rhs → Steps_binary_rhs_ctx_b
        -- IH on rhs with hnorm_rhs
        sorry
```

### WORKFLOW for each sorry:
1. `lean_goal` at the sorry line
2. Write the HasLabeledInHead case first (first-position template from L9902-9923)
3. Write the ¬HasLabeledInHead case (adapt L13256-13304)
4. `lean_multi_attempt` to test before editing
5. For the discard step, check what `Flat.step?` does with the specific expression form

## APPROACH
1. Start with binary_rhs (L9901) — template above
2. Then setProp_val (L9924) — same pattern, use Steps_setProp_obj_ctx_b for first-position lifting
3. Then getIndex_idx (L9947)
4. Then setIndex_idx, setIndex_val (L9971-9972)
5. Then call_env (L9996)

## DO NOT TOUCH (other agents):
- L9997, L10022-L10025 (list cases — jsspec)
- L13671-13705, L14601-14635 (if_branch — wasmspec)
- L11272-L11927 (compound/while — defer)
- L15476+ (blocked cases)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
