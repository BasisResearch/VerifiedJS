# wasmspec — 24 individual sorries in if_branch zones. Prove second-position cases.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~2.3GB free. USE LSP ONLY — no builds.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9901-9996 (labeled_branch_step second-position)
- jsspec may work on list cases
- **YOU** own L13671-13705 and L14601-14635 ONLY

## YOUR 24 SORRIES (12 per theorem):

### normalizeExpr_if_branch_step (true) — L13671-13705:
```
    | binary_rhs => sorry      -- L13671
    | call_env => sorry        -- L13672
    | call_args => sorry       -- L13673
    | newObj_env => sorry      -- L13697
    | newObj_args => sorry     -- L13698
    | setProp_val => sorry     -- L13699
    | getIndex_idx => sorry    -- L13700
    | setIndex_idx => sorry    -- L13701
    | setIndex_val => sorry    -- L13702
    | makeEnv_values => sorry  -- L13703
    | objectLit_props => sorry -- L13704
    | arrayLit_elems => sorry  -- L13705
```

### normalizeExpr_if_branch_step_false — L14601-14635 (mirror of above)

## EXACT TEMPLATE: seq_right at L13230-13304

The seq_right case in YOUR OWN THEOREM is the EXACT pattern! Look at L13230-13304:
1. `Classical.em (HasIfInHead b)` to split on first sub-expr
2. If HasIfInHead: IH on first sub-expr + `Steps_seq_ctx_b` (L13236-13255)
3. If ¬HasIfInHead: `no_if_head_implies_trivial_chain` → `trivialChain_eval_value` → discard step → IH on second sub-expr (L13256-13304)

### For binary_rhs (L13671):
```lean
    | binary_rhs h_rhs =>
      rename_i lhs rhs op  -- CHECK with lean_goal!
      simp only [ANF.normalizeExpr] at hnorm
      rcases Classical.em (HasIfInHead lhs) with h_lhs_if | h_lhs_noif
      · -- HasIfInHead lhs: IH + Steps_binary_lhs_ctx_b
        have hlhs_depth : lhs.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
        obtain ⟨sf_lhs, evs_lhs, hsteps_lhs, hsil_lhs, henv_lhs, hheap_lhs, hfuncs_lhs, hcs_lhs,
          htrace_lhs, hpres_lhs, ⟨n_lhs, m_lhs, hnorm_lhs⟩, hewf_lhs⟩ :=
          ih lhs hlhs_depth h_lhs_if env heap trace funcs cs _ n m cond then_ else_ v
            hnorm (fun x hfx => hewf x (VarFreeIn.binary_lhs _ _ _ _ hfx)) heval hbool
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
      · -- ¬HasIfInHead lhs: trivialChain → value → IH on rhs
        have htc_lhs := no_if_head_implies_trivial_chain lhs.depth lhs (Nat.le_refl _)
          (fun _ => ANF.normalizeExpr rhs K) cond then_ else_ n m hnorm h_lhs_noif
        have hnorm_rhs : (ANF.normalizeExpr rhs K).run n = .ok (.if cond then_ else_, m) := by
          rwa [normalizeExpr_trivialChain_passthrough lhs.depth lhs (Nat.le_refl _) htc_lhs] at hnorm
        obtain ⟨v_lhs, evs_lhs, hsteps_lhs, hnoerr_lhs, _, hpres_lhs⟩ :=
          trivialChain_eval_value (trivialChainCost lhs) lhs env heap trace funcs cs
            htc_lhs (Nat.le_refl _) (fun x hfx => hewf x (VarFreeIn.binary_lhs _ _ _ _ hfx))
        obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
          Steps_binary_lhs_ctx_b op rhs hsteps_lhs (fun ev hev msg => hnoerr_lhs ev hev msg)
            (fun smid evs1 h _ => hpres_lhs smid evs1 h)
        have hws_eq : ws = ⟨.binary op (.lit v_lhs) rhs, env, heap, trace ++ evs_lhs, funcs, cs⟩ := by
          cases ws; simp_all
        rw [hws_eq] at hwsteps
        -- Discard step: .binary op (.lit v_lhs) rhs
        -- If rhs is not a value: Flat.step? steps into rhs → binary_rhs context
        -- Need to check if binary with lit lhs steps directly or evaluates rhs first
        -- Use lean_hover_info on Flat.step? to check binary case
        sorry
```

### PRIORITY ORDER:
1. **binary_rhs** (L13671/L14601) — template above
2. **setProp_val** (L13699/L14629) — obj→value, then IH on val
3. **call_env** (L13672/L14602) — funcExpr→value, then IH on envExpr
4. **newObj_env** (L13697/L14627) — same pattern as call_env
5. **getIndex_idx** (L13700/L14630) — obj→value, then IH on idx
6. **setIndex_idx, setIndex_val** (L13701-13702/L14631-14632)
7. List cases (L13673, L13698, L13703-13705) — harder

### DO BOTH THEOREMS: Each proved case in if_branch_step should be mirrored in if_branch_step_false.

### APPROACH for each:
1. `lean_goal` at the sorry line
2. Check `rename_i` variable order via the goal
3. Write the HasIfInHead sub-case (copy first-position template from same theorem)
4. Write the ¬HasIfInHead sub-case (adapt L13256-13304)
5. Verify with `lean_diagnostic_messages`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
