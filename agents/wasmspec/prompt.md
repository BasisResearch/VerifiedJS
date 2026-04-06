# wasmspec — 24 individual sorries in if_branch zones. Prove second-position cases.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~2.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9822-9947 (labeled_branch_step second-position)
- jsspec may work on list cases
- **YOU** own L13593-13627 and L14523-14557 ONLY

## YOUR 24 SORRIES (12 per theorem):

### normalizeExpr_if_branch_step (true) — L13593-13627:
```
    | binary_rhs => sorry      -- L13593
    | call_env => sorry        -- L13594
    | call_args => sorry       -- L13595
    | newObj_env => sorry      -- L13619
    | newObj_args => sorry     -- L13620
    | setProp_val => sorry     -- L13621
    | getIndex_idx => sorry    -- L13622
    | setIndex_idx => sorry    -- L13623
    | setIndex_val => sorry    -- L13624
    | makeEnv_values => sorry  -- L13625
    | objectLit_props => sorry -- L13626
    | arrayLit_elems => sorry  -- L13627
```

### normalizeExpr_if_branch_step_false — L14523-14557 (mirror of above)

## EXACT TEMPLATE: seq_right at L13155-13226

The seq_right case in YOUR OWN THEOREM already shows the second-position pattern! Look at L13155-13226. It uses:
1. `Classical.em (HasIfInHead b)` to split on first sub-expr
2. If HasIfInHead: IH on first sub-expr + `Steps_seq_ctx_b`
3. If ¬HasIfInHead: `no_if_head_implies_trivial_chain` → `trivialChain_eval_value` → discard step → IH on second sub-expr

### For binary_rhs (L13593):
```lean
    | binary_rhs h_rhs =>
      rename_i lhs rhs op  -- check rename_i order with lean_goal!
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
      · -- ¬HasIfInHead lhs: trivialChain → value → discard → IH on rhs
        -- ADAPT L13178-13226 (seq_right ¬HasIfInHead case)
        -- Key differences: use Steps_binary_lhs_ctx_b for lifting, different discard step
        sorry
```

### PRIORITY ORDER:
1. **binary_rhs** (L13593) — most similar to seq_right, template above
2. **call_env** (L13594) — funcExpr→value, then IH on envExpr
3. **newObj_env** (L13619) — same pattern as call_env
4. **setProp_val** (L13621) — obj→value, then IH on val
5. **getIndex_idx** (L13622) — obj→value, then IH on idx
6. **setIndex_idx, setIndex_val** (L13623-13624) — multi-position
7. List cases (L13595, L13620, L13625-13627) — harder, attempt if time

### DO BOTH THEOREMS: Each proved case in if_branch_step should be mirrored in if_branch_step_false.

### APPROACH for each:
1. `lean_goal` at the sorry line
2. Check `rename_i` variable order via the goal
3. `simp only [ANF.normalizeExpr] at hnorm`
4. `Classical.em (HasIfInHead <first_sub>)` to split
5. HasIfInHead case: IH + Steps_*_ctx_b (like first-position template)
6. ¬HasIfInHead case: trivialChain → eval → discard → IH (adapt L13178-13226)
7. Wire up existentials

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
