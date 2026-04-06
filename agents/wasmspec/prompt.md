# wasmspec — 26 individual sorries in if_branch zones. Prove them!

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE, leave it alone
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY

## MEMORY: ~3GB free. USE LSP ONLY — no builds.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9584-9709 zone + L10956-11611 zone
- **YOU** own L13355-13367 and L14263-14275 ONLY

## !! LINE NUMBERS SHIFTED !! Old L13231→L13355, Old L14139→L14263 (+124 lines from proof agent decomposition)

## YOUR 26 SORRIES (13 per theorem):

### normalizeExpr_if_branch_step (true branch) — L13355-13367:
```
    | binary_rhs => sorry      -- L13355
    | call_env => sorry        -- L13356
    | call_args => sorry       -- L13357
    | newObj_func => sorry     -- L13358
    | newObj_env => sorry      -- L13359
    | newObj_args => sorry     -- L13360
    | setProp_val => sorry     -- L13361
    | getIndex_idx => sorry    -- L13362
    | setIndex_idx => sorry    -- L13363
    | setIndex_val => sorry    -- L13364
    | makeEnv_values => sorry  -- L13365
    | objectLit_props => sorry -- L13366
    | arrayLit_elems => sorry  -- L13367
```

### normalizeExpr_if_branch_step_false — L14263-14275 (mirror of above)

## HELPERS AVAILABLE (ALL EXIST):
| Helper | For case |
|--------|----------|
| Steps_binary_rhs_ctx_b op lv | binary_rhs |
| Steps_call_env_ctx_b fv args | call_env |
| Steps_call_arg_ctx_b funcExpr envExpr done remaining | call_args |
| Steps_newObj_func_ctx_b envExpr args | newObj_func |
| Steps_newObj_env_ctx_b fv args | newObj_env |
| Steps_newObj_arg_ctx_b funcExpr envExpr done remaining | newObj_args |
| Steps_setProp_val_ctx_b ov prop | setProp_val |
| Steps_getIndex_idx_ctx_b ov | getIndex_idx |
| Steps_setIndex_idx_ctx_b ov val | setIndex_idx |
| Steps_setIndex_val_ctx_b ov iv | setIndex_val |
| Steps_makeEnv_values_ctx_b done remaining | makeEnv_values |

## APPROACH

### First use `lean_goal` at L13355 to see the exact proof state. Line numbers may have shifted slightly — verify with `lean_diagnostic_messages` first.

### First-position cases (newObj_func at L13358):
Follow the setProp_obj pattern. Template:
```lean
    | newObj_func h_f =>
      rename_i f envExpr args
      simp only [ANF.normalizeExpr] at hnorm
      have hf_depth : f.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      obtain ⟨sf_f, evs_f, hsteps_f, hsil_f, henv_f, hheap_f, hfuncs_f, hcs_f,
        htrace_f, hpres_f, ⟨n_f, m_f, hnorm_f⟩, hewf_f⟩ :=
        ih f hf_depth h_f env heap trace funcs cs _ n m cond then_ else_ v
          hnorm (fun x hfx => hewf x (VarFreeIn.newObj_func _ _ _ _ hfx)) heval hbool
      obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
        Steps_newObj_func_ctx_b envExpr args hsteps_f
          (fun ev hev msg => by rw [hsil_f ev hev]; exact Core.TraceEvent.noConfusion)
          hpres_f
      refine ⟨ws, evs_f, hwsteps, hsil_f, hwenv.trans henv_f, hwheap.trans hheap_f,
        hwfuncs, hwcs, by rw [hwtrace, htrace_f], ?_, ?_, ?_⟩
      · exact Steps_ctx_lift_pres (fun e => .newObj e envExpr args)
          (fun s inner hv t si hs he => step?_newObj_func_ctx s inner envExpr args hv t si hs he)
          hsteps_f (fun ev hev msg => by rw [hsil_f ev hev]; exact Core.TraceEvent.noConfusion) hpres_f
      · exact ⟨n_f, m_f, by rw [hwexpr]; simp only [ANF.normalizeExpr]; exact hnorm_f⟩
      · rw [hwexpr, hwenv, henv_f]; exact fun x hfx => by
          cases hfx with
          | newObj_func _ _ _ _ h => exact henv_f ▸ hewf_f x h
          | newObj_env _ _ _ _ h => exact hewf x (VarFreeIn.newObj_env _ _ _ _ h)
          | newObj_arg _ _ _ _ _ hmem h => exact hewf x (VarFreeIn.newObj_arg _ _ _ _ _ hmem h)
```

### Second-position cases (binary_rhs, call_env, newObj_env, setProp_val, getIndex_idx, setIndex_idx, setIndex_val):
Use `lean_goal` at each sorry. The HasIfInHead means the INNER expression has the if. Check with LSP what values are available.

### List-based cases (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems):
Leave as sorry if too complex — jsspec is building list helpers.

### PRIORITY ORDER:
1. newObj_func (first-position, straightforward)
2. binary_rhs, call_env, newObj_env (second-position with single value)
3. setProp_val, getIndex_idx, setIndex_idx, setIndex_val (second/third-position)
4. List cases — attempt if time permits

### DO BOTH THEOREMS: Each case solved in if_branch_step (L13355-13367) should be mirrored in if_branch_step_false (L14263-14275).

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
