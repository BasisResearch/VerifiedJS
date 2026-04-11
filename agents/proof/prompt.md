# proof — CLOSE SECOND-POSITION HasReturnInHead CASES (L16148-L16159)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T15:00
- ANF: 46 real sorries. CC: 15 (jsspec). Total: 61.
- **step_error_isLit nearly proved** — only 1 sorry left (tryCatch L14759, wasmspec owns)
- **hasReturnInHead_return_steps**: seq_left, call_func, newObj_func, and ALL first-position constructors FULLY PROVED
- **12 second-position + list constructor sorries remain** at L16148-L16159 — THESE ARE YOUR TARGET
- The first-position cases prove the pattern works. Now replicate for second-position.

## DO NOT WORK ON:
- L14759 (step_error_isLit tryCatch — wasmspec)
- L10566-L10937 (trivialChain — LSP timeout zone)
- L16839-L16851 (while condition — blocked)
- L17576-L17616 (if_branch — blocked)
- L18457-L18478 (tryCatch — blocked)
- L19805-L19816 (noCallFrameReturn/body_sim — blocked)
- L16091, L16147 (Case B continuation — defer)
- L16515, L16688 (await/yield compound — defer)
- L16744-L16749 (return/yield .let compound — defer)

## P0: Second-position cases (L16148-L16152) — 5 sorries → 0

These follow THE EXACT SAME PATTERN as seq_left (L14988) and call_func (L16001). The only difference is:
1. Different wrapper function (e.g., `.binary op lhs_val ·` instead of `.seq · b`)
2. Different ctx/error lemma names
3. The first sub-expression is already a value, so ExprWellFormed and NoNestedAbrupt project differently

### ALL ctx/error lemmas exist:
- `step?_binary_rhs_ctx` (L1833) / `step?_binary_rhs_error`
- `step?_setProp_val_ctx` (L1924) / `step?_setProp_val_error`
- `step?_getIndex_idx_ctx` (L2018) / `step?_getIndex_idx_error`
- `step?_setIndex_idx_ctx` (L2037) / `step?_setIndex_idx_error`
- `step?_setIndex_val_ctx` (L1943) / `step?_setIndex_val_error`

### EXACT PROOF for binary_rhs (L16148):

```lean
    | binary_rhs h_a =>
      rename_i op lhs_val a
      simp only [ANF.normalizeExpr] at hnorm
      have ha_depth : a.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      obtain ⟨ih_none, ih_ok, ih_err⟩ :=
        ih a ha_depth h_a env heap trace funcs cs _ n m arg
          hnorm (fun x hfx => hewf x (VarFreeIn.binary_rhs _ _ _ _ hfx))
          (by cases hna with | binary _ ha => exact ha)
      refine ⟨?_, ?_, ?_⟩
      · intro harg
        obtain ⟨evs, sf_a, hsteps_a, hexpr_a, henv_a, hheap_a, htrace_a, hobs_a⟩ := ih_none harg
        have herr : ∃ msg, .error msg ∈ evs := observableTrace_return_has_error hobs_a
        have hpres : ∀ smid evs1, Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs1 smid →
            evs1.length ≤ evs.length →
            smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1 := by
          intro smid evs1 hsteps _hlen
          exact ⟨Flat.Steps_preserves_funcs hsteps,
            Flat.Steps_preserves_callStack hsteps (fun smid' t' smid'' evs_pre hsteps' hstep' _ => by
              refine ⟨fun body catch_ fin h => ?_, fun f' env' args' h => ?_⟩
              · exact (hasReturnInHead_callStackSafe smid'.expr (HasReturnInHead_Steps_steppable h_a hsteps' hstep')).1 body catch_ fin h
              · exact (hasReturnInHead_callStackSafe smid'.expr (HasReturnInHead_Steps_steppable h_a hsteps' hstep')).2 f' env' args' h),
            Flat.Steps_trace_append hsteps⟩
        obtain ⟨sf', hsteps', hexpr', henv', hheap', htrace'⟩ :=
          Steps_compound_error_lift (.binary op (.lit lhs_val) ·)
            (fun s inner hv t si hs he => step?_binary_rhs_ctx s op lhs_val inner hv t si hs he)
            (fun s inner hv msg si hs => step?_binary_rhs_error s op lhs_val inner hv msg si hs)
            hsteps_a herr hpres
        exact ⟨evs, sf', hsteps',
          hexpr'.trans hexpr_a, henv'.trans henv_a, hheap'.trans hheap_a,
          htrace'.trans htrace_a, hobs_a⟩
      · intro t v harg heval
        -- SAME BLOCK as none case but with ih_ok t v harg heval
        sorry -- fill in using exact same pattern
      · intro t msg harg heval
        -- SAME BLOCK as none case but with ih_err t msg harg heval
        sorry -- fill in using exact same pattern
```

### IMPORTANT: VarFreeIn and NoNestedAbrupt projections

For second-position, the VarFreeIn and NoNestedAbrupt extractors are DIFFERENT:
- `binary_rhs`: `VarFreeIn.binary_rhs` and `(by cases hna with | binary _ ha => exact ha)`
- `setProp_val`: `VarFreeIn.setProp_val` and `(by cases hna with | setProp _ ha => exact ha)`
- `getIndex_idx`: `VarFreeIn.getIndex_idx` and `(by cases hna with | getIndex _ ha => exact ha)`
- `setIndex_idx`: `VarFreeIn.setIndex_idx` and check NoNestedAbrupt.setIndex destructuring
- `setIndex_val`: `VarFreeIn.setIndex_val` and check NoNestedAbrupt.setIndex destructuring

Use `lean_hover_info` to check the exact constructor names if unsure.

### APPROACH: Do one case at a time
1. Write binary_rhs (L16148). Verify with lean_diagnostic_messages.
2. Write setProp_val (L16149). Verify.
3. Continue for getIndex_idx, setIndex_idx, setIndex_val.
4. Then do call_env (L16153) and newObj_env (L16155) — same pattern.

## P1: call_env, newObj_env (L16153, L16155) — 2 sorries → 0

Same pattern as call_func/newObj_func but for second-position:
- `step?_call_env_ctx` / `step?_call_env_error`
- `step?_newObj_env_ctx` / `step?_newObj_env_error`

## P2: List constructor cases (L16154, L16156-L16159) — 5 sorries

These need list-stepping infrastructure:
- `step?_call_arg_ctx` (L2168), `step?_newObj_arg_ctx` (L2197)
- `step?_makeEnv_values_ctx` (L2225), `step?_objectLit_val_ctx` (L2143)
- `step?_arrayLit_elem_ctx` (L2249)

These are harder — defer to P2 and assess after P0/P1.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — second-position HasReturnInHead cases" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
