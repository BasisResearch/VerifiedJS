# proof — 22 ANF sorries. ALL helpers now exist. Decompose the catch-alls!

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~400MB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13060 and L13866 zones (if_branch catch-alls)
- **YOU** own everything else
- DO NOT touch those lines

## PROGRESS: 22 ANF sorries remain. You closed 8 last run — great work!

## ===== PRIORITY 0: DECOMPOSE L9504 CATCH-ALL =====

**THIS IS YOUR #1 JOB.** The L9504 catch-all covers ~15 constructor cases. ALL Steps_X_ctx_b helpers NOW EXIST (jsspec built them). You can prove every single one.

The catch-all is at L9504 in `normalizeExpr_labeled_branch_step`:
```
    | _ => sorry -- remaining: seq_right, setProp_obj/val, binary_rhs, call_func/env/args, ...
```

**Replace it with explicit cases.** Follow the EXACT pattern of `binary_lhs` at L9482-9503:

### Simple 2-position cases (follow binary_lhs pattern exactly):
Each needs: (1) rename_i, (2) simp [ANF.normalizeExpr] at hnorm, (3) depth bound, (4) IH, (5) Steps_X_ctx_b, (6) refine, (7) Steps_ctx_lift_pres, (8) normalizeExpr fact, (9) VarFreeIn well-formedness.

| Constructor | Steps helper | step? helper | VarFreeIn constructor(s) | normalizeExpr simp |
|-------------|-------------|-------------|--------------------------|-------------------|
| binary_rhs h_rhs | Steps_binary_rhs_ctx_b op lv | step?_binary_rhs_ctx | binary_rhs, binary_lhs | ANF.normalizeExpr (needs lv from HasLabeledInHead.binary_rhs — h_rhs proves rhs has labeled, so lhs must be a value) |
| setProp_obj h_obj | Steps_setProp_obj_ctx_b prop val | step?_setProp_obj_ctx | setProp_obj, setProp_value | ANF.normalizeExpr |
| setProp_val h_val | Steps_setProp_val_ctx_b ov prop | step?_setProp_val_ctx | setProp_value, setProp_obj | needs ov from val position |
| getIndex_obj h_obj | Steps_getIndex_obj_ctx_b idx | step?_getIndex_obj_ctx | getIndex_obj, getIndex_idx | ANF.normalizeExpr |
| getIndex_idx h_idx | Steps_getIndex_idx_ctx_b ov | step?_getIndex_idx_ctx | getIndex_idx, getIndex_obj | needs ov |
| setIndex_obj h_obj | Steps_setIndex_obj_ctx_b idx val | step?_setIndex_obj_ctx | setIndex_obj, setIndex_idx, setIndex_value | ANF.normalizeExpr |
| setIndex_idx h_idx | Steps_setIndex_idx_ctx_b ov val | step?_setIndex_idx_ctx | setIndex_idx, setIndex_obj, setIndex_value | needs ov |
| setIndex_val h_val | Steps_setIndex_val_ctx_b ov iv | step?_setIndex_val_ctx | setIndex_value, setIndex_obj, setIndex_idx | needs ov, iv |
| call_func h_f | Steps_call_func_ctx_b envExpr args | step?_call_func_ctx | call_func, call_env, call_arg | ANF.normalizeExpr |
| call_env h_env | Steps_call_env_ctx_b fv args | step?_call_env_ctx | call_env, call_func, call_arg | needs fv |
| newObj_func h_f | Steps_newObj_func_ctx_b envExpr args | step?_newObj_func_ctx | newObj_func, newObj_env, newObj_arg | ANF.normalizeExpr |
| newObj_env h_env | Steps_newObj_env_ctx_b fv args | step?_newObj_env_ctx | newObj_env, newObj_func, newObj_arg | needs fv |

### seq_right case:
`seq_right h_right` — similar to seq_left which is already proved. Use Steps_seq_ctx_b for the left side, then recurse for the right side via seq structure.

### List-based cases (harder — may need to sorry individually):
| call_args h_args | Steps_call_arg_ctx_b funcExpr envExpr done remaining | list decomposition |
| newObj_args h_args | Steps_newObj_arg_ctx_b funcExpr envExpr done remaining | list decomposition |
| makeEnv_values h_vals | Steps_makeEnv_values_ctx_b done remaining | list decomposition |
| objectLit_props h_props | (no Steps helper yet) | KEEP AS SORRY |
| arrayLit_elems h_elems | (no Steps helper yet) | KEEP AS SORRY |

### APPROACH:
1. Use `lean_goal` at L9504 to see the exact proof state
2. Replace `| _ => sorry` with explicit constructor cases
3. Start with the simple cases (binary_rhs, setProp_obj, call_func, etc.)
4. For binary_rhs and other "second position" cases: the HasLabeledInHead proof tells you the inner expression has the labeled. The outer expression's first sub-expression was already normalized to a value/trivial. You need to extract that value.
5. Use `lean_multi_attempt` to test your proofs
6. For list cases (call_args, newObj_args, makeEnv_values) and objectLit/arrayLit: use `sorry` for now

**KEY INSIGHT from binary_lhs proof (L9482-9503):**
```lean
    | binary_lhs h_lhs =>
      rename_i lhs op rhs
      simp only [ANF.normalizeExpr] at hnorm
      have hlhs_depth : lhs.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      obtain ⟨sf_lhs, evs_lhs, hsteps_lhs, hsil_lhs, henv_lhs, hheap_lhs, hfuncs_lhs, hcs_lhs,
        htrace_lhs, hpres_lhs, ⟨n_lhs, m_lhs, hnorm_lhs⟩, hewf_lhs⟩ :=
        ih lhs hlhs_depth label h_lhs env heap trace funcs cs _ n m body
          hnorm (fun x hfx => hewf x (VarFreeIn.binary_lhs _ _ _ _ hfx))
      obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
        Steps_binary_lhs_ctx_b op rhs hsteps_lhs
          (fun ev hev msg => by rw [hsil_lhs ev hev]; exact Core.TraceEvent.noConfusion)
          hpres_lhs
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
```

## PRIORITY 1: Groups B-E (after L9504)
These are lower priority — only attempt if L9504 is done:
- L10751 compound HasThrowInHead
- L10908 compound HasReturnInHead
- L11085 compound HasAwaitInHead
- L11243 compound HasYieldInHead
- L10902, L11079, L11237 compound inner_val/inner_arg
- L11299, L11303, L11304 return/yield/compound
- L11394, L11406 while condition

## DO NOT TOUCH (blocked):
L14707, L14725, L14728, L15811, L15822, L16042, L16095

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
