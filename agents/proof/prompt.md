# proof — 46 ANF sorries. L9585 catch-all is YOUR #1 job.

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~100MB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13231-13243 and L14139-14151 zones (if_branch individual cases)
- **YOU** own everything else
- DO NOT touch those lines

## PROGRESS: You closed 8 sorries last run — great work! Now decompose L9585.

## ===== PRIORITY 0: DECOMPOSE L9585 CATCH-ALL =====

**THIS IS YOUR #1 JOB.** Line 9585 has:
```
    | _ => sorry -- remaining: seq_right, setProp_obj/val, binary_rhs, call_func/env/args, ...
```

**Replace with explicit cases.** Follow the EXACT pattern of `binary_lhs` at L9560-9584:

### First-position cases (follow binary_lhs pattern exactly):
| Constructor | Steps helper | step? helper | VarFreeIn |
|-------------|-------------|-------------|-----------|
| setProp_obj h_obj | Steps_setProp_obj_ctx_b prop val | step?_setProp_obj_ctx | setProp_obj, setProp_value |
| getIndex_obj h_obj | Steps_getIndex_obj_ctx_b idx | step?_getIndex_obj_ctx | getIndex_obj, getIndex_idx |
| setIndex_obj h_obj | Steps_setIndex_obj_ctx_b idx val | step?_setIndex_obj_ctx | setIndex_obj, setIndex_idx, setIndex_value |
| call_func h_f | Steps_call_func_ctx_b envExpr args | step?_call_func_ctx | call_func, call_env, call_arg |
| newObj_func h_f | Steps_newObj_func_ctx_b envExpr args | step?_newObj_func_ctx | newObj_func, newObj_env, newObj_arg |

### Second-position cases (harder — need value from first position):
| Constructor | Steps helper | Notes |
|-------------|-------------|-------|
| binary_rhs h_rhs | Steps_binary_rhs_ctx_b op lv | need lv: use `lean_goal` to find how lhs value is available |
| setProp_val h_val | Steps_setProp_val_ctx_b ov prop | need ov from obj position |
| getIndex_idx h_idx | Steps_getIndex_idx_ctx_b ov | need ov |
| setIndex_idx h_idx | Steps_setIndex_idx_ctx_b ov val | need ov |
| setIndex_val h_val | Steps_setIndex_val_ctx_b ov iv | need ov AND iv |
| call_env h_env | Steps_call_env_ctx_b fv args | need fv |
| newObj_env h_env | Steps_newObj_env_ctx_b fv args | need fv |

### List-based (KEEP AS SORRY):
| call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems |

### seq_right case:
`seq_right h_right` — similar to already-proved seq_left. Use Steps_seq_ctx_b.

### APPROACH:
1. Use `lean_goal` at L9585 to see the exact proof state
2. Replace `| _ => sorry` with explicit constructor cases
3. Do ALL first-position cases first (easy wins — follow binary_lhs template)
4. For second-position: use `lean_goal` to understand what values are available
5. Use `lean_multi_attempt` to test proofs
6. List cases: leave as individual `sorry`

### Template for first-position (e.g. setProp_obj):
```lean
    | setProp_obj h_obj =>
      rename_i obj prop val
      simp only [ANF.normalizeExpr] at hnorm
      have hobj_depth : obj.depth ≤ d := by simp [Flat.Expr.depth] at hd; omega
      obtain ⟨sf_obj, evs_obj, hsteps_obj, hsil_obj, henv_obj, hheap_obj, hfuncs_obj, hcs_obj,
        htrace_obj, hpres_obj, ⟨n_obj, m_obj, hnorm_obj⟩, hewf_obj⟩ :=
        ih obj hobj_depth label h_obj env heap trace funcs cs _ n m body
          hnorm (fun x hfx => hewf x (VarFreeIn.setProp_obj _ _ _ _ hfx))
      obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
        Steps_setProp_obj_ctx_b prop val hsteps_obj
          (fun ev hev msg => by rw [hsil_obj ev hev]; exact Core.TraceEvent.noConfusion)
          hpres_obj
      refine ⟨ws, evs_obj, hwsteps, hsil_obj, hwenv.trans henv_obj, hwheap.trans hheap_obj,
        hwfuncs, hwcs, by rw [hwtrace, htrace_obj], ?_, ?_, ?_⟩
      · exact Steps_ctx_lift_pres (fun e => .setProp e prop val)
          (fun s inner hv t si hs he => step?_setProp_obj_ctx s inner prop val hv t si hs he)
          hsteps_obj (fun ev hev msg => by rw [hsil_obj ev hev]; exact Core.TraceEvent.noConfusion) hpres_obj
      · exact ⟨n_obj, m_obj, by rw [hwexpr]; simp only [ANF.normalizeExpr]; exact hnorm_obj⟩
      · rw [hwexpr, hwenv, henv_obj]; exact fun x hfx => by
          cases hfx with
          | setProp_obj _ _ _ _ h => exact henv_obj ▸ hewf_obj x h
          | setProp_value _ _ _ _ h => exact hewf x (VarFreeIn.setProp_value _ _ _ _ h)
```

## PRIORITY 1: Groups B-E (after L9585)
Lower priority — only attempt if L9585 is done:
- L10832, L10989, L11166, L11324: compound HasXInHead
- L10983, L11160, L11318: compound inner_val/inner_arg
- L11380, L11384, L11385: return/yield/compound
- L11475, L11487: while condition

## DO NOT TOUCH (blocked or wasmspec-owned):
- L13231-13243, L14139-14151 (wasmspec)
- L14992, L15010, L15013 (tryCatch — blocked)
- L16096, L16107, L16327, L16380 (call frame/break/continue — blocked)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
