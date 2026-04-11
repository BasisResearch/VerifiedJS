# proof — CLOSE call_env AND newObj_env

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T19:05
- ANF: 37 real sorries. CC: 12. Total: **49**.
- **YOU CLOSED 6 SORRIES since 18:05!** setProp_val, getIndex_idx, setIndex_idx, setIndex_val all done!
- 2 more second-position cases remain: call_env (L18644) and newObj_env (L18646).
- After those: 5 list cases remain (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems).

## YOUR TARGET: L18644 (call_env) and L18646 (newObj_env)

### VERIFIED LINE NUMBERS (from file at 19:05):
```
L18644: | call_env h_a => sorry -- second-position: return in env of call f env args
L18646: | newObj_env h_a => sorry -- second-position: return in env of newObj f env args
```

### TEMPLATE: Use call_func proof at L16450-L16521 as base

The call_env case is structurally IDENTICAL to call_func, but:
1. **Wrapper**: `(.call (.lit fv) · args_list)` instead of `(.call · envExpr args_list)`
2. **ctx lemma**: `step?_call_env_ctx s fv inner args hv t si hs he` (L1962)
3. **error lemma**: `step?_call_env_error s fv inner args hv msg si hs` (L2588)
4. **VarFreeIn**: `VarFreeIn.call_env` instead of `VarFreeIn.call_func`
5. **HasNoAwait**: `by cases hna with | call _ ha _ => exact ha` (second field)
6. **Depth**: `a.depth ≤ d` from `Flat.Expr.depth` — same omega proof

**CRITICAL DIFFERENCE from call_func**: call_env is a SECOND-POSITION case, so `fv` (func) is already a value. The preceding steps `hwsteps_b` need to be included in the trace. Look at the setIndex_val proof right above (L18590-L18643) for how to handle the preceding value steps:
- The trace is `evs_b ++ evs_a`
- Steps are `Flat.Steps.append hwsteps_b hsteps'`
- observableTrace uses `observableTrace_all_silent hsil_b` pattern

### For newObj_env (L18646):
Same pattern, but use:
- Wrapper: `(.newObj (.lit fv) · args_list)`
- ctx: `step?_newObj_env_ctx s fv inner args hv t si hs he` (L1999)
- error: `step?_newObj_env_error s fv inner args hv msg si hs` (L2602)
- VarFreeIn: `VarFreeIn.newObj_env`
- HasNoAwait: `by cases hna with | newObj _ ha _ => exact ha`

### APPROACH:
1. Read L18590-L18643 (setIndex_val proof — your most recent template for second-position)
2. Read L16450-L16521 (call_func — shows the IH structure for call cases)
3. Write call_env at L18644, combining both patterns. Verify with LSP.
4. Write newObj_env at L18646 (same pattern). Verify with LSP.
5. Target: -2 sorries.

## AFTER P0: List cases (L18645, L18647-18650) — 5 sorries
These are harder (list decomposition needed). Defer until call_env + newObj_env done.

## DO NOT WORK ON:
- L10843-L11214 (trivialChain — LSP timeout zone)
- L19325-L19337 (while — blocked)
- L20062-L20102 (if_branch — blocked)
- L20943-L20964 (tryCatch — blocked)
- L22521-L22592 (noCallFrameReturn/body_sim — blocked)
- ClosureConvertCorrect.lean

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — call_env + newObj_env L18644+L18646" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
