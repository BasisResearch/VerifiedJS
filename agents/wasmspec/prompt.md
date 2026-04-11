# wasmspec — CLOSE compound return cases (L14353) + assess L13215

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL. Do 5 cases at a time, verify, continue.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T12:00
- Total: 48 sorries (ANF 33, CC 15).
- **HasReturnInHead_step_nonError (L13623)**: WRITTEN, ~600 lines. Depends on step_error_isLit.
- **HasReturnInHead_Steps_steppable (L14161)**: PROVED (modulo step_error_isLit).
- **hasReturnInHead_return_steps (L14207)**: Sorry at L14353 (compound catch-all).
- **proof agent is working on step_error_isLit (L14157)**. DO NOT touch it.

## P0: L14353 — compound HasReturnInHead catch-all in hasReturnInHead_return_steps

```
14353:    | _ => sorry -- remaining compound HasReturnInHead cases: same pattern as seq_left
```

This is the catch-all for compound HasReturnInHead constructors in `hasReturnInHead_return_steps`. The seq_left case is proved (L14291-14352). Use EXACTLY the same pattern.

### Strategy
1. `lean_goal` at L14353 to see which constructors hit this catch-all
2. Replace `| _ => sorry` with individual constructor matches:
   - `| .let_init h =>` — same as seq_left but with `step?_let_ctx` / `step?_let_error`
   - `| .assign_val h =>` — same pattern with `step?_assign_ctx` / `step?_assign_error`
   - `| .getProp_obj h =>` — same pattern
   - etc. for all compound constructors

3. For each: follow the seq_left proof pattern at L14291-14352:
   - Get IH on sub-expression (depth decreases)
   - Use `Steps_compound_error_lift` (L13135) to lift Steps through the compound wrapper
   - Need step?_XXX_ctx and step?_XXX_error lemmas

4. **CHECK**: Do step?_XXX_ctx and step?_XXX_error lemmas exist for each constructor? Search with:
   ```
   lean_local_search "step?_let_ctx" or lean_local_search "step?_assign_ctx"
   ```
   If they don't exist, write them first (they follow the same pattern as step?_seq_ctx).

5. Even if some cases need sorry, splitting the catch-all into individual cases is progress.

### Key lemmas available
- `Steps_compound_error_lift` at L13135
- `HasReturnInHead_step_nonError` at L13623
- `HasReturnInHead_Steps_steppable` at L14161
- `hasReturnInHead_callStackSafe` — callStack safety from HasReturnInHead
- `step?_seq_ctx` and `step?_seq_error` — existing context/error lemmas for seq

### Pattern from seq_left (L14291-14352)
Read the seq_left case carefully. The key structure is:
1. Get IH: `hasReturnInHead_return_steps` on sub-expression with reduced depth
2. Extract `hsteps_a`, `herr`, `hpres` from IH
3. Build `hpres` callback using `Steps_preserves_callStack` + `HasReturnInHead_Steps_steppable` + `hasReturnInHead_callStackSafe`
4. Apply `Steps_compound_error_lift` with appropriate ctx/error lemmas
5. Combine all witnesses

## P1: L13215 — anfConvert_step_sim compound catch-all

After P0, assess if this sorry can use the same infrastructure. Read 30 lines around it.

## P2: L14709 (HasAwaitInHead) and L14882 (HasYieldInHead)

Check if `HasAwaitInHead` / `HasYieldInHead` types exist. If so, follow the same error propagation pattern.

## P3: L14938, L14942, L14943 — return/yield .let + compound catch-all

Structural induction on sub-expression.

## DO NOT WORK ON:
- L14152-L14157 (step_error_isLit — proof agent is on this)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound HasReturnInHead return cases" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
