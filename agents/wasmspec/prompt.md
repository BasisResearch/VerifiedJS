# wasmspec — CLOSE compound return cases (L14353) + await/yield (L14709, L14882)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL. Do 5 cases at a time, verify, continue.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T11:30
- Total: 48 sorries (ANF 33, CC 15).
- **HasReturnInHead_step_nonError (L13623)**: WRITTEN, ~600 lines. Depends on step_error_isLit (proof agent working on it).
- **HasReturnInHead_Steps_steppable (L14161)**: PROVED (modulo step_error_isLit).
- **hasReturnInHead_return_steps (L14207)**: Sorry at L14353 (compound catch-all).

## P0: L14353 — compound HasReturnInHead catch-all in hasReturnInHead_return_steps

```
14353:    | _ => sorry -- remaining compound HasReturnInHead cases: same pattern as seq_left
```

This is the catch-all for compound HasReturnInHead constructors in `hasReturnInHead_return_steps`. The seq_left case is proved (L14291-14352). Use EXACTLY the same pattern.

### Strategy
1. `lean_goal` at L14353 to see which constructors hit this catch-all
2. Split into individual constructor cases (let_init, assign_val, getProp_obj, binary_lhs, etc.)
3. For each: follow the seq_left proof pattern at L14291-14352:
   - Get IH on sub-expression (depth decreases)
   - Use `Steps_compound_error_lift` (L13135) to lift Steps through the compound wrapper
   - Need step?_XXX_ctx and step?_XXX_error lemmas (analogous to step?_seq_ctx and step?_seq_error)
4. Even if some cases need sorry, splitting is progress

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

## P1: L14709 (HasAwaitInHead) and L14882 (HasYieldInHead)

These are await/yield analogues. Check if `HasAwaitInHead` / `HasYieldInHead` types exist. If so, follow the same error propagation pattern. If not, these may need different infrastructure.

## P2: L14938, L14942, L14943 — return/yield .let + compound catch-all

```
14938:    | some val => sorry -- return (some val): compound, can produce .let
14942:    | some val => sorry -- yield (some val): compound, can produce .let
14943:  | _ => sorry -- compound expressions
```

Structural induction on sub-expression.

## P3: L13215 — anfConvert_step_sim compound catch-all

May be closable now that HasReturnInHead infrastructure exists.

## DO NOT WORK ON:
- L14152-L14157 (step_error_isLit — proof agent is on this)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound HasReturnInHead return cases" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
