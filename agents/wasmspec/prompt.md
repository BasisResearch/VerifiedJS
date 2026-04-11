# wasmspec — CLOSE HasReturnInHead_step_nonError remaining sorry + compound return cases

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL. Do 5 cases at a time, verify, continue.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T11:06
- Total: 50 sorries (ANF 33, CC 17).
- **HasReturnInHead_step_nonError (L13623)**: WRITTEN, 27 cases done. 1 sorry remains inside at ~L14157 (in `HasReturnInHead_step_error_isLit`). proof agent is being directed to close L14157.
- **HasReturnInHead_Steps_steppable (L14161)**: PROVED. Depends on step_error_isLit.
- **hasReturnInHead_return_steps (L14207)**: Still has sorry at L14353.

## P0: L14353 — remaining compound HasReturnInHead cases in hasReturnInHead_return_steps

```
14353:    | _ => sorry -- remaining compound HasReturnInHead cases: same pattern as seq_left
```

This is the catch-all for compound HasReturnInHead constructors in `hasReturnInHead_return_steps`. The seq_left case is proved — use EXACTLY the same pattern for the remaining constructors.

### Strategy
1. `lean_goal` at L14353 to see which constructors are covered by this catch-all
2. Split the catch-all into individual constructor cases
3. For each: IH on sub-expression (depth decreases), then lift via `Steps_compound_error_lift` (L13135)
4. Even if some cases need sorry, splitting into individual cases is progress

### Key lemmas available
- `Steps_compound_error_lift` at L13135 — lifts Steps through compound wrappers
- `HasReturnInHead_step_nonError` at L13623 — preservation through non-error steps
- `HasReturnInHead_Steps_steppable` at L14161 — preservation through multi-step

## P1: L14709 (compound HasAwaitInHead) and L14882 (compound HasYieldInHead)

These are the await/yield analogues. They need the same error propagation pattern. If HasReturnInHead infrastructure is done, check if similar lemmas exist for HasAwaitInHead / HasYieldInHead, or if they can reuse the return infrastructure.

## P2: L14938, L14942, L14943 — return/yield .let + compound catch-all

```
14938:    | some val => sorry -- return (some val): compound, can produce .let
14942:    | some val => sorry -- yield (some val): compound, can produce .let
14943:  | _ => sorry -- compound expressions
```

These need structural induction on the sub-expression.

## P3: L13215 — compound cases in anfConvert_step_sim

```
13215:  | _ => sorry -- compound cases: need Steps lifting lemma + error propagation
```

This is the main step_sim catch-all. May be closable now that HasReturnInHead infrastructure exists.

## DO NOT WORK ON:
- L14152-L14157 (step_error_isLit — proof agent is doing this)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound HasReturnInHead return cases" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
