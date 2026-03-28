# wasmspec — CLOSE MECHANICAL WASM SORRIES

## STATUS: 27 non-comment sorry tokens in VerifiedJS/Wasm/Semantics.lean. Down from 36. Good progress.

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## P0: binOp trap cases (12 sorries at L6475-6553)

These are all in `step_sim` for binary operations where the stack has wrong types or is empty. Pattern:
- L6475, 6483, 6487, 6490, 6493, 6496: first batch
- L6538, 6541, 6544, 6547, 6550, 6553: second batch

For EACH sorry, use `lean_goal` to see the exact state, then `lean_multi_attempt` with:
```
["simp_all [step?, pop2?, trapState, pushTrace, withI32Bin, withI32Rel, traceToWasm]",
 "cases v1 <;> cases v2 <;> simp_all [step?, trapState, pushTrace, traceToWasm]",
 "simp only [step?, pop2?, trapState, pushTrace]; split <;> simp_all",
 "unfold step? withI32Bin pop2?; simp [trapState, pushTrace, traceToWasm]",
 "exact ⟨_, by simp [step?, pop2?, trapState, pushTrace], by constructor <;> simp_all⟩"]
```

If heartbeat timeout: add `set_option maxHeartbeats 400000` before the declaration.

## P1: control flow (4 sorries)
- L10390: callIndirect
- L10650: br
- L10733: brIf
- L11067: memoryGrow

Use `lean_goal` at each, then `lean_multi_attempt`.

## P2: inner step_sim cases (11 sorries at L9953-10387)

These are deeper in the proof. Work on them after P0 and P1.

## WORKFLOW
1. `lean_goal` at sorry line
2. `lean_multi_attempt` with 3-5 tactic candidates
3. If one works, edit the sorry to that tactic
4. Verify with `lean_diagnostic_messages`
5. Move to next sorry

## RULES
1. Build after EVERY change — `lake build VerifiedJS.Wasm.Semantics`
2. If something breaks, REVERT immediately
3. Do NOT touch other files
4. Prefer closing easy cases first (accumulate wins)

## Log progress to agents/wasmspec/log.md
