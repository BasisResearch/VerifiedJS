# wasmspec — CLOSE binOp TRAP SORRIES (12 targets)

## STATUS: 27 sorries in VerifiedJS/Wasm/Semantics.lean. You closed br + brIf last run. KEEP PUSHING.

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## P0: binOp trap cases — 12 sorries (L6475-6553)

These are your MAIN TARGET. You've been blocked by heartbeat timeouts. Solutions:

1. **Add `set_option maxHeartbeats 800000` before the theorem** (if not already present)
2. **Use `refine` instead of `simp_all`** — simp_all is the timeout culprit
3. **Work in smaller chunks** — close 2-3 sorries per edit, build, verify, repeat

Specific tactic to try at EACH sorry (use `lean_multi_attempt` first):
```
["refine ⟨_, by simp only [step?, pop2?, trapState, pushTrace, withI32Bin, withI32Rel, withF64Bin]; rfl, ?_⟩; constructor <;> simp_all [traceToWasm]",
 "exact ⟨_, rfl, by constructor <;> simp_all [traceToWasm]⟩",
 "simp only [step?, pop2?, trapState, pushTrace, withI32Bin, withI32Rel, withF64Bin, traceToWasm]; exact ⟨_, rfl, by constructor <;> assumption⟩",
 "unfold step? withI32Bin pop2?; simp only [trapState, pushTrace]; refine ⟨_, rfl, ?_⟩; constructor <;> simp_all"]
```

If ALL of those fail: use `lean_goal` to see the EXACT goal, then construct the proof term manually with `exact ⟨state, proof_step, proof_record⟩`.

## P1: Store/load inner cases — 13 sorries (L9950-10387)

These are deeper in `step_sim`. Same pattern as binOp but with different Wasm instructions. Work on after P0.

Priority order within P1:
1. L9950-9956: stack underflow cases (simplest)
2. L10011-10012, L10068-10069: type mismatch cases
3. L10026-10029: remaining store cases
4. L10075, L10330, L10383-10387: other

## P2: callIndirect (L10390) and memoryGrow (L11150) — 2 sorries

These are standalone. Try after P0 and P1.

## WORKFLOW
1. `lean_goal` at sorry → understand exact goal
2. `lean_multi_attempt` with 4-5 candidates
3. If found: edit sorry → build → verify
4. If timeout: add maxHeartbeats, try simpler tactic decomposition
5. Move to next

## TARGET: Close at least 4 binOp trap sorries this run (-4 minimum)

## Log progress to agents/wasmspec/log.md
