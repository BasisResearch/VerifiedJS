# wasmspec — GOOD JOB ON return-none. KEEP CLOSING SORRIES.

## STATUS: 25 Wasm sorries (was 27). You closed return-none — excellent work. KEEP PUSHING.

File: `VerifiedJS/Wasm/Semantics.lean`

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## SORRY INVENTORY (25 grep lines, ~22 actual sorries):

### step_sim constructor cases (12 sorries, L6542-6620):
- L6542: let
- L6550: seq
- L6554: if
- L6557: while_
- L6560: throw
- L6563: tryCatch
- L6605: return (some t)
- L6608: yield
- L6611: await
- L6614: labeled
- L6617: break
- L6620: continue

### Deeper cases (8 sorries):
- L10145: binOp i32 type mismatch trap
- L10255: binOp f64 type mismatch trap
- L10261: unOp (entire case)
- L10516: call (sorry'd, commented-out proof below)
- L10569: call stack underflow
- L10573: call successful (blocked: multi-frame)
- L10576: callIndirect
- L11336: memoryGrow

### Top-level (1 sorry):
- L308: (check what this is)

## P0: return (some t) at L6605 — EASIEST WIN

You already proved return-none (L6568-6604). `return (some t)` is similar:
- ANF step: evaluates trivial t, produces silent event
- IR code: from LowerCodeCorr, should be value code + return_
- Copy the return-none pattern but handle the value

Use `lean_goal` at L6605 to see exact goal. Use `lean_multi_attempt` with candidates.

## P1: binOp trap cases (L10145, L10255) — 2 sorries

These are type-mismatch trap cases. Both IR and Wasm trap with same trace. Pattern:
```lean
simp [irStep?, hcode_ir, irPop2?, irTrapState, irPushTrace] at hstep
obtain ⟨rfl, rfl⟩ := hstep
-- Show Wasm also traps
refine ⟨_, ?_, { ... }⟩
```
Use `lean_goal` at each, then `lean_multi_attempt`.

## P2: unOp (L10261) — 1 sorry

The commented-out proof below (L10262-10512) shows the intended approach. It was sorry'd because of API changes. Try uncommenting and fixing.

## P3: call stack underflow (L10569) — needs emit_preserves_params

The comment says "Wasm param count might differ from IR param count, but for valid emit, param counts correspond." Write or find that lemma.

## SKIP: call successful (L10573) — blocked by multi-frame invariant. Leave as sorry.
## SKIP: step_sim constructor cases (L6542-6620) — these are structural, need ANF proof first.

## WORKFLOW
1. `lean_goal` at sorry → understand exact goal
2. `lean_multi_attempt` with 4-5 candidates
3. If found: edit sorry → build → verify
4. If timeout: add maxHeartbeats, try simpler tactic decomposition
5. Move to next

## TARGET: Close return-some (-1) + 2 binOp traps (-2) + unOp (-1) = net -4 this run

## Log progress to agents/wasmspec/log.md
