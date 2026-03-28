# wasmspec — CLOSE WASM SORRIES: TARGET -3 THIS RUN

## STATUS: 20 actual Wasm sorries in Semantics.lean. return-none proved earlier — good work.

File: `VerifiedJS/Wasm/Semantics.lean`

## SORRY INVENTORY (20 actual):

### Top-level (1):
- L308: Use `lean_goal` to check what this needs

### step_sim constructor cases (12, L6542-6620):
- L6542: let, L6550: seq, L6554: if, L6557: while_, L6560: throw, L6563: tryCatch
- L6605: return some, L6608: yield, L6611: await, L6614: labeled, L6617: break, L6620: continue
- **SKIP ALL 12** — these are structural, blocked by ANF proof progress

### binOp (2):
- L10290: type mismatch trap case
- L10296: another binOp case

### Other (5):
- L10551: unOp or similar
- L10604, L10608: call stack frame cases
- L10611: callIndirect
- L11371: memoryGrow

## P0: binOp cases (L10290, L10296) — EASIEST WINS

Use `lean_goal` at L10290 and L10296. These are type mismatch / trap cases similar to the ones you already proved.

Pattern from your prior successes:
1. Show IR traps because types don't match
2. Show Wasm also traps (step? produces trap state)
3. Build EmitSimRel with trap states matching

```lean
-- At the sorry, try:
lean_multi_attempt at L10290: ["simp_all", "exact ⟨_, rfl, by simp_all⟩", "refine ⟨_, ?_, ?_⟩ <;> simp_all"]
```

## P1: L10551 — check with lean_goal

If it's a straightforward case (unOp, comparison), close it. If it requires deep stack reasoning, skip.

## P2: L308 — check with lean_goal

This is the top-level sorry. May be easy or may be a placeholder for a large proof obligation.

## SKIP: L6542-6620 (structural step_sim), L10604/L10608 (call multi-frame), L10611 (callIndirect), L11371 (memoryGrow)

## TARGET: Close 3 sorries (-3): binOp (2) + one of L10551/L308

## WORKFLOW
1. `lean_goal` at sorry line → understand the goal
2. `lean_multi_attempt` with candidate tactics
3. Edit sorry → build: `lake build VerifiedJS.Wasm.Semantics`
4. Move to next sorry

## Log progress to agents/wasmspec/log.md
