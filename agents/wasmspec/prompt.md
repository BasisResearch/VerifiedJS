# wasmspec — CLOSE BINOP TRAP + UNOP SORRIES

## STATUS: 21 Wasm sorries in Semantics.lean. You closed br/brIf and stack underflow traps — good work.

File: `VerifiedJS/Wasm/Semantics.lean`

## BUILD STATUS: BROKEN (EmitCorrect.lean type mismatch — proof agent fixing). DO NOT touch Proofs/*.lean.

## SORRY INVENTORY (~21 actual sorries):

### Top-level (1):
- L308: Check what this is with `lean_goal`

### step_sim constructor cases (12, L6542-6620):
- L6542: let, L6550: seq, L6554: if, L6557: while_, L6560: throw, L6563: tryCatch
- L6605: return some, L6608: yield, L6611: await, L6614: labeled, L6617: break, L6620: continue
- SKIP these — structural, blocked by ANF proof

### binOp type mismatch traps (2):
- L10149: i32 type mismatch trap
- L10263: f64 type mismatch trap

### Other (6):
- L10269: unOp
- L10524: call sorry
- L10577, L10581: call stack frames
- L10584: callIndirect
- L11344: memoryGrow

## P0: binOp type mismatch traps (L10149, L10263) — 2 EASY WINS

You already proved the stack underflow trap cases. The type mismatch cases are similar:
- `pop2?` returns `some (a, b)` but types don't match (e.g., not both i32)
- Both IR and Wasm trap with the same trace
- Use `lean_goal` at each line, then `lean_multi_attempt`

Pattern:
```lean
-- IR traps because types don't match
-- Wasm also traps: show step? produces trap state
-- Build EmitSimRel with trap state
```

## P1: unOp (L10269) — 1 sorry

Check if there's a commented-out proof below. The wasmspec log mentions "L10262-10512 commented-out proof". Try uncommenting and fixing API changes.

## P2: call (L10524) — if straightforward

Use `lean_goal` to see what's needed. If it requires multi-frame reasoning, skip.

## SKIP: step_sim constructor cases (L6542-6620), callIndirect, memoryGrow — too complex for now

## WORKFLOW
1. `lean_goal` at sorry line
2. `lean_multi_attempt` with tactic candidates
3. Edit sorry → build: `lake build VerifiedJS.Wasm.Semantics`
4. Move to next

## TARGET: Close 2 binOp traps (-2) + unOp (-1) = net -3 this run

## Log progress to agents/wasmspec/log.md
