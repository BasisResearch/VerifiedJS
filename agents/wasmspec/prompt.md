# wasmspec — CLOSE writeLE? LEMMA + binOp CASES

## STATUS: 20 actual Wasm sorries in Semantics.lean. Target: -3 this run.

File: `VerifiedJS/Wasm/Semantics.lean`

## P0: L308 — writeLE?_preserves_size (EASY WIN, PURE LEMMA)

Goal is:
```
mem mem' : ByteArray
addr width : Nat
value : UInt64
h : writeLE? mem addr width value = some mem'
⊢ mem'.size = mem.size
```

writeLE? is defined at L269:
```lean
private def writeLE? (mem : ByteArray) (addr width : Nat) (value : UInt64) : Option ByteArray := Id.run do
  let mut out := mem
  for k in [0:width] do
    let idx := addr + k
    if idx < out.size then
      let byte := UInt8.ofNat ((value.toNat / Nat.pow 2 (8 * k)) % 256)
      out := out.set! idx byte
    else
      return none
  return some out
```

Key insight: `ByteArray.set!` preserves size (it uses `Array.set!` which preserves size when index is in bounds). The loop maintains the invariant `out.size = mem.size`.

Approach: Prove by induction on `width`. The for loop `[0:width]` iterates width times.

Try:
```lean
  induction width generalizing mem with
  | zero => simp [writeLE?, Id.run, forIn, ForIn.forIn] at h; exact h ▸ rfl
  | succ n ih =>
    unfold writeLE? at h
    simp [Id.run] at h
    -- unfold the for loop one step, use set! preserves size, apply ih
    sorry
```

Or try unfolding the `Id.run do` loop as `List.forIn` and proving the invariant. You may need:
```lean
theorem ByteArray.size_set! (a : ByteArray) (i : Nat) (v : UInt8) : (a.set! i v).size = a.size
```

Check if this lemma exists with `lean_local_search` for "ByteArray" "size" "set". If not, prove it inline.

**NOTE**: LSP may time out on this file (11K+ lines). If `lean_goal` times out:
1. Try `lean_multi_attempt` with shorter snippets
2. Or just write the proof and build: `lake build VerifiedJS.Wasm.Semantics`
3. Use `lean_diagnostic_messages` to check errors

## P1: binOp cases (L10284, L10290)

These are deep in the file so LSP may time out. Use this strategy:
1. Read the surrounding code (50 lines around each sorry) to understand the goal
2. Write the proof based on the pattern of nearby proved cases
3. Build to check

The binOp cases typically follow the pattern:
- IR evaluates binOp on two values
- If types mismatch → IR traps → show Wasm also traps
- If types match → produce result → show Wasm produces same result
- Build EmitSimRel with updated stack

## P2: L10545

Same approach — read context, write proof, build.

## SKIP: L6542-6620 (structural), L10598/L10602 (call), L10605 (callIndirect), L11365 (memoryGrow)

## WORKFLOW
1. Prove writeLE?_preserves_size at L308 → build
2. Read context around L10284, L10290 → write proofs → build
3. Read context around L10545 → write proof → build
4. Log to agents/wasmspec/log.md

## BUILD COMMAND: `lake build VerifiedJS.Wasm.Semantics`
