# wasmspec — unOp DONE! Target: return-some + call underflow

## STATUS: unOp PROVED. 16 actual Wasm sorries. Target: ≤14 (-2).

File: `VerifiedJS/Wasm/Semantics.lean`

## UPDATED SORRY MAP (line numbers current as of 11:05):
### Structural block (6 sorries):
- L6738: let
- L6746: seq
- L6750: if
- L6753: while
- L6756: throw
- L6759: tryCatch

### Return/control (7 sorries):
- **L6801: return-some** ← P0
- L6804: yield
- L6807: await
- L6810: labeled
- L6813: break
- L6816: continue

### Emit block (4 sorries):
- **L10829: call (underflow/no-args case)** ← P1
- **L10833: call (successful case)** — BLOCKED by multi-frame
- L10835: callIndirect
- L11595: memoryGrow

## PRIORITY 0: return-some (L6801) — ADAPT FROM return-none (L6764-6800)

The return-none proof is RIGHT ABOVE at L6764-6800. The `some t` case is similar but needs:
1. Show `t : ANF.Trivial` maps to IR value via `hrel.hvar` or `hrel.henv`
2. Show IR emits const instruction for value, then return_
3. LowerCodeCorr: `return_some` constructor maps to `[const_val, return_]`

Pattern (adapt from return-none):
```lean
| some t =>
    -- Invert LowerCodeCorr for return (some t)
    have hc := hrel.hcode; rw [hexpr] at hc
    -- return_some case: code = constCode ++ [return_]
    -- where constCode pushes the trivial value onto stack
    have hcode_eq := hc  -- need to match return_some constructor
    -- ANF step: silent, expr → trivial (trivialOfValue (evalTrivial ...))
    -- IR: execute const instructions + return_
    sorry -- fill after reading LowerCodeCorr.return_some
```

Read `LowerCodeCorr` constructors (grep for `return_some` in the file) to understand the exact IR code layout. Then adapt the return-none proof pattern.

## PRIORITY 1: call underflow (L10829)

Read context around L10829. The underflow case means IR stack doesn't have enough args. You need to show Wasm ALSO underflows or handle the corresponding Wasm behavior. Check if `hrel.hstack` gives stack correspondence that makes this provable.

## SKIP
- L10833 (call success): blocked by multi-frame EmitSimRel
- Structural block (let/seq/if/while/throw/tryCatch): need 1:N framework
- L10835 (callIndirect), L11595 (memoryGrow): lower priority

## LSP TIMEOUT WORKAROUND
This file is 11K+ lines. lean_goal/lean_multi_attempt WILL timeout. Instead:
1. Read code context (50+ lines around sorry)
2. Read nearest proved case for pattern
3. Write proof directly using Edit
4. Build: `lake build VerifiedJS.Wasm.Semantics`
5. Use `lean_diagnostic_messages` with start_line/end_line to check errors

## GREAT WORK on unOp! Keep the momentum.
## Log to agents/wasmspec/log.md
