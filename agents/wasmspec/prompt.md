# wasmspec — L308 DONE! Target: unOp + return-some + yield/await

## STATUS: L308 (writeLE?) PROVED. Wasm actual sorries: ~16. Target: ≤13 (-3).

File: `VerifiedJS/Wasm/Semantics.lean`

## SORRY MAP (Wasm/Semantics.lean):
### Structural block (6 sorries): L6690 let, L6698 seq, L6702 if, L6705 while, L6708 throw, L6711 tryCatch
### Return-some + remaining (7 sorries): L6753 return-some, L6756 yield, L6759 await, L6762 labeled, L6765 break, L6768 continue
### Emit block (4 sorries): L10477 unOp, L10730 call, L10790 callIndirect, L11551 memoryGrow
- Note: L10731-10789 is a COMMENT BLOCK (`/-...-/`). The sorries inside are NOT actual.

## PRIORITY 0: unOp (L10477) — EASIEST WIN

The commented-out proof attempt at L10478+ shows the ENTIRE approach. It just needs to be un-commented and fixed. Read L10478-10727 to see the full template.

Strategy:
1. Read the commented-out proof (L10478-10727)
2. Un-comment it, replacing the `sorry` at L10477
3. Fix any API mismatches (the comment says it was WIP)
4. Build: `lake build VerifiedJS.Wasm.Semantics`

## PRIORITY 1: return-some (L6753) — ADAPT FROM return-none

The return-none case (L6712+) is ALREADY PROVED above L6753. The `some t` case needs to:
- Show the trivial value `t` maps to an IR value
- Show the IR const instruction produces the right Wasm value
- Then return_ instruction fires

Read the return-none proof (L6712-6752) and adapt for the `some` case.

## PRIORITY 2: yield (L6756), await (L6759)

These follow similar patterns to throw/return. Read the nearby proved cases and adapt.

## SKIP: structural block (let/seq/if/while/throw/tryCatch — need 1:N framework), call (needs multi-frame), callIndirect, memoryGrow

## LSP TIMEOUT WORKAROUND
This file is 11K+ lines. lean_goal/lean_multi_attempt WILL timeout. Instead:
1. Read the code context (50+ lines around sorry)
2. Read the nearest proved case for pattern
3. Write the proof directly using Edit
4. Build: `lake build VerifiedJS.Wasm.Semantics`
5. Use `lean_diagnostic_messages` with start_line/end_line to check errors

## Log to agents/wasmspec/log.md
