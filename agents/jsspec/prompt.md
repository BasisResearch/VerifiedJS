# jsspec — CC VALUE SUB-CASES: 5 sorries all with same pattern

## STATUS: 62 sorries. You're investigating L2920/L3020/L3090/L3159/L3244. KEEP GOING.

## PRIORITY 0: CC value sub-cases (L2907, L3031, L3101, L3170, L3255)

All 5 say `| some cv => sorry -- callee/arg is value`. The pattern in each:
- `Core.exprValue? subexpr = some cv` means `subexpr = .lit cv`
- The Flat side has `sf.expr = .call (.lit (convertValue cv)) ...` (or similar)
- `step?` on the Flat side evaluates the value part (it's already a lit, so moves to next sub-expr or executes)
- You need `HeapInj` to map Core heap operations to Flat heap operations

### Investigation steps:
1. `lean_goal` at EACH sorry (L2907, L3031, L3101, L3170, L3255) — understand what differs
2. `lean_local_search "HeapInj"` and `lean_local_search "convertValue"` — find available lemmas
3. Look at the STRING case of getProp (L2930-2975) as a template — it's a fully proved value case

### For L2907 specifically (callee is value in .call):
- When callee is a value, args may still need stepping
- OR all args are values and we execute the call
- Case split on `Core.exprListValue? args`

Write helper lemmas directly into ClosureConvertCorrect.lean (section before L2907). Build after each.

## PRIORITY 1: CC objectLit/arrayLit helpers (L3403, L3429, L3437, L3484, L3491, L3517, L3525)

Check `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean` for staging work. Inline what's valid.

## PRIORITY 2: CC getProp object sorry (L2929) — only if proof agent hasn't started this

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/` (read only — staging reference)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
## LOG: agents/jsspec/log.md — LOG IMMEDIATELY when you start and every 30 min
