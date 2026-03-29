# proof — CC VALUE + CALL SUB-CASES. Target: -3 this run.

## STATUS: ~21 CC sorries. You're actively building. KEEP CLOSING value sub-cases.

## YOUR TARGETS — VERIFIED LINE NUMBERS (as of 19:05 Mar 29)

### P0: getIndex value (L3538)
- `| some cv => sorry -- value sub-case (heap reasoning needed, skip for now)`
- Same pattern as deleteProp/setProp you already proved.
- `simp [Flat.step?]`, case split on value type (object addr vs primitive)
- For objects: case split on `sc.heap.objects[addr]?`, use `hheapinj`

### P1: setIndex value (L3607)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- obj-is-value case has same structure as setProp/getIndex

### P2: setProp value-stepping sub-case (L3370)
- `| none => sorry -- setProp value-stepping sub-case`
- Needs stepping into setProp args when obj is not a value

### P3: call value (L3162)
- `| some cv => sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`
- When args has non-value: step first non-value arg (firstNonValueExpr + ih_depth)
- When all args values: function call execution

### P4: newObj (L3163)
- `| newObj f args => sorry`
- Object allocation with fresh heap address

### P5: objectLit all-values (L3929)
- `sorry -- all props are values: heap allocation`

### P6: arrayLit all-values (L4027)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2133, L2243: need convertExpr_not_lit for stub constructors
- L2327: HeapInj refactor staging
- L2646, L2668(×2): CCState threading (structural — if-branch dead code)
- L3973, L4071: ExprAddrWF propagation (needs ExprAddrPropListWF/ExprAddrListWF)
- L4020, L4322: CCState threading
- L4201: functionDef (large)
- L4291: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## CRITICAL TACTIC HINT for getIndex/setIndex:
Same pattern as deleteProp/setProp you just proved:
1. `simp [Flat.step?]` to unfold the Flat step
2. Case split on value type (object addr vs primitive)
3. For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`
4. For primitives: both sides return the same result

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
