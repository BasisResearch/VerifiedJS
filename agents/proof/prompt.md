# proof — CC VALUE + CALL SUB-CASES. Target: -3 this run.

## STATUS: 22 CC sorries (grep-c). DOWN from 24. You closed deleteProp + setProp. EXCELLENT. KEEP GOING.

## YOUR TARGETS — value sub-cases (same pattern as deleteProp/setProp you just proved)

### P0: getIndex value (L3620)
- `| some cv => sorry -- value sub-case (heap reasoning needed, skip for now)`
- Case: `getIndex obj idx` where `Core.exprValue? obj = some cv`
- Same pattern as setProp/deleteProp you already proved.
- For objects: case split on `sc.heap.objects[addr]?`, use `hheapinj`
- For primitives: both sides return same result

### P1: setIndex value (L3689)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Case: `setIndex obj idx value` where `Core.exprValue? obj = some cv`
- Most complex: may need sub-case on idx and value too
- But obj-is-value case has same structure as setProp

### P2: call value (L3162) — after P0-P1
- `| some cv => sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`
- When args has non-value: step first non-value arg (use firstNonValueExpr + ih_depth)
- When all args values: function call execution

### P3: newObj (L3163) — after P2
- `| newObj f args => sorry`
- Object allocation with fresh heap address

### P4: objectLit all-values (L4011) — after P3
- `sorry -- all props are values: heap allocation`

### P5: arrayLit all-values (L4109)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2133, L2243: need convertExpr_not_lit for stub constructors
- L2327: HeapInj refactor staging
- L2646, L2668(×2): CCState threading (structural — if-branch dead code)
- L4055, L4153: ExprAddrWF propagation
- L4102, L4404: CCState threading
- L4283: functionDef (large)
- L4373: tryCatch (large)

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
