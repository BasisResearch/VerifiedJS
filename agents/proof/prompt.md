# proof — CC VALUE + CALL SUB-CASES. Target: -2 this run.

## STATUS: 22 CC sorries (grep -c). Unchanged from last session. Push harder.

## YOUR TARGETS — VERIFIED LINE NUMBERS (as of 00:05 Mar 30)

### P0: getIndex value (L3630) — HIGHEST PRIORITY
- `| some cv => sorry -- value sub-case (heap reasoning needed, skip for now)`
- Same pattern as setProp/deleteProp you already proved.
- `simp [Flat.step?]`, case split on value type (object addr vs primitive)
- For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`

### P1: setIndex value (L3699)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Same structure as getIndex/setProp

### P2: call value (L3171)
- `| some cv => sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`
- When args has non-value: step first non-value arg (firstNonValueExpr + ih_depth)
- When all args values: function call execution

### P3: newObj (L3172)
- `| newObj f args => sorry`
- Object allocation with fresh heap address

### P4: objectLit all-values (L4021)
- `sorry -- all props are values: heap allocation`

### P5: arrayLit all-values (L4119)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2142, L2252: need convertExpr_not_lit for stub constructors (jsspec staging)
- L2336: HeapInj refactor staging
- L2655, L2677(×2): CCState threading (if-branch dead code)
- L4065, L4163: ExprAddrWF propagation (needs ExprAddrPropListWF/ExprAddrListWF — jsspec staging)
- L4112, L4414: CCState threading
- L4293: functionDef (large)
- L4383: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## CRITICAL TACTIC HINT for value sub-cases (P0-P1):
Same pattern as setProp/deleteProp you proved:
1. `simp [Flat.step?]` to unfold the Flat step
2. Case split on value type (object addr vs primitive)
3. For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`
4. For primitives: both sides return the same result

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
