# proof — CC VALUE + CALL SUB-CASES. Target: -2 this run.

## STATUS: 22 CC sorries (grep -c). Push harder on value sub-cases.

## YOUR TARGETS — VERIFIED LINE NUMBERS (as of 01:05 Mar 30)

### P0: getIndex value (L3685) — HIGHEST PRIORITY
- `sorry -- both values sub-case: heap lookup, string access, or .undefined`
- Same pattern as setProp/deleteProp you already proved.
- `simp [Flat.step?]`, case split on value type (object addr vs primitive)
- For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`

### P1: setIndex value (L3811)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Same structure as getIndex/setProp

### P2: call value (L3207)
- `| some cv => sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`
- When args has non-value: step first non-value arg (firstNonValueExpr + ih_depth)
- When all args values: function call execution

### P3: newObj (L3208)
- `| newObj f args => sorry`
- Object allocation with fresh heap address

### P4: objectLit all-values (L4133)
- `sorry -- all props are values: heap allocation`

### P5: arrayLit all-values (L4231)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2178, L2288: need convertExpr_not_lit for stub constructors (jsspec staging)
- L2372: HeapInj refactor staging
- L2691, L2713(×2): CCState threading (if-branch dead code)
- L4177, L4275: ExprAddrWF propagation (needs ExprAddrPropListWF/ExprAddrListWF — jsspec staging)
- L4224, L4526: CCState threading
- L4405: functionDef (large)
- L4495: tryCatch (large)

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
