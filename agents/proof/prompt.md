# proof — CC VALUE + CALL SUB-CASES. Target: -3 this run.

## STATUS: 23 CC sorries (grep -c). ~21 actual unique locations. You closed 2 last session (setProp, deleteProp). KEEP GOING.

## YOUR TARGETS — VERIFIED LINE NUMBERS (as of 20:05 Mar 29)

### P0: setProp value (L3363)
- `| some cv => sorry -- setProp value sub-case (WIP: heap equality for flatToCoreValue inside closures)`
- You were close on this last session. Same pattern as deleteProp you already proved.
- `simp [Flat.step?]`, case split on value type, use `hheapinj` for objects

### P1: getIndex value (L3433)
- `| some cv => sorry -- value sub-case (heap reasoning needed, skip for now)`
- Same pattern as deleteProp/setProp.
- `simp [Flat.step?]`, case split on value type (object addr vs primitive)
- For objects: case split on `sc.heap.objects[addr]?`, use `hheapinj`

### P2: setIndex value (L3502)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Same structure as setProp/getIndex

### P3: call value (L3162)
- `| some cv => sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`
- When args has non-value: step first non-value arg (firstNonValueExpr + ih_depth)
- When all args values: function call execution

### P4: newObj (L3163)
- `| newObj f args => sorry`
- Object allocation with fresh heap address

### P5: objectLit all-values (L3824)
- `sorry -- all props are values: heap allocation`

### P6: arrayLit all-values (L3922)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2133, L2243: need convertExpr_not_lit for stub constructors (jsspec staging)
- L2327: HeapInj refactor staging
- L2646, L2668(×2): CCState threading (if-branch dead code)
- L3868, L3966: ExprAddrWF propagation (needs ExprAddrPropListWF/ExprAddrListWF — jsspec staging)
- L3915, L4217: CCState threading
- L4096: functionDef (large)
- L4186: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## CRITICAL TACTIC HINT for value sub-cases (P0-P2):
Same pattern as deleteProp you proved:
1. `simp [Flat.step?]` to unfold the Flat step
2. Case split on value type (object addr vs primitive)
3. For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`
4. For primitives: both sides return the same result

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
