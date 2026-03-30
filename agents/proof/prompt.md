# proof — CC VALUE + CALL SUB-CASES. Target: -1 this run.

## STATUS: 23 CC sorries (grep -c), ~21 actual. You've been running 4h+ with 0 closures. Time to close ONE.

## YOUR TARGETS — VERIFIED LINE NUMBERS (as of 03:05 Mar 30)

### P0: getIndex value (L3751, L3752) — HIGHEST PRIORITY
Two sub-cases on same sorry block:
- L3751: `sorry -- getIndex object both-values: heap lookup via HeapInj`
- L3752: `sorry -- getIndex string both-values: string indexing`

**For L3752 (string indexing)**: This should be EASIER than object case.
- Both Flat and Core do string character indexing → same result
- Try: `simp [Flat.step?, Core.step?]`, unfold string indexing on both sides
- If types match, `rfl` or `congr` should close it

**For L3751 (object case)**: Same pattern as getProp object you already proved.
- Case split on `sc.heap.objects[addr]?` → some/none
- Use `hheapinj` for heap correspondence
- Use `HeapInj_get` or similar from your infrastructure

### P1: setIndex value (L3924)
- `sorry -- value sub-case (heap reasoning needed)`
- Same class as getIndex/setProp

### P2: call value (L3266)
- `sorry -- callee is value: arg stepping or call execution`
- Case split on `exprListValue? args`

### P3: newObj (L3267)
- `| newObj f args => sorry`

### P4: objectLit all-values (L4246)
- `sorry -- all props are values: heap allocation`

### P5: arrayLit all-values (L4344)
- `sorry -- all elements are values: heap allocation`

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs)
- L2237, L2347: need convertExpr_not_lit for stub constructors (jsspec staging)
- L2431: HeapInj refactor staging
- L2750, L2772(×2): CCState threading (if-branch dead code)
- L4290, L4388: ExprAddrWF propagation (needs ExprAddrPropListWF/ExprAddrListWF)
- L4337, L4639: CCState threading (concatenated lists, while)
- L4518: functionDef (large)
- L4608: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## STRATEGY SHIFT: Pick the EASIEST sorry first
You've been stuck for 4h. Stop trying the hardest case first.
- L3752 (getIndex string) is probably easiest — string indexing should be pure computation
- If stuck after 20min on any case, move to the next one
- Close ONE sorry this run, even if it's the simplest one

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
