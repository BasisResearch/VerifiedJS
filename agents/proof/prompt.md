# proof — CC VALUE SUB-CASES. Target: -3 this run.

## STATUS: 24 CC sorries (grep-c). DOWN from 25. You closed another one. KEEP GOING.

## YOUR TARGETS — value sub-cases (same pattern as getProp string/primitive)

You proved getProp string and primitive sub-cases. Now apply the SAME pattern to these value sub-cases:

### P0: deleteProp value (L3361)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Same pattern as getProp. `lean_goal` at L3361, then case split on value type.
- For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj`.

### P1: setProp value (L3500)
- `| some cv => sorry -- value sub-case (heap reasoning needed)`
- Object property set. Similar heap reasoning to getProp but writing.

### P2: getIndex value (L3431 — marked "skip for now")
- Array index access. Similar heap reasoning.

### P3: setIndex value (L3585 — marked "skip for now")
- Array index set. Similar heap reasoning.

### P4: call value (L3162) — after P0-P3
- Case split on `exprListValue? args`. When all args are values, use call execution lemma.

### P5: newObj (L3163) — after P4
- Object allocation. Heap reasoning for fresh address.

## BLOCKED (do NOT touch):
- L1177, L1178: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L2133, L2243: need convertExpr_not_lit for stub constructors
- L2327: HeapInj refactor staging
- L2646, L2668(×2): CCState threading (structural — if-branch dead code)
- L3733, L3831: all-values heap allocation (do after P5)
- L3777, L3875: ExprAddrWF propagation
- L3824, L4126: CCState threading
- L4005: functionDef (large)
- L4095: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics: `["simp [Flat.step?, Flat.evalTrivial]", "cases h_heap : sc.heap.objects[addr]?"]`
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## CRITICAL TACTIC HINT for value sub-cases:
All of L3361, L3431, L3500, L3585 have the shape:
```
| some cv => sorry -- value sub-case (heap reasoning needed)
```
The proof pattern is:
1. `simp [Flat.step?]` to unfold the Flat step
2. Case split on the value type (object addr vs primitive)
3. For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj` hypothesis
4. For primitives: both sides return the same primitive result

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
