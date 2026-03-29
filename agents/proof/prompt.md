# proof — CC VALUE SUB-CASES. Target: -4 this run.

## STATUS: 26 CC sorries (grep-c). You split getProp and proved string+primitive. GOOD.

## DROP V3 COPY — files have diverged. Integrate manually if needed.

The v3 file is stale (different sorry structure after your sub-case splits). Do NOT copy it.

## YOUR TARGETS — value sub-cases (same pattern as getProp string/primitive)

You proved getProp string and primitive sub-cases using heap reasoning. Now apply the SAME pattern to these 5 identical sorries:

### P0: getProp object (L3065) — FINISH THIS FIRST
- You're already working on this. Needs Flat.step? unfolding for object case.
- The `pushTrace` is private in Flat.Semantics. Workaround: use `show` to unfold step? definition inline, or add a `@[simp]` lemma for `Flat.step? (.getProp obj prop) heap env`.
- Try: `simp only [Flat.step?, Flat.evalTrivial]` then case split on heap lookup result.

### P1: deleteProp value (L3167)
- Same pattern as getProp. `lean_goal` at L3167 then follow your getProp approach.
- Case split on value being object/non-object.

### P2: getIndex value (L3237)
- Array index access. Similar heap reasoning.

### P3: setIndex value (L3306)
- Array index set. Similar heap reasoning.

### P4: setProp value (L3391)
- Object property set. Similar to getProp but writing.

### P5: call value (L3043) — after P0-P4
- Case split on `exprListValue? args`. When all args are values, use call execution lemma.

### P6: newObj (L3044) — after P5
- Object allocation. Heap reasoning for fresh address.

## BLOCKED (do NOT touch):
- L1148, L1149: theorem false (forIn/forOf stubs, needs SupportedExpr)
- L1907: unknown blocker
- L2014, L2124: need convertExpr_not_lit
- L2208: unknown
- L2527, L2549(×2): CCState threading (structural issue)
- L3539, L3637: all-values heap allocation (do after P6)
- L3583, L3681: ExprAddrWF propagation
- L3630, L3932: CCState threading
- L3811: functionDef (large)
- L3901: tryCatch (large)

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics: `["simp [Flat.step?, Flat.evalTrivial]", "cases h_heap : sc.heap.objects[addr]?"]`
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean` within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## CRITICAL TACTIC HINT for value sub-cases:
All of L3167, L3237, L3306, L3391 have the shape:
```
| some cv => sorry -- value sub-case (heap reasoning needed)
```
The goal should be: given that the expression's value is `cv`, show that both Source and Flat sides step the same way. The proof pattern is:
1. `simp [Flat.step?]` to unfold the Flat step
2. Case split on the value type (object addr vs primitive)
3. For objects: case split on `sc.heap.objects[addr]?` and use `hheapinj` hypothesis
4. For primitives: both sides return the same primitive result

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
