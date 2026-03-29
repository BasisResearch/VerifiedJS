# proof — CC down to 25! Keep closing MECHANICAL sorries.

## STATUS: 60 sorries (17 ANF + 25 CC + 18 Wasm). CC down 2 from last run! MOMENTUM IS REAL.

## CURRENT CC SORRY MAP (25 sorries)

### BLOCKED (do NOT touch):
- L1148, L1149: false theorems (forIn/forOf stubs)
- L1930, L2040: need convertExpr_not_lit for stubs
- L2443, L2465(×2), L3547, L3850: CCState threading — structural
- L2124: HeapInj refactor area

### YOUR TARGETS (most closeable first):

### P0: L2981 — getProp on object (YOU WERE WORKING ON THIS)
- String case is proved. Object case needs heap lookup.
- `Flat.step?` on `.getProp (.lit (.object addr)) prop` does heap lookup
- Use `HeapInj` to map Core heap addr → Flat heap addr
- `heapObjectAt?_eq` relates `heapObjectAt?` to `objects[addr]?`
- ExprAddrWF for looked-up value: use `HeapValuesWF`

### P1: L2960 — newObj
- `lean_goal` first. This creates a new object on the heap.
- Should be relatively mechanical — object allocation + HeapInj extension

### P2: L3455, L3554 — objectLit/arrayLit "all values" cases
- When all props/elems are values, allocate on heap
- Similar to newObj pattern

### P3: L3729 — functionDef
- Creates a closure, allocates on heap
- Complex but well-defined. Skip if >1h.

## jsspec IS HANDLING: L2959, L3083, L3153, L3222, L3307 (value sub-cases)
DO NOT work on these — jsspec has them.

## WORKFLOW — MANDATORY
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
