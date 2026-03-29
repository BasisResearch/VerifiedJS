# proof — INTEGRATE JSSPEC V3 + CLOSE CC SORRIES. Target: -5 this run.

## STATUS: 60 sorries (17 ANF + 25 CC + 18 Wasm). FLAT 5 CONSECUTIVE RUNS. EMERGENCY.

## P0 — COPY JSSPEC INTEGRATED FILE (instant -3 sorries)

jsspec's integrated v3 file closes 3 CC sorries and adds 9 helper lemmas.
The patch won't apply cleanly (hunk 3 context shifted). Use the FULL FILE instead:

```bash
cp .lake/_tmp_fix/CC_integrated_v3.lean VerifiedJS/Proofs/ClosureConvertCorrect.lean
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```

If build fails, revert with `git checkout VerifiedJS/Proofs/ClosureConvertCorrect.lean`.

The v3 file has 22 sorries (vs current 25). It adds:
- `list_find?_mem`, `HeapInj_set_same` (near L895)
- 7 Flat_step?/Core_step? helpers (near L1971)
- Closes: getProp ExprAddrWF (was L3093), deleteProp value (was L3355), setProp value (was L3216)

**DO THIS FIRST. This is 3 free sorry closures.**

If the build fails after copying, diff the two files to identify the conflict:
```bash
diff VerifiedJS/Proofs/ClosureConvertCorrect.lean .lake/_tmp_fix/CC_integrated_v3.lean
```
Then manually integrate the changes.

## CC SORRY MAP (22 after v3 applied) — TARGETS

### YOUR TARGETS (sorted by closability):

#### P1: getIndex value (was ~L3286)
- Same pattern as deleteProp/setProp proofs from v3
- use lean_goal at the sorry, then follow the exact same heap reasoning pattern

#### P2: setIndex value (was ~L3440)
- Same class. Follow setProp pattern.

#### P3: L3093 → ExprAddrWF (ONLY if v3 didn't close it)
- `cases` on `sc.heap.objects[addr]?`, then `find?`, use `hheapvwf` + `list_find?_mem`

#### P4: call value (was ~L3043)
- Case split on `exprListValue? args`

#### P5: newObj (was ~L3044)
- Object allocation on heap

#### P6: objectLit/arrayLit all-values (was ~L3588, L3686)
- Heap allocation, similar to newObj

#### P7: ExprAddrWF propagation (was ~L3632, L3730)

#### P8: functionDef (was ~L3860)
#### P9: tryCatch (was ~L3950)

### BLOCKED (do NOT touch):
- L1148, L1149: false theorems (forIn/forOf stubs)
- L2014, L2124: need convertExpr_not_lit for stubs
- L2208: unknown
- L2527, L2549(×2): CCState threading if-branches
- L3679, L3981: CCState threading

## WORKFLOW — MANDATORY
1. **FIRST**: Copy v3 file (P0 above) and BUILD
2. `lean_goal` BEFORE every sorry attempt — line numbers WILL SHIFT after v3 copy
3. `lean_multi_attempt` to test tactics
4. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
5. If build breaks: revert within 2 minutes
6. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/CC_integrated_v3.lean` (read — jsspec's tested full file)
- `.lake/_tmp_fix/jsspec_v3.patch` (read — jsspec's diff)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
