# proof — CC + ANF sorries. Target: CLOSE 3+ sorries this run.

## STATUS: 60 sorries (17 ANF + 25 CC + 18 Wasm). FLAT 4 consecutive runs. MUST CLOSE SORRIES NOW.

## P0 — APPLY JSSPEC PATCH IMMEDIATELY (instant -3 sorries)

jsspec created a COMPLETE, TESTED patch at `.lake/_tmp_fix/jsspec_final_v2.patch`.
It closes 3 CC sorries: deleteProp value (L3337), setProp value (L3113), getProp object (L3011).
jsspec CANNOT write to CC file (permissions). YOU must apply it.

```bash
cd /opt/verifiedjs
patch -p1 < .lake/_tmp_fix/jsspec_final_v2.patch
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```

If build fails: `patch -R -p1 < .lake/_tmp_fix/jsspec_final_v2.patch` to revert ALL,
then try applying just the helper lemma hunks (first 4 hunks add helpers, last 3 close sorries).

DO THIS FIRST BEFORE ANYTHING ELSE. This is free sorry reduction.

## CC SORRY MAP (25 actual sorries) — LINE NUMBERS VERIFIED 2026-03-29T13:05

### BLOCKED (do NOT touch):
- L1148, L1149: false theorems (forIn/forOf stubs)
- L1960, L2070: need convertExpr_not_lit for stubs
- L2473, L2495(×2): CCState threading if-branches
- L3576: CCState threading objectLit
- L3878: CCState threading while_

### After applying patch, YOUR TARGETS (sorted by closability):

#### P1: L3183 — getIndex value (FOLLOW PATTERN FROM PATCH)
- After patch, you have Flat_step?_getIndex helpers already added
- Follow exact same pattern as deleteProp/setProp proofs in the patch

#### P2: L3252 — setIndex value (FOLLOW PATTERN FROM PATCH)
- Same class. Flat_step?_setIndex helpers from patch.

#### P3: L2154 — captured var (1:N stepping)
- Captured var converts to `.getEnv (.var envVar) idx`
- Flat needs 2 steps, Core 1 step

#### P4: L2990 — newObj
- Object allocation, both Core/Flat allocate on heap

#### P5: L2989 — call value sub-case
- Case split on exprListValue? args

#### P6: L3485, L3583 — objectLit/arrayLit all-values
- Heap allocation, similar to newObj

#### P7: L3529, L3627 — ExprAddrWF propagation

#### P8: L3757 — functionDef
#### P9: L3847 — tryCatch

## WORKFLOW — MANDATORY
1. **FIRST**: Apply jsspec patch (P0 above)
2. `lean_goal` BEFORE every sorry attempt
3. `lean_multi_attempt` to test tactics
4. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
5. If build breaks: SORRY IT BACK within 2 minutes
6. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/jsspec_final_v2.patch` (read — jsspec's tested patch)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
