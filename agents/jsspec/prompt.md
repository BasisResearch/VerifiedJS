# jsspec — IMPLEMENT CCStateAgree FIX (unblocks 6 sorries!)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 15 actual sorries. You closed arrayLit and consoleLog type mismatch — EXCELLENT.
All easy non-blocked targets are exhausted. 6 of remaining sorries are BLOCKED by CCStateAgree.

## ⚠️⚠️⚠️ THIS IS THE HIGHEST IMPACT TASK ⚠️⚠️⚠️

### TOP PRIORITY: Fix CCStateAgree invariant (L3355-3357)

wasmspec analyzed the CCStateAgree blocker in detail. The root cause:

**The invariant at L3355-3357 requires output CCStateAgree:**
```lean
∃ (st_a st_a' : Flat.CCState),
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧ CCStateAgree st' st_a'  -- ← output agreement FAILS
```

**Why it fails**: When a step DISCARDS sub-expressions (if-then discards else_, if-else skips then_) or DUPLICATES them (while_ unrolling), the CCState from converting the original expression doesn't match the CCState from converting the stepped expression. `convertExpr` increments `nextId` via `freshVar` for each sub-expression it processes.

**The fix**: Drop output CCStateAgree. Change L3355-3357 to:
```lean
∃ (st_a : Flat.CCState),
  sf'.expr = (Flat.convertExpr sc'.expr scope envVar envMap st_a).fst ∧
  CCStateAgree st st_a
```

This is sufficient because:
- Cases that NEED output agreement (sub-stepping like tryCatch non-error) can prove it via a standalone lemma
- Cases that FAIL output agreement (if branch, while_ unroll) are resolution/expansion steps where no outer expression needs the bridge

### IMPLEMENTATION STEPS:

1. **Read L3330-3365** to understand the full theorem signature
2. **Change L3355-3357**: Remove `st_a'` from the existential, drop `CCStateAgree st' st_a'`
3. **Fix L3359** (the `obtain` that destructures the result): Remove `st_a'` binding
4. **Fix L3361** (the `exact` that packs the result): Remove `st_a'`
5. **For each of the 6 blocked sorries** (L3715, L3738×2, L6516, L6587, L6694):
   - The existential now only needs `st_a` and input `CCStateAgree st st_a`
   - For if-then (L3715): `st_a = st`, input agreement trivial by `⟨rfl, rfl⟩`
   - For if-else (L3738): `st_a = st_t` (state after then_), need `CCStateAgree st st_t` — may need monotonicity lemma
   - For while_ (L6694): `st_a = st`, input agreement trivial
   - For tryCatch (L6516, L6587): similar analysis
6. **Fix any sub-stepping cases** that relied on output agreement (tryCatch non-error around L6643):
   - May need a standalone lemma for output agreement in sub-stepping cases
   - `convertExpr_state_determined` (L566) bridges via input agreement
7. **Build and verify**: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

### AFTER CCStateAgree FIX: newObj (L4477/4485)

If CCStateAgree fix goes well and you have time:
```lean
| newObj f args => sorry -- f not a value / non-value arg
```
Similar to arrayLit. Both involve constructor + args. Pattern:
- All-values: both Core and Flat allocate, HeapInj via `alloc_both`
- Non-value: find first non-value, step it, use IH

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5123 getIndex string — UNPROVABLE (Float.toString opaque)
- L4271 non-consoleLog call — BLOCKED no FuncsCorr
- L3387 captured var — multi-step gap

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. Read the invariant at L3355-3357
3. Implement the fix
4. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
