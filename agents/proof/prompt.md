# proof — Close ExprAddrWF sorries (44 mechanical) then remaining CC/ANF

You own Proofs/*.lean and compiler passes. HeapCorr is DONE. ExprAddrWF is DEFINED and in CC_SimRel. ExprAddrWF_mono is PROVED.

## TASK 0 (DO FIRST): Close 44 `sorry /- ExprAddrWF -/` sites

There are ~44 instances of `sorry /- ExprAddrWF -/` in ClosureConvertCorrect.lean. Two patterns:

### Pattern A — Tuple positions (e.g. L989, L1063, L1120, L1310, L1451, ...)
These fill the ExprAddrWF slot in a CC_SimRel tuple. The sorry is in term mode inside `exact ⟨..., sorry /- ExprAddrWF -/, ...⟩`.

**Sub-expression case** (heap unchanged, result is sub-expression of `sc.expr`):
Replace `sorry /- ExprAddrWF -/` with:
```lean
(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; rw [hsc'_expr]; exact h)
```
For nested sub-expressions, project: `exact h.1`, `exact h.2`, `exact h.2.1`, `exact h.2.2`

**Literal result** (result is `.lit v` for non-object):
```lean
(by simp [ExprAddrWF, ValueAddrWF])
```

**New heap object** (result is `.lit (.object addr)` where `addr = old heap size`):
```lean
(by simp [ExprAddrWF, ValueAddrWF]; omega)
```

### Pattern B — IH call arguments (e.g. L1491, L1649, L1820, L1881, ...)
These pass ExprAddrWF to `ev_sub` or `ih_depth`. VERIFIED at L1491 — all 3 tactics close:
```lean
(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.1)
(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h)
(by simp [ExprAddrWF, ValueAddrWF]; omega)
```

### WORKFLOW: For each sorry site:
1. `lean_multi_attempt` with these 5 tactics (omit `by` if already in tactic mode):
   ```
   ["(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h)",
    "(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.1)",
    "(by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.2)",
    "(by simp [ExprAddrWF, ValueAddrWF])",
    "(by simp [ExprAddrWF, ValueAddrWF]; omega)"]
   ```
2. Replace `sorry /- ExprAddrWF -/` with the one that succeeds
3. Move to next sorry site

## TASK 1: Remaining CC sorries (5 non-ExprAddrWF)

After ExprAddrWF, only these remain:
- **L1003**: captured variable case (needs getEnv proof)
- **L1713**: call (needs env/heap/funcs correspondence)
- **L1714**: newObj (needs env/heap correspondence)
- **L3153**: objectLit (needs heap with allocObjectWithProps)
- **L3154**: arrayLit (needs heap with allocObjectWithProps)
- **L3155**: functionDef (needs env/heap/funcs + CC state)
- **L4812**: init sorry in closureConvert_init_related

## TASK 2: ANF sorries (2 remain)

- **ANFConvertCorrect.lean:106**: main theorem
- **ANFConvertCorrect.lean:1181**: induction case

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
