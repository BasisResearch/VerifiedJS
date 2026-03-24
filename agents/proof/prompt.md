# proof — Close ExprAddrWF sorries (44 of them) then remaining CC

You own Proofs/*.lean and compiler passes. HeapCorr is DONE. ExprAddrWF is DEFINED and in CC_SimRel.

## TASK 0 (DO FIRST): Fix ExprAddrWF_mono (L657) — VERIFIED PROOF

Replace `sorry` at line 657 with this EXACT code (verified via lean_multi_attempt — "No goals"):

```lean
  match e with
  | .lit v => exact ValueAddrWF_mono h hle
  | .var _ | .call _ _ | .newObj _ _ | .objectLit _ | .arrayLit _ | .break _ | .continue _ | .return none | .yield none _ | .this => trivial
  | .«let» _ init body => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .assign _ value => exact ExprAddrWF_mono h hle
  | .«if» cond t el => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2.1 hle, ExprAddrWF_mono h.2.2 hle⟩
  | .seq a b => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .getProp obj _ => exact ExprAddrWF_mono h hle
  | .setProp o _ v => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .getIndex e1 e2 => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .setIndex o i v => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2.1 hle, ExprAddrWF_mono h.2.2 hle⟩
  | .deleteProp obj _ => exact ExprAddrWF_mono h hle
  | .typeof arg => exact ExprAddrWF_mono h hle
  | .unary _ arg => exact ExprAddrWF_mono h hle
  | .binary _ l r => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .functionDef _ _ body _ _ => exact ExprAddrWF_mono h hle
  | .throw arg => exact ExprAddrWF_mono h hle
  | .tryCatch b _ c none => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .tryCatch b _ c (some fe) => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2.1 hle, ExprAddrWF_mono h.2.2 hle⟩
  | .while_ c b => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .forIn _ o b => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .forOf _ i b => exact ⟨ExprAddrWF_mono h.1 hle, ExprAddrWF_mono h.2 hle⟩
  | .return (some arg) => exact ExprAddrWF_mono h hle
  | .yield (some arg) _ => exact ExprAddrWF_mono h hle
  | .labeled _ b => exact ExprAddrWF_mono h hle
  | .await arg => exact ExprAddrWF_mono h hle
```

## TASK 1: Close 44 `sorry /- ExprAddrWF -/` sites

There are 44 instances. Two patterns:

### Pattern A — Conclusion tuples (e.g. L964, L1038, L1095, L1285, L1743, ...)
These need `ExprAddrWF sc'.expr sc'.heap.objects.size`. Three sub-patterns:

**A1. Heap unchanged, result is sub-expression** (labeled, typeof, unary, break, continue, var, etc.):
- `sc'.expr` is a sub-expression of `sc.expr`, heap unchanged
- Extract from `hexprwf` (the CC_SimRel ExprAddrWF component)
- Replace `sorry /- ExprAddrWF -/` with:
  ```lean
  by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h
  ```
  or for nested (e.g. `.let` body): `exact h.2` or `exact h.1`

**A2. Result is `.lit (.object addr)` where `addr = old heap size`** (objectLit, arrayLit, newObj, setProp, setIndex):
- New heap size = old + 1, addr = old size
- Replace with: `by simp [ExprAddrWF, ValueAddrWF]; omega`

**A3. Result is `.lit v` for non-object `v`** (break→undefined, continue→undefined, return→undefined, etc.):
- Replace with: `by simp [ExprAddrWF, ValueAddrWF]`

### Pattern B — IH calls (e.g. L1184, L1317, L1466, L1624, ...)
These pass ExprAddrWF to `ih_depth` or `ev_sub`. Need `ExprAddrWF sub_expr sc.heap.objects.size`.

- Extract from `hexprwf` by decomposing: `rw [hsc] at hexprwf; simp [ExprAddrWF] at hexprwf`
- Then `exact hexprwf.1` or `exact hexprwf.2` or `exact hexprwf.2.1` etc.
- Replace `sorry /- ExprAddrWF -/` with:
  ```lean
  by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.1
  ```

### IMPORTANT: Use `lean_multi_attempt` to test each fix before editing!

Try these tactics at each sorry site:
```
["by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h",
 "by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.1",
 "by have h := hexprwf; rw [hsc] at h; simp [ExprAddrWF] at h; exact h.2",
 "by simp [ExprAddrWF, ValueAddrWF]",
 "by simp [ExprAddrWF, ValueAddrWF]; omega"]
```

## TASK 2: Remaining CC sorries (after ExprAddrWF)

Only 2 non-ExprAddrWF CC sorries remain:
- **L978**: captured variable case
- **L4787**: init sorry (`closureConvert_init_related`)

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
