# proof — Close CC sorries (ExprAddrWF is #1 priority)

You own Proofs/*.lean and compiler passes. HeapCorr is DONE. ExprAddrWF is DEFINED and in CC_SimRel.

## TASK 0 (DO FIRST): Close ExprAddrWF_mono (L657) — unlocks ~20 sorries

```lean
private theorem ExprAddrWF_mono {e : Core.Expr} {n m : Nat}
    (h : ExprAddrWF e n) (hle : n ≤ m) : ExprAddrWF e m := by
  sorry  -- THIS IS LINE 657
```

**Fix**: Structural induction on `e`. Each case is either `True` (trivially holds) or recurses. Pattern:

```lean
  induction e with
  | lit v => exact ValueAddrWF_mono h hle
  | var _ => trivial
  | «let» _ init body ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | assign _ value ih => exact ih h hle
  | «if» cond t e ih1 ih2 ih3 => exact ⟨ih1 h.1 hle, ih2 h.2.1 hle, ih3 h.2.2 hle⟩
  | seq a b ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | call _ _ | newObj _ _ | objectLit _ | arrayLit _ | «break» _ | «continue» _ | «return» none | yield none _ | this => trivial
  | getProp e _ ih => exact ih h hle
  | setProp o _ v ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | getIndex e1 e2 ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | setIndex o i v ih1 ih2 ih3 => exact ⟨ih1 h.1 hle, ih2 h.2.1 hle, ih3 h.2.2 hle⟩
  | deleteProp e _ ih => exact ih h hle
  | typeof e ih => exact ih h hle
  | unary _ e ih => exact ih h hle
  | binary _ l r ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | functionDef _ _ body _ _ ih => exact ih h hle
  | throw e ih => exact ih h hle
  | tryCatch b _ c fe ih1 ih2 ih3 => cases fe <;> simp [ExprAddrWF] at * <;> exact ⟨ih1 h.1 hle, ih2 h.2.1 hle, ih3 h.2.2 hle⟩  -- adjust for none case
  | while_ c b ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | forIn _ o b ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | forOf _ i b ih1 ih2 => exact ⟨ih1 h.1 hle, ih2 h.2 hle⟩
  | «return» (some e) ih => exact ih h hle
  | yield (some e) _ ih => exact ih h hle
  | labeled _ b ih => exact ih h hle
  | await e ih => exact ih h hle
```

Adjust constructor names to match your `Core.Expr` definition. Use `lean_goal` at L657 if unsure of exact names.

## TASK 1: Close ~20 `sorry /- ExprAddrWF -/` sites

All instances of `sorry /- ExprAddrWF -/` need `ExprAddrWF sc'.expr sc'.heap.objects.size`. Pattern for each case:

**When heap unchanged** (most cases — break, continue, return, labeled, typeof, unary, etc.):
- `sc'.expr` is a sub-expression of `sc.expr` → extract from `ExprAddrWF sc.expr n`
- Heap unchanged → same `n`
- Proof: `simp [ExprAddrWF] at haddr ⊢; exact haddr.1` (or `.2`, depending on which sub-expr)

**When heap grows** (objectLit, arrayLit, newObj, setProp, etc.):
- `sc'.expr = .lit (.object addr)` where `addr = old heap size`
- New heap size = old + 1, so `addr < new_size` by `omega`
- Proof: `simp [ExprAddrWF, ValueAddrWF]; omega`

**When stepping a sub-expression** (let init, if cond, binary lhs, etc.):
- Use `ExprAddrWF_mono` with `hle : old_heap ≤ new_heap` (since heap only grows)

Try `simp [ExprAddrWF, ValueAddrWF] at *` first. Many will close with `omega` or `trivial` after simp.

## TASK 2: Close L1764 and L2172 (well-formedness)

After ExprAddrWF_mono is proved, these close because:
- `ExprAddrWF (.getProp (.lit (.object addr)) prop) sc.heap.objects.size` gives `addr < sc.heap.objects.size`
- This contradicts `hge : addr ≥ sc.heap.objects.size`
- Proof: `exact absurd haddr (Nat.not_lt.mpr hge)` (adjust names)

## TASK 3: objectLit (L3137) and arrayLit (L3138) — NOW UNBLOCKED

wasmspec added `allocObjectWithProps` that populates heap props. Both Core and Flat now push actual properties.

## TASK 4: newObj (L1689) — NOT blocked

Both Core and Flat push `[]` for newObj. HeapCorr is preserved (same empty list pushed to both heaps). Should be provable now.

## TASK 5: ANF (L106, L1181), call (L1688), functionDef (L3139) — later

## Rules
- `bash scripts/lake_build_concise.sh` to build (only ONCE at end)
- lean_goal + lean_multi_attempt BEFORE editing
- Log strategy + progress to agents/proof/log.md
