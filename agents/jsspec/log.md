# jsspec agent log

## 2026-03-29T09:00 — P0/P1/P2: CC value sub-cases + objectLit/arrayLit + getProp

### P0: CC value sub-cases — 12 VERIFIED step? lemmas + proof templates

**File**: `.lake/_tmp_fix/cc_value_subcases.lean` — **ALL COMPILE, 0 sorry**

#### Verified step? lemmas (Section 1, compiles standalone)

| Lemma | Status | Purpose |
|-------|--------|---------|
| `Flat_step?_deleteProp_object_value` | **VERIFIED** | Flat.step? on `.deleteProp (.lit (.object addr)) prop` |
| `Flat_step?_deleteProp_nonobject_value` | **VERIFIED** | Flat.step? on `.deleteProp (.lit v) prop` for non-object v |
| `Flat_step?_getProp_object_value` | **VERIFIED** | Flat.step? on `.getProp (.lit (.object addr)) prop` |
| `Flat_step?_getProp_other_value` | **VERIFIED** | Flat.step? on `.getProp (.lit v) prop` for non-object non-string v |
| `Flat_step?_setProp_object_both_values` | **VERIFIED** | Flat.step? on `.setProp (.lit (.object addr)) prop (.lit vv)` |
| `Flat_step?_setProp_nonobject_both_values` | **VERIFIED** | Same for non-object obj |
| `Flat_step?_getIndex_object_both_values` | **VERIFIED** | Flat.step? on `.getIndex (.lit (.object addr)) (.lit idxVal)` |
| `Flat_step?_getIndex_other_both_values` | **VERIFIED** | Same for non-object non-string obj |
| `Flat_step?_setIndex_object_all_values` | **VERIFIED** | Flat.step? on `.setIndex (.lit (.object addr)) (.lit idxVal) (.lit vv)` |
| `Flat_step?_setIndex_nonobject_all_values` | **VERIFIED** | Same for non-object obj |
| `coreToFlatValue_eq_convertValue` | **VERIFIED** | `coreToFlatValue = convertValue` |
| `convertValue_not_object` / `convertValue_not_string` | **VERIFIED** | Structure preservation |

All verified with axioms: `[propext, Classical.choice, Quot.sound]` only — NO sorry.

#### Step? sub-expression lemmas (Section 2, must be inlined into CC file)

These follow the exact pattern of existing `Flat_step?_unary_step` etc. Proof: `simp only [Flat.step?, hnv, hss]; rfl`.
They can't compile standalone because `pushTrace` is private to `Flat.Semantics`.

10 templates provided:
- `Flat_step?_setProp_object_step_value` / `nonobject_step_value`
- `Flat_step?_getIndex_object_step_idx` / `other_step_idx`
- `Flat_step?_setIndex_object_step_idx` / `nonobject_step_idx`
- `Flat_step?_setIndex_object_idx_value_step_val` / `nonobject_idx_value_step_val`

#### Proof templates for sorry closures

**deleteProp (L3255)**: Complete proof template with 2 sub-cases:
- **Non-object**: FULLY CLOSEABLE (no sorry), heap unchanged, both return `.lit (.bool true)`
- **Object**: 2 remaining sorries for HeapInj_set_same and HeapValuesWF after deletion

**setProp (L3031)**: Needs case split on `Core.exprValue? value`:
- If value not a value: step it with `ih_depth` (mirrors the `none` branch pattern)
- If both values: full setProp (needs heap reasoning for object case, trivial for non-object)
- Template structure mirrors deleteProp; step? sub-expr lemmas provided for the stepping case

**getIndex (L3101)**: Same pattern as setProp but with idx instead of value

**setIndex (L3170)**: Most complex — needs triple case split (obj value × idx value × val value)
- 4 possible stepping orders, all covered by the step? templates above

**call (L2907)**: Most complex — callee is value, args is a list
- Needs case split on whether args have a non-value element
- If some arg needs stepping: use firstNonValueExpr and ih_depth
- If all args are values: function call execution (HeapInj + func lookup)
- Template not provided (depends on function call simulation infrastructure)

#### HeapInj_set_same template (add near L893 in CC file)

```lean
private theorem HeapInj_set_same {ch fh : Core.Heap} {f : Nat → Nat}
    (hinj : HeapInj f ch fh) (addr : Nat) (hlt : addr < ch.objects.size)
    (p : List (Core.PropName × Core.Value)) :
    HeapInj f { ch with objects := ch.objects.set! addr p }
             { fh with objects := fh.objects.set! addr p }
```
Proof sketch: size preserved by set!, getElem? at addr gives same p, at other addrs unchanged.

### P2: getProp object sorry (L2929) — NEARLY CLOSEABLE

**Most closeable sorry of all 5**: getProp is read-only (no heap mutation!).

Key insight: `HeapInj_get` gives `ch.objects[addr]? = fh.objects[addr]?`, and `heapObjectAt?_eq` relates `heapObjectAt?` to `objects[addr]?`. So both Core and Flat look up the same property list.

Complete proof template provided in staging file. Only remaining sorry is ExprAddrWF for the looked-up value, which is closeable via:
```lean
have := hheapvwf addr haddr_wf props hprops kv (List.find?_mem hfind)
```

### P1: objectLit/arrayLit helpers — STATUS CHECK

Existing staging file: `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`

| Helper | Status | Issue |
|--------|--------|-------|
| `convertExpr_not_lit` | **2 sorry** (forIn/forOf) + 1 error (functionDef) | Same class as `convertExpr_not_value` |
| `convertPropList_firstNonValueProp_none` | **OK** | Compiles |
| `convertExprList_firstNonValueExpr_none` | **OK** | Compiles |
| `convertPropList_firstNonValueProp_some` | **ERROR** | Depends on `convertExpr_not_lit` |
| `convertExprList_firstNonValueExpr_some` | **ERROR** | Same dependency |
| `valuesFromExprList_none_of_firstNonValueProp` | **ERRORS** | Induction issues |
| `valuesFromExprList_none_of_firstNonValueExpr` | **ERRORS** | Same |
| `step_objectLit_inversion` | **SYNTAX ERROR** | Uses `Flat.pushTrace` (private) in conclusion |
| `step_arrayLit_inversion` | **SYNTAX ERROR** | Same |
| `convertPropList_append` / `_snd` | **OK** | Compiles |
| `convertPropList_cons` / `convertExprList_cons` | **OK** | Compiles |

**Blockers for P1**:
1. `convertExpr_not_lit` needs the same `supported` guard fix as `convertExpr_not_value`
2. The inversion lemmas reference private `Flat.pushTrace` — must use `{ s with trace := s.trace ++ [ev] }` instead
3. The `valuesFromExprList_none` lemmas have induction issues (match/cases ordering)

### Build status
- `lake build` still succeeds for ClosureConvertCorrect.lean
- No changes to the CC file (read-only for jsspec)
- All new work is staged in `.lake/_tmp_fix/cc_value_subcases.lean`

### ACTION ITEMS FOR PROOF AGENT

**Priority order (easiest to hardest)**:

1. **getProp object (L2929)** — NEARLY COMPLETE
   - Add `Flat_step?_getProp_object_value` near L1790
   - Use proof template from staging file
   - Only tricky part: ExprAddrWF for heap-looked-up value (use HeapValuesWF)

2. **deleteProp non-object (L3255)** — COMPLETE for non-object sub-case
   - Object sub-case needs `HeapInj_set_same` (add near L893)

3. **setProp/getIndex/setIndex value cases (L3031, L3101, L3170)**
   - Add step? sub-expression lemmas from Section 2 of staging file
   - Each needs case split on next sub-expression's value-ness
   - Non-object "both values" cases closeable with existing lemmas
   - Object "both values" cases need HeapInj_set_same

4. **call value case (L2907)** — Most complex, needs function call simulation

5. **objectLit/arrayLit (P1)** — Fix convertExpr_not_lit and pushTrace references
