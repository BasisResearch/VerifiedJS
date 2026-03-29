# jsspec — INTEGRATE YOUR STAGED PROOFS INTO CC. Target: CLOSE 2+ sorries NOW.

## STATUS: 60 sorries. ZERO progress last 2 runs. Your staging work is DONE. Now INTEGRATE.

## YOUR TARGETS — LINE NUMBERS VERIFIED 2026-03-29T12:05

### STEP 1: Add helper lemmas to CC file (ClosureConvertCorrect.lean)

Near L1790 (after existing Flat_step? helpers), add these from your staging:
- `Flat_step?_deleteProp_object_value`
- `Flat_step?_deleteProp_nonobject_value`
- `Flat_step?_setProp_object_both_values` / `nonobject_both_values`
- `Flat_step?_getIndex_object_both_values` / `other_both_values`
- `Flat_step?_setIndex_object_all_values` / `nonobject_all_values`
- `HeapInj_set_same` near L893

Near L1574 (after existing Core.step? helpers), add:
- `Core_step?_setProp_value_step`
- `Core_step?_getIndex_value_step`
- `Core_step?_setIndex_value_step_idx` / `value_step_val`

### STEP 2: Close L3337 — deleteProp value (EASIEST)
- Your staging has complete proof in `cc_deleteProp_value_proof.lean`
- Object: HeapInj_set_same + HeapValuesWF with filter
- Non-object: trivial (heap unchanged)
- **Build after this. If green, commit mentally and move to next.**

### STEP 3: Close L3113 — setProp value
- Your staging has complete proof in `cc_value_proofs_v2.lean` (B2)
- Non-object: trivial. Object: HeapInj via flatToCoreValue_convertValue + HeapInj_set_same

### STEP 4: Close L3011 — getProp object
- Read-only operation (no heap mutation!)
- HeapInj_get → same property list in Core and Flat
- Staging file has template

### STEP 5 (stretch): L3252 — setIndex value, L3183 — getIndex value

## proof agent IS HANDLING: L2154, L2989, L2990, L3485, L3583, L3529, L3627, L3757, L3847
DO NOT work on these.

## WORKFLOW
1. `lean_goal` at each sorry FIRST — verify line numbers match
2. Write helper lemma → `lake build` → use in sorry → `lake build`
3. If build breaks: SORRY IT BACK immediately
4. LOG to agents/jsspec/log.md every 30 min

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/` (read only — your staging reference)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
