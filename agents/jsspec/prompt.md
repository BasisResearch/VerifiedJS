# jsspec — CC VALUE SUB-CASES: you own L2907, L3031, L3101, L3170, L3255

## STATUS: 60 sorries. CC stuck at 25 this run. WE NEED CLOSES. Your staged proofs are ready — INTEGRATE THEM.

## YOUR TARGETS (5 value sub-cases) — LINE NUMBERS VERIFIED 2026-03-29T11:05

### You already staged proofs in `.lake/_tmp_fix/`. NOW CLOSE THE SORRIES.

### L3255 — deleteProp value (EASIEST — start here)
- Your staging file `cc_deleteProp_value_proof.lean` has the complete proof
- Add `Flat_step?_deleteProp_object_value` + `Flat_step?_deleteProp_nonobject_value` near L1790
- Add `HeapCorr_set_same` near L893 if not already there
- Replace sorry at L3255 with staged proof

### L3031 — setProp value
- `cc_all_value_proofs.lean` has the template
- Add `Flat_step?_setProp_value_value` helper
- Case split: object vs non-object

### L3101 — getIndex value
### L3170 — setIndex value
- Same pattern as setProp. Add step? helpers, case split.

### L2907 — call value (HARDEST — do last)
- Callee is value → case split on `Core.exprListValue? args`
- All args values → execute call (function simulation)
- Some arg needs stepping → `firstNonValueExpr` + ih

### Helper lemma pattern (all compile in staging):
```lean
cases ve_or_ie with
| lit v => simp [Core.exprValue?] at hnv
| _ => cases cv <;> simp [Core.step?, Core.exprValue?, hss, Core.pushTrace]
```

## ALSO CONSIDER if blocked: L3429, L3517 (step extraction), L3437, L3525 (ExprAddrWF)

## proof agent IS HANDLING: L2929 (getProp), L2908 (newObj), L3403/L3491 (all-values), L3655 (functionDef)
DO NOT work on these.

## WORKFLOW
1. `lean_goal` at each sorry FIRST
2. Write helper lemma → build → use in sorry → build
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK immediately
5. LOG to agents/jsspec/log.md every 30 min

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/` (read only — your staging reference)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
