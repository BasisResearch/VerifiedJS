# jsspec — CC VALUE SUB-CASES: you own L2959, L3083, L3153, L3222, L3307

## STATUS: 60 sorries. CC down 2 to 25! You helped make this happen. KEEP GOING.

## YOUR TARGETS (5 value sub-cases, all same pattern)

### Pattern for all 5:
- `Core.exprValue? subexpr = some cv` means `subexpr = .lit cv`
- Flat side has the converted lit value
- `step?` on the Flat side evaluates the value part
- Need `HeapInj` to map Core heap operations to Flat heap operations
- Template: the STRING case of getProp (search for `getProp` proved case around L2930-2975)

### L2959 — call: callee is value
- When callee is a value, case split on `Core.exprListValue? args`
- All args values → execute the call (needs function call simulation)
- Some arg needs stepping → use firstNonValueExpr + ih_depth
- This is the HARDEST of the 5. Save for last if stuck.

### L3083 — setProp value sub-case
### L3153 — getIndex value sub-case
### L3222 — setIndex value sub-case
### L3307 — deleteProp value sub-case

These 4 are simpler than call. Start with L3307 (deleteProp) — closest to getProp pattern.

### Helper lemmas to add (near L1790):
- `Flat_step?_deleteProp_object_value`: unfolding `step?` for `.deleteProp (.lit (.object addr)) prop`
- `Flat_step?_setProp_value_value`: for `.setProp (.lit v1) prop (.lit v2)`
- Similar for getIndex, setIndex

## ALSO CONSIDER: L3500, L3599 (ExprAddrWF propagation)
If value sub-cases are blocked, these may be easier — they need `ExprAddrPropListWF` / `ExprAddrListWF` helpers.

## proof agent IS HANDLING: L2981 (getProp object), L2960 (newObj), L3455/L3554 (all-values), L3729 (functionDef)
DO NOT work on these.

## WORKFLOW
1. `lean_goal` at each sorry FIRST
2. Write helper lemma → build → use in sorry → build
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK immediately
5. LOG to agents/jsspec/log.md every 30 min

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/` (read only — staging reference)

## DO NOT EDIT: `VerifiedJS/Proofs/ANFConvertCorrect.lean`, `VerifiedJS/Wasm/Semantics.lean`
