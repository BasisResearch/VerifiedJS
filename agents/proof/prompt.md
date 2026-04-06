# proof — K-independence lemma + compound cases

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~2.3GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L13697+ and L14792+ zones (if_branch individual cases)
- jsspec may work on list cases (L10159, L10183-10187)
- **YOU** own L10063-L10158 (second-position cases) AND compound zones (L11434+)
- DO NOT touch wasmspec or jsspec zones

## ===== CRITICAL DISCOVERY: K-MISMATCH IN SECOND-POSITION CASES =====

**The ¬HasLabeledInHead sub-cases for second-position are BLOCKED by a fundamental issue.**

The seq_right case works because `normalizeExpr (.seq b a) K = normalizeExpr a K` — the continuation K passes through UNCHANGED. After stepping b→value and discarding, `normalizeExpr a K` uses the SAME K.

For binary_rhs: `normalizeExpr (.binary op lhs rhs) K = normalizeExpr rhs K_rhs` where
`K_rhs = fun rhsTriv => bindComplex (.binary op (trivialOfFlat lhs) rhsTriv) K`. After stepping lhs (.var x) → (.lit v): `normalizeExpr (.binary op (.lit v) rhs) K = normalizeExpr rhs K_rhs'` where
`K_rhs' = fun rhsTriv => bindComplex (.binary op (trivialOfFlatValue v) rhsTriv) K`.

**K_rhs ≠ K_rhs'** because `trivialOfFlat (.var x) = .var x` but `trivialOfFlatValue v = .litNum/.litBool/...`. The ANF body CHANGES when lhs is evaluated. The theorem conclusion needs the SAME body, so it's UNSATISFIABLE.

### Option A: Prove a K-independence lemma (PREFERRED)
If normalizeExpr e K = .ok (.labeled label body, m) and HasLabeledInHead e label, then .labeled comes from e, not K. So for any K': normalizeExpr e K' = .ok (.labeled label body', m') where body' may differ from body. But the OUTER .labeled label wrapper is preserved.

The theorem conclusion needs `normalizeExpr sf'.expr K = .ok (body, m')` — body WITHOUT .labeled wrapper. Since body depends on K (the labeled body is `normalizeExpr inner K`), and K changes after stepping... this option is HARD.

### Option B: Case-split on whether lhs is already a value
When lhs = .lit v (already a value), there's NO K-mismatch! `trivialOfFlat (.lit v) = trivialOfFlatValue v`. This case is directly provable. For lhs NOT a value: leave sorry or prove impossible from ExprWellFormed + normalizeExpr structure.

### Option C: Restrict HasLabeledInHead
Remove binary_rhs and other second-position constructors. This would require showing the downstream usage never needs them.

## ===== PRIORITY: INVESTIGATE AND UNBLOCK =====

**P0: Determine if second-position cases are truly needed.**
1. Check ALL call sites of `normalizeExpr_labeled_branch_step` (~L10700, L10770, L10816)
2. At each call site, check what `hlh : HasLabeledInHead` is passed
3. If `hlh` is always a first-position constructor, second-position cases are DEAD CODE
4. If second-position IS needed, investigate Option B (case-split on lhs being a value)

**P1: If second-position is dead code, remove the constructors.**
Remove binary_rhs, setProp_val, getIndex_idx, setIndex_idx, setIndex_val, call_env, newObj_env, call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems from HasLabeledInHead. This eliminates 12 sorries instantly.

**P2: If second-position IS needed, try Option B.**
For each second-position case, add `cases lhs with | lit v => ... | _ => sorry`.
The `.lit v` sub-case is directly provable (K matches). Leave others as sorry.

## YOUR 6 SECOND-POSITION SORRIES (may be removable):
- L10063: `binary_rhs h_rhs => sorry`
- L10086: `setProp_val h_val => sorry`
- L10109: `getIndex_idx h_idx => sorry`
- L10133: `setIndex_idx h_idx => sorry`
- L10134: `setIndex_val h_val => sorry`
- L10158: `call_env h_env => sorry`

## DO NOT TOUCH (other agents):
- L10159, L10183-L10187 (list cases — jsspec)
- L13697+, L14792+ (if_branch — wasmspec)
- L15809+ (blocked cases)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
