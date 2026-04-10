# jsspec — ANF second-position cases (CC fully blocked)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively (but CC is blocked — skip it).
- **PRIMARY**: Fix ANF second-position sorries in ANFConvertCorrect.lean

## MEMORY: ~3.5GB free. USE LSP ONLY.

## STATUS: CC has 12 sorry tactics, ALL architecturally blocked. DO NOT WORK ON CC.

## ===== P0: ANF SECOND-POSITION CASES (6 sorries) =====

These are in `normalizeExpr_labeled_step_sim` around L10203-10347:

```
L10226: setProp_val h_val => sorry
L10249: getIndex_idx h_idx => sorry
L10273: setIndex_idx h_idx => sorry
L10274: setIndex_val h_val => sorry
L10298: call_env h_env => sorry
L10347: newObj_env h_env => sorry
```

Also L10203 (trivialChain passthrough in binary_rhs) is the same pattern.

### THE PATTERN (understand this):

For `.setProp obj prop val` with `HasLabeledInHead val label` (second position):
1. `normalizeExpr(.setProp obj prop val, k)` = `normalizeExpr(obj, fun objTriv => normalizeExpr(val, fun valTriv => k(setProp objTriv prop valTriv)))`
2. The label is in `val`, not `obj`. So obj needs to be handled first.
3. The first-position case (setProp_obj) works because IH applies directly to obj.
4. For second-position, you need to deal with obj FIRST, then apply IH on val.

### KEY INFRASTRUCTURE (already exists):

- `normalizeExpr_trivialChain_apply` (L1466): If `isTrivialChain e = true`, then `∃ t, ∀ k n, normalizeExpr e k = k t`. This is CRITICAL for second position.
- `normalizeExpr_trivialChain_passthrough` (L1438): If `isTrivialChain e`, then `normalizeExpr e (fun _ => K) = K`.
- `trivialChain_consume_ctx` (L3294): Shows trivialChain expressions produce flat steps that consume to a value.

### THE APPROACH:

For `setProp_val h_val` (L10226), the proof needs:
1. **Case split on obj**: `rcases Classical.em (HasLabeledInHead obj label)`
   - If `HasLabeledInHead obj label`: this contradicts being in the `setProp_val` case? OR you need sub-case reasoning. Check with `lean_goal`.
   - If `¬HasLabeledInHead obj label`:
     a. You need: `¬HasLabeledInHead obj label → isTrivialChain obj = true` OR handle non-trivialChain obj separately
     b. If obj IS trivialChain: use `normalizeExpr_trivialChain_apply` to get the trivial `t` for obj
     c. Then the normalizeExpr simplifies to `(normalizeExpr val (fun valTriv => k(setProp t prop valTriv))).run n_obj`
     d. Apply IH on val (which has the label)
     e. Lift through setProp context

2. **Check**: Does the theorem hypotheses include something like `NoNestedLabeled` or `ExprWellFormed` that connects ¬HasLabeledInHead to isTrivialChain? Search with `lean_local_search "NoNested"` and `lean_local_search "isTrivialChain"`.

3. **Check**: Look at how `binary_lhs` handles the sub-case at L10170-10203. The `¬HasLabeledInHead lhs label` branch (L10202-10203) is ALSO sorry. This suggests the same lemma is needed for ALL second-position cases plus the first-position ¬HasLabeled sub-cases.

### CONCRETE STEPS:
1. `lean_goal` at L10226 to see exact proof state and available hypotheses
2. `lean_local_search "HasLabeledInHead"` to find all constructors and any negation lemmas
3. `lean_local_search "isTrivialChain"` to find connection lemmas
4. Look for a hypothesis that says the expression is "simple" or "well-formed" in ways that connect to trivialChain
5. If the needed `¬HasLabeledInHead → isTrivialChain` lemma doesn't exist, WRITE IT as a helper theorem
6. Once you have that lemma, the proof pattern is: trivialChain_apply on first sub-expr → IH on second sub-expr → Steps_*_ctx to lift

### ALSO LOOK AT L10203:
The `binary_rhs` ¬HasLabeledInHead sub-case (L10202-10203) is the SAME issue. If you solve the general lemma, it fixes 7+ sorries at once.

## WORKFLOW
1. `lean_goal` at L10226 and L10203 to understand the goals
2. Search for the connection between HasLabeledInHead and isTrivialChain
3. Write helper lemma if needed
4. Apply to each second-position sorry
5. Verify with `lean_diagnostic_messages`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
