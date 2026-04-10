# wasmspec — CLOSE MORE LABELED_BRANCH + CAT B BREAK/CONTINUE

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- BUILD PASSES. LSP available.
- You closed 3 sorries last run (L9865, L10220, L10550). Good work.
- Error propagation is now COMPLETE in Flat/Semantics.lean (48 `.error _` patterns). This unblocks Cat B break/continue cases.
- ANF: 44 sorries. CC: 15. Total: 59.

## P0: CAT B BREAK/CONTINUE — NOW UNBLOCKED

Error propagation is done. The Cat B cases (L15376, L15447) that were blocked should now be closable. These are compound HasBreakInHead/HasContinueInHead cases where Flat.step? now propagates errors through compound wrappers.

### Pattern for Cat B cases:
With error propagation, when a break/continue fires inside a compound expr:
1. Flat.step? matches `t` on `.error _` branch
2. Returns `s'.expr = sa.expr` (unwrapped), not wrapped in the compound
3. This should match the ANF simulation since normalizeExpr produces the abrupt completion directly

### APPROACH
1. Read L15370-15460 to see current Cat B sorry state
2. Use `lean_goal` at L15376 and L15447 to check exact goals
3. Try `lean_multi_attempt` with: `["unfold Flat.step? at *; simp_all", "simp [Flat.step?, Flat.pushTrace]", "sorry"]`
4. If the goal needs the error propagation match, use:
```lean
match t with
| .error _ => <use sa.expr = unwrapped>
| _ => <contradiction with NoNestedAbrupt>
```

## P1: REMAINING LABELED_BRANCH CLOSABLE CASES (L10333-L10706)

Last run you categorized remaining sorries. Focus on type (a) — simple tactic failures:

### Closable targets:
1. **L10383, L10431, L10481** (binary_lhs/rhs, unary): These follow the same pattern as the ones you already closed. Use the template from L10550 (newObj_func proof).

2. **L10508, L10558** (call_func, call_env): Should follow same IH + Steps_*_ctx_b lifting pattern.

3. **L10333** (trivialChain passthrough): This is the hardest. Read context — if it needs a value-trivia correspondence lemma, document what's needed and skip.

### For each:
1. `lean_goal` to see exact goal
2. Check if IH + lifting lemma closes it
3. If it needs a new lifting lemma (like Steps_*_ctx_b), check if one exists with `lean_local_search`

## P2: DEPTH/RETURN/YIELD COMPOUND (L10911-L11091)

6 sorries in normalizeExpr_labeled_branch_step for compound return/yield expressions inside labeled branches. These may need depth induction — assess whether the error propagation changes help here.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — Cat B + labeled_branch" >> agents/wasmspec/log.md`
2. Try Cat B break/continue first (P0) — highest value if closable
3. Then labeled_branch simple cases (P1)
4. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
