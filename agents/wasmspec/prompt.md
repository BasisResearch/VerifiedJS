# wasmspec — Close normalizeExpr_if_branch_step sorries, then tackle compound eval context

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.4GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead. Wait 60s then check again.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L11200-11360 (tryCatch) and L12400-12717 (break/continue/return)
- **YOU** own L8000-10912 (normalizeExpr step sim infrastructure)
- DO NOT touch lines outside your range

## GREAT PROGRESS LAST RUN! 4 lemmas proved:
- `trivialChain_eval_value` (proved)
- `no_if_head_implies_trivial_chain` (proved)
- `trivialChain_if_true_sim` (proved)
- `trivialChain_if_false_sim` (proved)
- Seq ¬HasIfInHead closed in both branches

## CURRENT STATE: Your zone has 28 sorries (decomposed from 8). This is fine — they're narrower and more tractable.

### IMMEDIATE TARGETS — normalizeExpr_if_branch_step (L10563-10643, 12 sorries)

These were created by YOUR decomposition. Close them using YOUR proven infrastructure:

**L10563, L10591, L10619** (3 sorries): `hpres for ws` — State preservation through lifted steps.
These should follow from `trivialChain_eval_value` which proves env/heap/funcs/cs preservation.
Try: `lean_multi_attempt` with `["exact trivialChain_eval_value ...", "simp [trivialChain_eval_value]"]`

**L10571** (1 sorry): trivialChain evaluation → value → branch `.if` → then_flat.
This IS what `trivialChain_if_true_sim` proves! Wire it in directly.

**L10621** (1 sorry): ExprWellFormed for ws.expr = .seq sf_a.expr b.
Should follow from ExprWellFormed composition.

**L10625** (1 sorry): ¬HasIfInHead a → trivialChain eval → IH on b; or HasIfInHead a → IH on a.
This is the core recursion. Use strong induction on depth + your proven infrastructure.

**L10629-10642** (5 sorries): IH on init/arg/v with different K (let/throw/return/await/yield).
These all follow the same pattern — apply IH through the appropriate `Steps_*_ctx` lemma.

**L10643** (1 sorry): remaining exotic cases (binary, unary, getProp, etc.).
Case split — most should be contradictions (no HasIfInHead for these).

### THEN: L10682 — normalizeExpr_if_branch_step_false (symmetric)
```lean
sorry -- TODO: symmetric to normalizeExpr_if_branch_step
```
Once normalizeExpr_if_branch_step is done, copy it with `true_sim` → `false_sim` substitutions.

### THEN: L10787-10799 and L10901-10912 (8 sorries)
These are "UNLOCK" sorries that depend on normalizeExpr_if_branch_step being proved. Once Step 1 lands, try:
```lean
lean_multi_attempt at L10787 column 7
["exact normalizeExpr_if_branch_step ...", "apply normalizeExpr_if_branch_step"]
```

### USE lean_multi_attempt AGGRESSIVELY
Before editing, test tactics at each sorry. This avoids rebuilds.

## PRIORITY ORDER
1. L10563/10591/10619 (hpres — should be easy with trivialChain_eval_value)
2. L10571 (wire in trivialChain_if_true_sim)
3. L10621 (ExprWellFormed)
4. L10625 (core recursion with IH)
5. L10629-10643 (IH applications + exotic contradictions)
6. L10682 (symmetric false case)
7. L10787-10912 (UNLOCK sorries)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
