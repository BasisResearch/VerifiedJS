# proof — Close hasBreakInHead/hasContinueInHead, then non-labeled inner value sorries

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` entirely.

## STATE: ANF has 22 sorries, ALL in L6400-7410 (step simulation cases).
normalizeExpr_if_cond_source is DONE ✓ (L2025-2468).

## YOUR IMMEDIATE TASKS (in order):

### TASK 1: hasBreakInHead_flat_error_steps (L6608) — HIGH PRIORITY
This theorem says: if `HasBreakInHead e label`, then `e` flat-steps to `.lit .undefined` with break error trace.

⚠️ KEY DIFFICULTY: Error propagation through eval contexts does NOT immediately produce `.lit .undefined` for compound expressions. When `.break label` is inside `.seq (.break label) b`, the Flat.step? on `.seq` produces `.seq (.lit .undefined) b` with the error event, NOT `.lit .undefined` directly. Then `.seq (.lit .undefined) b` steps silently to `b`.

APPROACH — You need multi-step reasoning:
- Base case `break_direct`: `Flat.step?_break_eq` (L3539) gives single step to `.lit .undefined`. Done.
- For eval context cases (seq_left, let_init, etc.):
  1. Use `step?_seq_error` (L1616), `step?_let_init_error` (L1628), etc. to propagate the error through the context
  2. After error step, you have e.g. `.seq (.lit .undefined) b` — still need to step to `.lit .undefined`
  3. This means you may need additional stepping after error propagation
  4. CHECK: does the theorem even hold for `seq_right`? If `HasBreakInHead b label` for `.seq a b`, you'd need to first evaluate `a` to a value, THEN step `b`. But `a` might not terminate!

FIRST: Use `lean_goal` at L6608 to see exact proof state. Then try `lean_multi_attempt` with:
```
["induction h", "cases h"]
```
to see what constructor cases appear. Verify the base case works before tackling compound cases.

Existing eval context error lemmas:
- `step?_seq_error` (L1616): `.seq a b` error propagation
- `step?_let_init_error` (L1628): `.let` error propagation
- `step?_unary_error` (L1640): `.unary` error propagation
- `step?_seq_ctx` (L1452): `.seq a b` non-error context stepping

IF this theorem is harder than expected, SKIP to Task 2.

### TASK 2: "non-labeled inner value" sorries (L6401, L6434, L6530, L6563)
These are `| _ => sorry` catch-all cases after `.labeled` is handled.
The remaining constructors after labeled are: `.var`, `.lit`, `.this`, `.seq`, `.let`, `.assign`, `.if`, `.call`, `.binary`, `.unary`, `.typeof`, `.getProp`, `.setProp`, `.getIndex`, `.setIndex`, `.deleteProp`, `.return`, `.yield`, `.while_`, `.tryCatch`, `.break`, `.continue`, `.throw`, `.await`, etc.

Use `lean_goal` at each sorry to see what constructors remain. Many might be closable by:
- `contradiction` (if the outer normalizeExpr output can't come from these)
- `exfalso` + simp reasoning
- Direct cases on the remaining constructors

### TASK 3: hasContinueInHead_flat_error_steps (L6621) — SAME PATTERN as Task 1

### SKIP THESE:
- L7284 (.let characterization) — bindComplex PRODUCES .let, approach wrong
- L6774-7257 (compound flat_arg/inner_val) — need depth induction, deprioritize
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
