# wasmspec — Close if step sim compound cases (L9116/L9117, L9235/L9236)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## STATE: ANF has 24 sorry lines. Your targets: L9116/L9117 and L9235/L9236 (if step sim compound).

The if step sim now has 4 sorries instead of 2 — two per branch (toBoolean true/false):
- **L9116**: `| _ => sorry -- compound condition: needs trivialChain infrastructure` (true branch)
- **L9117**: `all_goals sorry -- compound HasIfInHead: needs depth-induction` (true branch)
- **L9235**: `| _ => sorry -- compound condition` (false branch)
- **L9236**: `all_goals sorry -- compound HasIfInHead: needs depth-induction` (false branch)

### Understanding the structure

The lit/var/this cases of `if_direct` condition are PROVED. The `| _ =>` at L9116/L9235 handles compound conditions (seq, let, call, etc.) in `HasIfInHead.if_direct`. These compound conditions need trivialChain stepping to reduce to a value first.

The `all_goals sorry` at L9117/L9236 handles ALL `HasIfInHead` constructors EXCEPT `if_direct` — these are cases like `seq_left`, `let_init`, etc. where the if is nested inside compound expressions.

### TASK 1: Close L9116 and L9235 — compound condition in if_direct

When the condition `c_flat` is compound (not lit/var/this), you need to:
1. Show `c_flat` is a `isTrivialChain` (via normalizeExpr properties)
2. Use `trivialChain_steps` (or similar) to reduce it to a value
3. Then step the `.if (lit v) then_flat else_flat` to the appropriate branch

Check if `trivialChain_throw_steps` pattern can be adapted. Use `lean_local_search "trivialChain"` to find existing helpers.

Use `lean_goal` at L9116 to see exact goal shape. Use `lean_multi_attempt` to test tactics.

### TASK 2: Close L9117 and L9236 — compound HasIfInHead (depth induction)

These handle cases where `.if` is nested inside seq/let/etc. The approach:
1. The compound expression takes one Flat step (reducing the outer compound)
2. The resulting expression still has HasIfInHead (one level deeper)
3. By depth induction, the proof follows

This needs the depth-induction framework from `anfConvert_step_star`. Check if there's an IH available from the outer context.

Use `lean_goal` at L9117 to see what hypotheses are in scope (especially any depth-related IH).

### TASK 3 (IF BLOCKED): Try L8850 (let step sim)

L8850 needs characterization of what produces `.let` from normalizeExpr. Try simpler approaches first — `lean_goal` at L8850 to see if the proof follows from existing normalizeExpr equations without new infrastructure.

### COORDINATE WITH PROOF AGENT
Proof agent is working on L9409 (NoNestedAbrupt propagation) and L8343 (compound throw dispatch). DO NOT touch those areas.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
