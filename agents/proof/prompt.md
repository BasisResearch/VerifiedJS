# proof — Close the 7 step_sim theorems. They are the critical path.

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE
- ANF: 18 sorries. LowerCorrect: 0 ✓ DONE. CC: 21 — OTHER AGENTS OWN IT.
- The 6 tactics from the previous prompt are CONFIRMED TO FAIL. Do NOT attempt them.

## ANF SORRY BREAKDOWN (18 total)

### GROUP A: step_sim theorems (7 sorries, L4140-L4279) — YOUR TOP PRIORITY
These are standalone theorems. Each needs case analysis on `sf.expr` to find which Flat expression normalizeExpr produces the given ANF form, then construct the Flat step sequence.

| Line | Theorem | Strategy |
|------|---------|----------|
| L4140 | `normalizeExpr_return_step_sim` | Case-split `sf.expr`. For each case, unfold `normalizeExpr`, match against `hnorm` to determine which expressions can produce `.return`. Then use `Flat.step?` to construct steps. |
| L4164 | `normalizeExpr_await_step_sim` | Same pattern. `.await arg` only comes from `Flat.Expr.await`. |
| L4195 | `normalizeExpr_yield_step_sim` | Same pattern. `.yield` only from `Flat.Expr.yield`. |
| L4216 | `normalizeExpr_let_step_sim` | `.let` comes from compound expressions via `bindComplex`. The ANF step on `.let` evaluates `rhs` — mirror in Flat. |
| L4237 | `normalizeExpr_seq_step_sim` | `.seq` comes from `Flat.Expr.seq` or while expansion. ANF `.seq a b` steps to `a` (discarding b until a is value). |
| L4258 | `normalizeExpr_if_step_sim` | `.if` — ANF evaluates cond trivial, picks branch. Flat does same. |
| L4279 | `normalizeExpr_tryCatch_step_sim` | `.tryCatch` — wraps body execution. |

**Approach for each**:
1. `lean_goal` at the sorry line to see full proof state
2. Cases on `sf.expr` (the Flat source expression)
3. For each case, `unfold ANF.normalizeExpr at hnorm` then `simp` to derive contradiction or extract the mapping
4. For the valid case(s), construct `Flat.Steps` using `Flat.step?` lemmas
5. Use `lean_multi_attempt` to test candidate tactics
6. Start with the SIMPLEST theorem first (try `normalizeExpr_await_step_sim` — `.await` likely has a direct correspondence)

### GROUP B: normalizeExpr_labeled_step_sim depth-recursive (7 sorries, L3825-3923) — DEFER
These are the nested induction cases. The correct approach requires an **evaluation context lifting lemma** (you identified this in your log). This is ~100-200 lines of new code. Work on GROUP A first.

### GROUP C: hasBreakInHead/hasContinueInHead (2 sorries, L3940/3953) — DEFER
Your analysis says the `seq_right` inductive cases make these unprovable for non-terminating first args. Consider restricting the inductive or adding a guard. Low priority.

### GROUP D: throw compound (2 sorries, L4106/4109) — DEFER
Same evaluation-context issue as GROUP B.

## WORKFLOW
1. `grep -n "sorry" VerifiedJS/Proofs/ANFConvertCorrect.lean` to confirm line numbers
2. Pick one step_sim theorem from GROUP A (start with await or return)
3. `lean_goal` at the sorry
4. Work through the proof with case analysis + `lean_multi_attempt`
5. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
6. Move to the next theorem
7. Log to agents/proof/log.md after each closed sorry

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — jsspec and wasmspec are editing it
- LowerCorrect.lean — DONE (0 sorries)
