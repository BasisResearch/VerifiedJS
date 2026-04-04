# wasmspec — Fix hasBreakInHead/hasContinueInHead theorems + if_step_sim approach

## EXCELLENT analysis on break error propagation. Your finding that hasBreakInHead_flat_error_steps is NOT PROVABLE was critical.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec is implementing CCStateAgree fix
- **DO NOT** run `lake build` anything
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean for investigation 1 (but coordinate with proof agent — only edit L6600-6625 and call sites L7757-7900)

## YOUR JOB: Two investigations

### Investigation 1: Fix hasBreakInHead/hasContinueInHead (CRITICAL — 2 sorries + downstream)

The theorems at L6600-6625 are NOT PROVABLE as stated. But the call sites at L7757+ NEED them.

**Key insight**: `normalizeExpr_seq_while_first_family` proved that if normalizeExpr produces `.seq a b`, then `a = .while_ c d`. This means normalizeExpr NEVER produces `.seq (.break label) b`. Similarly for `.let`, `.if`, etc. — normalizeExpr CPS-transforms everything, so compound HasBreakInHead constructors (seq_left, seq_right, let_init, etc.) are UNREACHABLE for ANF-normalized expressions.

**Your task**: Verify this by checking:
1. Read HasBreakInHead definition (grep for `inductive HasBreakInHead`)
2. For each compound constructor of HasBreakInHead, determine if normalizeExpr can produce that form
3. If confirmed unreachable: the FIX is to add a lemma:
```lean
private theorem normalizeExpr_no_compound_break
    (e : Flat.Expr) (label : Option Flat.LabelName)
    (h : HasBreakInHead e label)
    (hnorm : ∃ orig k n, e = (ANF.normalizeExpr orig k n).fst) :
    h = .break_direct := by
  -- cases on h; for break_direct: rfl
  -- for each compound case: derive contradiction from hnorm
  sorry
```
Then hasBreakInHead_flat_error_steps only needs to handle break_direct (already provable).
And call sites for compound cases use `absurd` with normalizeExpr_no_compound_break.

4. Read the call sites at L7757-7900 to understand exactly how to restructure
5. Write your analysis and proposed code changes to `agents/wasmspec/break_fix_plan.md`

### Investigation 2: if_step_sim approach (L7336, L7367, L7370)

The proof agent found that characterizing normalizeExpr output as `.if` is harder than expected (not just from `.if` source — `.seq`, `.let` can propagate `.if`).

Tasks:
1. Read around L7330-7370 to see current proof state
2. What does if_step_sim actually need to prove? Use `lean_goal` at L7336
3. Can it be proved by strong induction on expression depth without full characterization?
4. Write findings to `agents/wasmspec/if_step_sim_plan.md`

### LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
