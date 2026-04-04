# wasmspec — Close Group G sorries at L8165/L8217 in ANFConvertCorrect.lean

## Your consolidation work was EXCELLENT. 8 false sorries → 2 honest ones.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## STATE: ANF has 22 sorries. The 2 break/continue compound sorries at L8165 and L8217 are yours.

## LINE NUMBERS UPDATED (shifted since last run):
- L8165: hasBreakInHead_flat_error_steps compound case
- L8217: hasContinueInHead_flat_error_steps compound case

## YOUR TASK: Close L8165 and L8217

### Strategy A: Prove normalizeExpr_break_implies_direct

If `normalizeExpr e k` with trivial-preserving `k` produces HasBreakInHead, then result is `.break l` (direct, not compound). If TRUE, L8165 closes via exfalso (compound case is impossible).

```lean
private theorem normalizeExpr_break_implies_direct
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (n m : Nat) (label : Option String) (e' : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (e', m))
    (hbreak : HasBreakInHead e' label) :
    ∃ l, e' = .break l := by
  sorry
```

Proof by induction on `e`:
- **Trivial (lit/var/this)**: `k t` gives `.trivial t`, no HasBreakInHead → contradiction
- **break l**: result is `.break l`, QED
- **continue l**: no HasBreakInHead → contradiction
- **return/throw/yield/await**: short-circuit, recurse via IH on arg
- **Compound (seq, let, etc.)**: `bindComplex` → recurse via IH
- **while_**: CRITICAL — check actual `normalizeExpr` case for `.while_`. If it produces compound HasBreakInHead, this theorem is FALSE.

### If Strategy A fails (while_ produces compound break):

**Strategy B**: Prove the compound case directly. At L8165 you have:
- `HasBreakInHead expr label` with compound constructor (seq_left, seq_right, let_init, etc.)
- Need to show Flat.Steps from the state to an error state

Use `lean_goal` at L8165 to see exact proof state. Then:
1. Case split on which HasBreakInHead constructor
2. For each compound constructor, show the sub-expression with break eventually produces `.break l`
3. The `.break l` then causes `flat_error` (break outside loop = error)

### WORKFLOW:
1. `lean_hover_info` on `ANF.normalizeExpr` at the `.while_` case to check output shape
2. If while_ output doesn't produce compound HasBreakInHead → prove Strategy A
3. If it does → pivot to Strategy B, use `lean_goal` at L8165
4. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## Regarding your hnoerr patch
Your hnoerr guards patch at `.claude-wasmspec/backups/hnoerr_guards.patch` is noted. The CC file permissions issue is known. Focus on Group G (ANF) sorries instead — those you CAN edit.

## Build command
`lake build VerifiedJS.Proofs.ANFConvertCorrect`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
