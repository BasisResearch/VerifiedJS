# wasmspec — Continue proving normalizeExpr_break_implies_direct to close L8119/L8170

## Your consolidation work was EXCELLENT. 8 false sorries → 2 honest ones.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## STATE: ANF has 22 sorries. The 2 break/continue compound sorries (L8119, L8170) are yours.

## YOUR TASK: Prove normalizeExpr_break_implies_direct (and continue variant)

### What you need to prove

If `normalizeExpr e k` produces an expression with `HasBreakInHead`, and `k` is trivial-preserving, then the result must be a direct `.break l` (not a compound like `.seq (.break l) b`).

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

### Proof strategy

Induction on `e.depth` (or `e` directly), mirroring `no_throw_head_implies_trivial_chain` (L6776).

For each case of `e`:
- **Trivial (lit/var/this)**: `normalizeExpr` calls `k t`, and `hk` says result is `.trivial t`. But `HasBreakInHead (.trivial t)` is impossible (no constructor matches). Contradiction.
- **break l**: `normalizeExpr (.break l) k` = `pure (.break l)`. So `e' = .break l`. QED.
- **continue l**: `normalizeExpr (.continue l) k` = `pure (.continue l)`. HasBreakInHead for `.continue l` is impossible. Contradiction.
- **return/throw/yield/await**: These short-circuit (ignore k). The result is `.return`/`.throw`/`.yield`/`.await arg`. HasBreakInHead for these can only come from the arg having HasBreakInHead... recurse via IH.
- **Compound (seq, let, assign, etc.)**: These use `bindComplex`. Need to show `bindComplex` preserves the property. Key: `bindComplex` calls `normalizeExpr sub_expr (fun t => normalizeExpr rest_with_t k)`. If the result has HasBreakInHead, then either the sub_expr or the continuation produced it. Recurse via IH.
- **while_**: Special — while_ DOES produce break-containing expressions. But with trivial-preserving k, does the output have compound HasBreakInHead? Check the actual `normalizeExpr` case for `.while_`.

### Key question: Does normalizeExpr for `.while_` produce compound HasBreakInHead?

Read the `normalizeExpr` case for `.while_ cond body`. If it produces something like:
```
.seq (.while_ normalizedCond normalizedBody) (k trivialResult)
```
then `.while_` might have break inside, giving `seq_right` HasBreakInHead... but `k trivialResult` produces `.trivial t` (by hk), which can't have HasBreakInHead. And `seq_left` would need HasBreakInHead in the while_ itself, which needs HasBreakInHead in the while_ body — this is possible!

So `.while_ cond (.seq (.break l) rest)` normalized might produce compound HasBreakInHead. If so, the theorem is FALSE and you need a different approach:

### Alternative if theorem is FALSE

If normalizeExpr CAN produce compound HasBreakInHead (via while_ bodies):
1. Prove a RESTRICTED version: normalizeExpr_break_implies_direct_or_while — result is either `.break l` or contains break only inside a while_-related position
2. Show that the compound while_ case at L8119 can be handled by showing the while_ body simulation works

### Useful tools
- `lean_hover_info` on `ANF.normalizeExpr` at the `.while_` case to see the output shape
- `lean_local_search` for "normalizeExpr" and "while"
- `lean_goal` at L8119 to see proof state
- `lean_multi_attempt` to test tactics

## Build command
`lake build VerifiedJS.Proofs.ANFConvertCorrect`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
