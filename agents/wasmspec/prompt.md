# wasmspec — Break/continue consolidated to 2 sorries. Now prove normalizeExpr_break_only_via_while.

## Your consolidation work was EXCELLENT. 8 false sorries → 2 honest ones.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## STATE: ANF has 22 sorries. The 2 break/continue compound sorries (L8119, L8170) are yours.

## YOUR TASK: Prove normalizeExpr output only has break/continue via while loops

The 2 remaining sorries (L8119 break compound, L8170 continue compound) are inside `anfConvert_step_star_aux`. They handle the case where `ANF.normalizeExpr sf.expr k` produces `.break label` or `.continue label` and `HasBreakInHead`/`HasContinueInHead` is compound (not direct break/continue).

**Key insight**: If we can prove that normalizeExpr with a trivial-preserving k NEVER produces compound HasBreakInHead (i.e., break only appears directly, not nested inside seq/let/etc.), then these 2 compound cases are UNREACHABLE and can be closed with `exfalso`.

### Step 1: Investigate normalizeExpr output shapes

What forms can `(ANF.normalizeExpr e k).run n` produce that have HasBreakInHead?

Read the normalizeExpr definition. For each case of `e`:
- `.break l`: k is NOT called (break short-circuits), result is `.break l` → HasBreakInHead.break_direct
- `.seq a b`: normalizeExpr produces `normalizeExpr a (fun _ => normalizeExpr b k)` → if `a` has break, does the result have HasBreakInHead?
- `.while_ c b`: normalizeExpr produces a loop structure with break inside

The critical question: does normalizeExpr EVER produce `.seq (.break l) something`? If the ANF normalization short-circuits on break (doesn't wrap it in seq/let), then compound HasBreakInHead is impossible.

### Step 2: Prove the theorem

```lean
private theorem normalizeExpr_break_implies_direct
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (n m : Nat) (label : Option String) (e' : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (e', m))
    (hbreak : HasBreakInHead e' label) :
    ∃ l, e' = .break l := by
  -- Induction on e, showing normalizeExpr never nests break inside compound forms
  sorry
```

If this is provable, add it to ANFConvertCorrect.lean and use it to close L8119:
```lean
    | seq_left _ | seq_right _ | ... =>
      exfalso
      have ⟨l, hl⟩ := normalizeExpr_break_implies_direct sf.expr k hk_triv n m label _ hnorm_simp hbreak_head
      -- hl says e' = .break l, but we matched on a compound HasBreakInHead constructor → contradiction
      sorry -- should be disprovable from hl and the constructor
```

### Step 3: Same for continue

```lean
private theorem normalizeExpr_continue_implies_direct
    (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n', ∃ m', (k t).run n' = .ok (.trivial t, m'))
    (n m : Nat) (label : Option String) (e' : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (e', m))
    (hcont : HasContinueInHead e' label) :
    ∃ l, e' = .continue l := by
  sorry
```

### Alternative: If normalizeExpr CAN produce compound break/continue

If while loops cause normalizeExpr to produce `.seq (.while_ ...) rest` where the while body has break, then compound HasBreakInHead IS reachable. In that case:

1. Read the `normalizeExpr` case for `.while_` carefully
2. Determine EXACTLY what output shape it produces
3. Prove a restricted version: break only appears in while-related positions
4. Use that to construct the correct simulation for those specific compound cases

### Useful commands:
- `lean_hover_info` on `ANF.normalizeExpr` to find its definition file
- `lean_local_search` for "normalizeExpr" to find related lemmas
- `lean_goal` at L8119/L8170 to see proof state

## Build command
`lake build VerifiedJS.Proofs.ANFConvertCorrect`

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
