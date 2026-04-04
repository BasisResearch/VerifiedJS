# wasmspec — CLOSE THE 3 MUTUAL INDUCTION SORRIES. Your NoNestedAbrupt work is blocked on them.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## BACKGROUND
You wrote excellent NoNestedAbrupt infrastructure last run (12 absurd lemmas, 4 bridge theorem blocks). BUT: the absurd lemmas at ~L4490 ALL depend on `hasThrowInHead_implies_hasAbruptCompletion` which is **sorry'd at L4472**. Your entire framework is built on sorry. Fix this NOW.

## YOUR TASK: Close L4472, L4478, L4484

These are the mutual theorems:
```lean
mutual
theorem hasThrowInHead_implies_hasAbruptCompletion :
    HasThrowInHead e → hasAbruptCompletion e = true := by intro h; sorry

theorem hasThrowInHeadList_implies_hasAbruptCompletionList :
    HasThrowInHeadList es → hasAbruptCompletionList es = true := by intro h; sorry

theorem hasThrowInHeadProps_implies_hasAbruptCompletionProps :
    HasThrowInHeadProps ps → hasAbruptCompletionProps ps = true := by intro h; sorry
end
```

### Why they're sorry'd
Lean 4 broke `induction h with` on these mutually recursive inductives (`HasThrowInHead` references `HasThrowInHeadList` in `call_args`, etc.).

### How to fix: Use the mutual recursor explicitly

The three inductives generate a mutual `.rec` (or `.casesOn`). Use it as a term-mode proof:

```lean
-- All 3 theorems from one recursor application
private def hasThrowInHead_hasAbruptCompletion_aux :
    (∀ e, HasThrowInHead e → hasAbruptCompletion e = true) ×
    (∀ es, HasThrowInHeadList es → hasAbruptCompletionList es = true) ×
    (∀ ps, HasThrowInHeadProps ps → hasAbruptCompletionProps ps = true) := by
  refine ⟨fun e h => ?_, fun es h => ?_, fun ps h => ?_⟩
  all_goals induction h with  -- try this first
  | throw_direct => simp [hasAbruptCompletion]
  | seq_left _ ih => simp [hasAbruptCompletion, ih]
  -- ... etc
```

If `induction h with` fails, try the explicit `.rec`:
```lean
@HasThrowInHead.rec
  (fun e _ => hasAbruptCompletion e = true)       -- motive for Expr
  (fun es _ => hasAbruptCompletionList es = true)  -- motive for List
  (fun ps _ => hasAbruptCompletionProps ps = true) -- motive for Props
  -- One case per HasThrowInHead constructor:
  (by simp [hasAbruptCompletion])                  -- throw_direct
  (fun _ ih => by simp [hasAbruptCompletion]; exact Or.inl ih)  -- seq_left
  (fun _ ih => by simp [hasAbruptCompletion]; exact Or.inr ih)  -- seq_right
  (fun _ ih => by simp [hasAbruptCompletion]; exact Or.inl ih)  -- let_init
  -- ... one per constructor (34 constructors total across all 3)
```

### Steps:
1. `lean_hover_info` on `HasThrowInHead` to check if `.rec` exists and its signature
2. `lean_multi_attempt` to test the approach
3. Write the proof
4. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

### COORDINATE WITH PROOF AGENT
The proof agent is ALSO targeting these 3 sorries. Check `git diff` before editing. If proof agent has changes at L4470-4484, work around them or focus on a DIFFERENT approach (e.g., write a standalone mutual def that the proof agent's sorry can call).

### After closing L4472/4478/4484:
Do the same for the Has{Return,Await,Yield}InHead variants — there should be similar bridge theorems. Check if they also need the same mutual recursor treatment.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
