# jsspec — WRITE NEW INDUCTION-BASED LEMMA FOR COMPOUND CASES

## STATUS: Good work on staging lemmas. Convert.lean permission issue resolved — proof agent will integrate your lemmas.

## CURRENT SORRY COUNT: ANF=13, CC=18, Wasm=20, Lower=1 → 52 total

## CRITICAL FINDING YOU MADE LAST RUN (CORRECT):
Compound cases (let, seq, if) CAN produce `.labeled` if a sub-expression is `.labeled`.
The proof needs **well-founded induction on Flat.Expr.depth**, not simple exfalso.

## PRIORITY 0: Write normalizeExpr_depth_not_labeled induction lemma

Write a new lemma into `.lake/_tmp_fix/VerifiedJS/ANF/ConvertHelpers.lean` that proves:

```lean
/-- For any expression e that is NOT .labeled, if k always produces trivial,
    then normalizeExpr e k never produces .labeled.
    Proved by well-founded induction on e.depth. -/
theorem normalizeExpr_not_labeled_of_not_labeled
    (e : Flat.Expr) (he : ∀ l b, e ≠ .labeled l b)
    (k : Trivial → ConvM Expr)
    (hk : ∀ (arg : Trivial) (n' : Nat), ∃ m', (k arg).run n' = .ok (.trivial arg, m'))
    (n : Nat) (label : String) (body : Expr) (m : Nat) :
    (normalizeExpr e k).run n ≠ .ok (.labeled label body, m) := by
  -- Well-founded induction on e.depth (or sizeOf)
  induction e using ... with
  | ... => ...
```

This single lemma would close L1563, L1595, and L1612 ALL AT ONCE.

**Approach for compound cases in the induction:**
- For `let n r b`: normalizeExpr unfolds to `bindComplex (evalComplex r) (fun fresh => normalizeExpr b' k')`.
  - bindComplex always produces `.let` → contradiction (use `bindComplex_not_labeled`)
  - Wait — actually bindComplex produces `.let fresh (normalizeExpr sub k')`. So the RESULT is always `.let`, never `.labeled`. So bindComplex_not_labeled handles it.
- For `seq a b`: normalizeExpr unfolds to `normalizeExpr a (fun _ => normalizeExpr b k)`.
  - The outer result comes from normalizeExpr on `a` with a new continuation.
  - Need to show the new continuation preserves the "produces trivial" property... but it doesn't! `fun _ => normalizeExpr b k` might not produce trivial.

**KEY INSIGHT**: The continuation `fun _ => normalizeExpr b k` does NOT produce trivial — it produces whatever normalizeExpr b k produces. So the simple "k produces trivial" approach FAILS for seq/if/let.

**REVISED APPROACH**: The lemma needs a WEAKER precondition. Instead of "k produces trivial", prove:
```lean
theorem normalizeExpr_not_labeled_of_not_labeled
    (e : Flat.Expr) (he : ∀ l b, e ≠ .labeled l b)
    (k : Trivial → ConvM Expr)
    (hk : ∀ (arg : Trivial) (n' : Nat) (label : String) (body : Expr) (m' : Nat),
      (k arg).run n' ≠ .ok (.labeled label body, m'))
    (n : Nat) (label : String) (body : Expr) (m : Nat) :
    (normalizeExpr e k).run n ≠ .ok (.labeled label body, m)
```

Where `hk` says "k never produces labeled" (weaker than "k produces trivial").

Then the induction works:
- Trivial k that produces trivial → trivial is not labeled → satisfies hk
- `fun _ => normalizeExpr b k` → by IH on b (smaller depth), normalizeExpr b k doesn't produce labeled (if b isn't labeled)...

Wait, but b COULD be labeled! The issue is: in `seq a b`, b might be `.labeled l body`. In that case normalizeExpr b k DOES produce `.labeled`.

**ACTUAL CORRECT APPROACH**: Use induction to show that the ONLY way normalizeExpr produces `.labeled` is if there exists a sub-expression that IS `.labeled`. Then in the caller (normalizeExpr_labeled_step_sim), we know the expression structure.

Actually, maybe simpler: the helper sorries L1563/L1595 are specifically about `return (some val)` and `yield (some val) delegate` where `val` is NOT `.labeled` (the `| _ =>` branch). So we need: "if val is not .labeled, then normalizeExpr val k (with k producing trivial) doesn't produce .labeled." This is FALSE for compound val containing labeled sub-expressions!

**CORRECT FIX**: L1563 and L1595 match on `| _ =>` meaning all val constructors EXCEPT `.labeled`. For TRIVIAL constructors (var, lit, this), it's immediate. For compound constructors, val could contain a nested `.labeled` — so it's genuinely hard.

Write up your analysis of WHY this is hard and what approaches could work, in ConvertHelpers.lean as a comment block. Then focus on:

## PRIORITY 1: Prove the EASY cases in L1563/L1595

Even if you can't handle all cases, expand `| _ => sorry` into individual constructor cases and prove the easy ones:
```lean
| var name => exfalso; ... (normalizeExpr_var_not_labeled + hk_triv)
| this => exfalso; ...
| lit _ => exfalso; ...
| «break» _ => exfalso; (normalizeExpr_break_not_labeled')
| «continue» _ => exfalso; (normalizeExpr_continue_not_labeled')
| while_ _ _ => exfalso; (already proved pattern at L1596-1600)
| tryCatch _ _ _ _ => exfalso; (already proved pattern at L1601-1611)
| call _ _ => exfalso; (bindComplex_not_labeled pattern)
| ... other bindComplex cases ...
| «return» none => exfalso; (normalizeExpr_return_none_not_labeled)
| yield none _ => exfalso; (normalizeExpr_yield_none_not_labeled)
```

Then leave the compound recursive cases (let, seq, if, return some, yield some) as individual sorries.

**Write these as a template in ConvertHelpers.lean** so proof agent can copy-paste into ANFConvertCorrect.lean.

## PRIORITY 2: Write more continuation no-confusion lemmas if needed

Check what other staging lemmas the proof agent might need.

## DO NOT edit: ANFConvertCorrect.lean, ClosureConvertCorrect.lean, EmitCorrect.lean, EndToEnd.lean, LowerCorrect.lean
## YOU CAN edit: .lake/_tmp_fix/**, VerifiedJS/Core/*, VerifiedJS/Flat/Semantics.lean
## Log to agents/jsspec/log.md
