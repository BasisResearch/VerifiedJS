# jsspec — ANF SimRel REDESIGN PREP + CC staging

## STATUS: normalizeExpr_not_labeled_family has sorry cases (needs noLabeledAnywhere predicate). Continuation no-confusion lemmas done.

## KEY DISCOVERY: normalizeExpr_not_labeled_family needs recursive predicate

Your analysis in `anf_not_labeled.lean` is correct: the top-level `h_not_labeled` is insufficient for recursive cases. `.labeled` propagates through sub-expressions.

## PRIORITY 0: Write `Flat.Expr.noLabeledAnywhere` predicate

Write in `.lake/_tmp_fix/VerifiedJS/Flat/ExprNoLabeled.lean`:

```lean
import VerifiedJS.Flat.Syntax

namespace VerifiedJS.Flat

/-- No .labeled constructor anywhere in the expression tree -/
def Expr.noLabeledAnywhere : Expr → Prop
  | .lit _ => True
  | .var _ => True
  | .this => True
  | .«break» _ => True
  | .«continue» _ => True
  | .«return» none => True
  | .«return» (some e) => e.noLabeledAnywhere
  | .yield (some e) _ => e.noLabeledAnywhere
  | .yield none _ => True
  | .throw e => e.noLabeledAnywhere
  | .await e => e.noLabeledAnywhere
  | .seq a b => a.noLabeledAnywhere ∧ b.noLabeledAnywhere
  | .«let» _ init body => init.noLabeledAnywhere ∧ body.noLabeledAnywhere
  | .«if» c t e => c.noLabeledAnywhere ∧ t.noLabeledAnywhere ∧ e.noLabeledAnywhere
  | .labeled _ _ => False
  | .while_ c b => c.noLabeledAnywhere ∧ b.noLabeledAnywhere
  | .tryCatch b _ cb f => b.noLabeledAnywhere ∧ cb.noLabeledAnywhere ∧ match f with | none => True | some fe => fe.noLabeledAnywhere
  -- Add all other constructors (assign, unary, binary, call, getProp, setProp, etc.)
  | _ => True  -- placeholder; expand for completeness
```

Then prove: `theorem noLabeledAnywhere_sub : e.noLabeledAnywhere → (sub-expressions of e).noLabeledAnywhere` for each constructor.

## PRIORITY 1: Complete normalizeExpr_not_labeled_family with noLabeledAnywhere

Update the hypothesis in `anf_not_labeled.lean` from `(∀ l b, e ≠ .labeled l b)` to `e.noLabeledAnywhere`. Then:

For `return (some value)` (L135-139): Since `(.return (some value)).noLabeledAnywhere → value.noLabeledAnywhere`, apply IH on value (depth decreases). The inner continuation `fun t => pure (.return (some t))` doesn't produce `.labeled` (noConfusion). ✓

For `throw arg` (L148-151): Same pattern. `(.throw arg).noLabeledAnywhere → arg.noLabeledAnywhere`. Apply IH. ✓

For compound cases (assign, seq, let, if): Use noLabeledAnywhere to get sub-expression hypotheses, then apply IH. The bindComplex-based continuations don't produce `.labeled` (use `bindComplex_not_labeled`). ✓

## PRIORITY 2: Prove initial expression has noLabeledAnywhere

For the ANF SimRel redesign to work, we need: the initial Flat program's main expression has `noLabeledAnywhere`. This is likely TRUE because `.labeled` is only introduced by while_ lowering (which happens at runtime, not in the source). Check:
1. Does `Flat.Expr` include `.labeled` in the initial program? Or is it only created by step?
2. If `.labeled` only comes from while_ lowering in step?, prove `initialState.expr.noLabeledAnywhere`.

Write this in `.lake/_tmp_fix/VerifiedJS/Flat/ExprNoLabeled.lean`.

## PRIORITY 3: CC staging maintenance

Check if proof agent needs any NEW staging proofs. The CC cases that are being attempted:
- objectLit/arrayLit: staging exists
- call: check `.lake/_tmp_fix/VerifiedJS/Proofs/cc_call_patches.lean`
- functionDef: may need staging
- captured var (L1828): may need EnvCorrInj lemma

If any of these need helper lemmas, write them in staging.

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`
- `VerifiedJS/ANF/Convert.lean` (helper lemmas only)

## DO NOT EDIT
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)

## Log to agents/jsspec/log.md
