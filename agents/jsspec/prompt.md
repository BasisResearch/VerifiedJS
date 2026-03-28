# jsspec — NORMALIZEEXPR BREAK INVERSION + CC INFRASTRUCTURE

## STATUS: Your inversion infrastructure in anf_norm_inv.lean is EXCELLENT. Now extend it for the break/continue case proof.

## CRITICAL CONTEXT: ANF break/continue semantics FIXED

wasmspec fixed ANF/Semantics.lean at 17:27. Break/continue/return/throw now produce `.error` events matching Flat. The ANF break/continue sorries (ANFConvertCorrect L1947-1950) are NO LONGER permanent mismatches. But they need normalizeExpr inversion to close.

## PRIORITY 0: normalizeExpr break SOURCE CHARACTERIZATION

The proof agent needs: given `normalizeExpr e k = .ok (.break label, m)` with `k` trivial-preserving, characterize ALL possible shapes of `e`.

**Key insight from your anf_norm_inv.lean**: general inversion is FALSE because `.seq (.lit .undefined) (.break l)` produces `.break l` for any k. So we need a STRUCTURAL characterization.

Write in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_break_inversion.lean`:

```lean
import VerifiedJS.ANF.Convert
import VerifiedJS.Flat.Semantics

namespace VerifiedJS

/-- If normalizeExpr produces .break, the source expression "contains .break" in
    an evaluation-head position. Specifically, either:
    1. e = .break l directly, OR
    2. e = .seq a b where a is a "value" (exprValue? a ≠ none) and
       normalizeExpr b k = .ok (.break l, m') for some m', OR
    3. e = .seq a b where normalizeExpr a produces value via bindComplex,
       and normalizeExpr b k = .ok (.break l, m'), OR
    4. e = .let name init body where normalizeExpr init finishes with value,
       and normalizeExpr body k = .ok (.break l, m')
-/

-- Step 1: For each "leaf" constructor, prove it CAN'T produce .break with trivial-preserving k
-- You already have many of these in anf_norm_inv.lean. Complete the set:

-- Missing from your existing infrastructure (check and fill gaps):
-- normalizeExpr (.getProp e name) k — uses bindComplex, produces .let, not .break
-- normalizeExpr (.setProp obj name val) k — produces .let, not .break
-- normalizeExpr (.binary op l r) k — produces .let, not .break
-- normalizeExpr (.unary op e) k — produces .let, not .break
-- normalizeExpr (.typeof e) k — produces .let, not .break
-- normalizeExpr (.deleteProp e name) k — produces .let, not .break
-- normalizeExpr (.assign name val) k — produces .let or .assign, not .break
-- normalizeExpr (.if cond t e) k — produces .if, not .break
-- normalizeExpr (.while_ cond body) k — produces .seq (.while_ ..), not .break
-- normalizeExpr (.call f args) k — uses bindComplex, produces .let, not .break
-- normalizeExpr (.newObj f args) k — uses bindComplex, produces .let, not .break

-- Step 2: For each "compound" constructor (.seq, .let), prove that .break output
-- implies .break exists in a sub-expression (recursive characterization)

-- Step 3: Write the MASTER inversion lemma (by induction on e.depth or structural):
theorem normalizeExpr_break_source (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n, ∃ m, (k t).run n = .ok (.trivial t, m))
    (label : Option String) (n m : Nat)
    (h : (ANF.normalizeExpr e k).run n = .ok (.break label, m)) :
    -- Flat can step from {expr := e} to {expr := .break label} in zero or more steps
    -- (This is the version the proof agent actually needs)
    ∃ evs sf', Flat.Steps { expr := e, env := default, heap := default, trace := [] } evs sf' ∧
               sf'.expr = .break label := by
  sorry -- prove by structural induction on e
```

This is the KEY MISSING PIECE for -2 ANF sorries. Even a partial version (proving just the `.break l` and `.seq` cases) is extremely valuable.

## PRIORITY 1: Flat multi-step seq-value lemma

The break inversion needs: if `e = .seq (.lit v) body`, then Flat steps to `{expr := body}` in one step. Write:

```lean
theorem Flat.steps_seq_value (s : Flat.State) (v : Flat.Value) (body : Flat.Expr) :
    Flat.step? { s with expr := .seq (.lit v) body } =
      some (.silent, Flat.pushTrace { s with expr := body } .silent) := by
  simp [Flat.step?, Flat.exprValue?]
```

## PRIORITY 2: Complete "leaf not-break" lemmas

For the master inversion, you need: `normalizeExpr (.X ...) k` with trivial-preserving k NEVER produces `.break` for each non-break, non-seq, non-let constructor. You have many already. Complete the missing ones listed above.

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`

## DO NOT EDIT
- `VerifiedJS/Proofs/*.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Semantics.lean` (owned by wasmspec)

## LOG to agents/jsspec/log.md
