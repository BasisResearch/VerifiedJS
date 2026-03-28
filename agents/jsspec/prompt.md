# jsspec — EXPRADDRWF LIST LEMMA + CC STATE THREADING INFRASTRUCTURE

## STATUS: Your verified staging lemmas are good. Now write infrastructure that DIRECTLY enables CC sorry closures.

## PRIORITY 0: ExprAddrListWF infrastructure

The proof agent is about to change `ExprAddrWF` for `.call` and `.newObj` from `True` to recursive. This needs a list version. Write in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_exprAddrWF_helpers.lean`:

```lean
import VerifiedJS.Proofs.ClosureConvertCorrect

namespace VerifiedJS.Proofs

/-- Well-formedness for expression lists. -/
def ExprAddrListWF : List Core.Expr → Nat → Prop
  | [], _ => True
  | e :: es, n => ExprAddrWF e n ∧ ExprAddrListWF es n

theorem ExprAddrListWF_mono {es : List Core.Expr} {n m : Nat} (h : n ≤ m)
    (hwf : ExprAddrListWF es n) : ExprAddrListWF es m := by
  induction es with
  | nil => trivial
  | cons e es ih =>
    obtain ⟨he, hes⟩ := hwf
    exact ⟨ExprAddrWF_mono h he, ih hes⟩

theorem ExprAddrListWF_map_convertExpr (args : List Core.Expr)
    (scope : List String) (envVar : String) (envMap : Flat.EnvMapping)
    (st : Flat.CCState) (n : Nat)
    (hwf : ExprAddrListWF args n) :
    -- property propagates through conversion
    sorry := by sorry
```

**Also write**: monotonicity lemma for ExprAddrWF propagation through Core.step?:
```lean
theorem ExprAddrWF_step_preserved (s : Core.State) (ev : Core.TraceEvent) (s' : Core.State)
    (hstep : Core.step? s = some (ev, s'))
    (hwf : ExprAddrWF s.expr s.heap.objects.size) :
    ExprAddrWF s'.expr s'.heap.objects.size := by
  sorry -- needs per-constructor analysis, but each case is mechanical
```

This is a critical infrastructure lemma needed by ALL CC stepping proofs. Even if you can only prove a few cases (lit, var, unary, binary), each proved case is useful.

## PRIORITY 1: CCStateAgree transitivity

Write in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_ccstate_helpers.lean`:

```lean
theorem CCStateAgree_trans {st1 st2 st3 : Flat.CCState}
    (h12 : CCStateAgree st1 st2) (h23 : CCStateAgree st2 st3) :
    CCStateAgree st1 st3 := by
  exact ⟨h12.1.trans h23.1, h12.2.trans h23.2⟩
```

And a key lemma: if we convert expression `e` from two CCStateAgree states, the output states also CCStateAgree. This is already proved at CC L548 (`convertExpr_state_determined`), but you need to verify it exists and document its exact signature.

## PRIORITY 2: normalizeExpr inversion (if time permits)

For each Flat.Expr constructor, determine what `normalizeExpr` produces. Specifically:
- `normalizeExpr (.lit v) k` always applies `k`
- `normalizeExpr (.let name rhs body) k` uses bindComplex on rhs
- `normalizeExpr (.call f args) k` wraps in bindComplex

Write simple characterization lemmas:
```lean
theorem normalizeExpr_lit (v : Flat.Value) (k : ANF.Trivial → ANF.ConvM ANF.Expr) (n : Nat) :
    (ANF.normalizeExpr (.lit v) k).run n = (k (ANF.trivialOfFlatValue v)).run n := by
  simp [ANF.normalizeExpr]
```

## FILES YOU CAN EDIT
- `.lake/_tmp_fix/VerifiedJS/**/*.lean` (staging area)
- `VerifiedJS/Flat/*.lean`, `VerifiedJS/Core/*.lean`

## DO NOT EDIT
- `VerifiedJS/Proofs/*.lean` (owned by proof)
- `VerifiedJS/Wasm/Semantics.lean` (owned by wasmspec)
- `VerifiedJS/ANF/Semantics.lean` (owned by wasmspec)

## LOG to agents/jsspec/log.md
