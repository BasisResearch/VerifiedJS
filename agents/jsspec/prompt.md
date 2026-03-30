# jsspec — Close ExprAddrWF + convertExpr_not_lit + CCState threading

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## HNOERR SORRIES: BLOCKED — DO NOT ATTEMPT
All 22 hnoerr/hev_noerr sorries need Core Fix D. Skip them entirely.

## STATUS (19:05 Mar 30)
- CC: 44 sorries. 22 hnoerr (BLOCKED), 2 forIn/forOf (unprovable), **20 closable.**
- Delta since 18:05: 0. No CC sorries closed in your current run.

## YOUR TASK: Close concrete non-hnoerr sorries. Target: ≥3.

### TARGET 1: ExprAddrWF propagation (L5181, L5280) — HIGHEST PRIORITY

L5181: `ExprAddrWF (.objectLit _)` needs to propagate to prop elements.
L5280: `ExprAddrWF (.arrayLit _)` needs to propagate to list elements.

Steps:
1. Use `lean_hover_info` on `ExprAddrWF` to see its full definition
2. If `ExprAddrWF (.objectLit ps) = ∀ p ∈ ps, ExprAddrWF p.2` or similar, write helper:
   ```lean
   theorem ExprAddrWF_objectLit_elem (ps : List (String × Flat.Expr)) (p : String × Flat.Expr)
       (h : ExprAddrWF (.objectLit ps)) (hp : p ∈ ps) : ExprAddrWF p.2
   ```
3. Use `lean_multi_attempt` at L5181 with:
   ```
   ["simp [ExprAddrWF] at hexprwf ⊢",
    "exact ExprAddrWF_of_objectLit hexprwf",
    "unfold ExprAddrWF at hexprwf; exact hexprwf"]
   ```
4. Same pattern for L5280 with arrayLit.

### TARGET 2: convertExpr_not_lit (L3010, L3120)

These need `convertExpr_not_lit` for stub constructors. The comment says "Proved in staging".

1. Check `.lake/_tmp_fix/cc_objectLit_arrayLit_helpers.lean` for the staged proof
2. If it compiles, port the proof directly into ClosureConvertCorrect.lean
3. Try `lean_multi_attempt` at L3010 with:
   ```
   ["simp [Flat.convertExpr]",
    "unfold Flat.convertExpr; simp",
    "intro h; exact absurd h (by simp [Flat.convertExpr])"]
   ```

### TARGET 3: CCState threading (L3534, L3556, L5228, L5532)

L3534: `sorry` in if-then branch — CCState threading between then/else conversions.
L3556: Two `sorry` in if — same class.
L5228: convertPropList over concatenated lists.
L5532: while_ lowering duplicates sub-expressions.

For L3534/L3556: The key property is `CCState` monotonicity:
```lean
-- If convertExpr produces (e1, st1) and then convertExpr with st1 produces (e2, st2),
-- then CCStateAgree st1 st2 and properties proved about st1 still hold at st2
```

Use `lean_goal` at each position to see what's actually needed. Often these are just
`CCStateAgree` transitivity or `CCState_mono` applications.

### TARGET 4: value sub-cases (L4065, L5136, L5235)

L4065: `.call callee args` where callee is a value — need to show arg stepping or call execution.
L5136: `.objectLit props` where all props are values — heap allocation proof.
L5235: `.arrayLit elems` where all elems are values — same as objectLit.

For L5136/L5235: When all elements are values, both Core and Flat do a single heap allocation.
The sim-rel needs: allocated addresses match and heap contents agree.

## DO NOT TOUCH:
- ANFConvertCorrect.lean (proof agent owns this)
- hnoerr/hev_noerr sorries (BLOCKED)
- forIn/forOf stubs (unprovable)

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/jsspec/log.md

## TARGET: Close at least 3 non-hnoerr sorries → CC from 44 to ≤41
