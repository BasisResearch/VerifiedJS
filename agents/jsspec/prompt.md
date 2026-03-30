# jsspec — Close non-hnoerr CC sorries + stage Core Fix D

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## HNOERR SORRIES: BLOCKED — DO NOT ATTEMPT
Your 17:00 analysis was CORRECT. The hnoerr sorries require a design-level fix:
adding Fix D error propagation to Core.step? so both Core and Flat produce the
same state (.lit .undefined) on error events. Until Core Fix D is implemented,
ALL 22 hnoerr/hev_noerr sorries are unprovable. DO NOT waste time on them.

## STATUS (18:05 Mar 30)
- CC: 44 sorries. 22 are hnoerr (BLOCKED). 2 are forIn/forOf (unprovable). **20 are closable.**

## YOUR TASK: Close non-hnoerr sorries

### TARGET 1: ExprAddrWF propagation (L5069, L5168)

L5069: `ExprAddrWF (.objectLit _)` doesn't propagate to elements.
L5168: `ExprAddrWF (.arrayLit _)` doesn't propagate to elements.

These need helper lemmas. Check how `ExprAddrWF` is defined:
```lean
-- ExprAddrWF is probably: all heap addresses in the expression are < heap.objects.size
-- For objectLit: ExprAddrWF (.objectLit ps) n = ... (likely always true or propagates to elements)
```

Use `lean_hover_info` on `ExprAddrWF` to see its definition. Then check if `simp [ExprAddrWF]` at the sorry site works, or if you need to write a `ExprAddrPropListWF_of_ExprAddrWF_objectLit` lemma.

Try `lean_multi_attempt` at L5069:
```
["simp [ExprAddrWF] at hexprwf ⊢; exact hexprwf",
 "exact ExprAddrWF_mono target_c (by simp [ExprAddrWF] at hexprwf; exact hexprwf) (by omega)",
 "simp [ExprAddrWF] at hexprwf; exact hexprwf"]
```

### TARGET 2: convertExpr_not_lit (L2898, L3008)

These need `convertExpr_not_lit` for stub constructors. Check if `convertExpr_not_value_supported`
(defined at L1377) can close them, since the expression is a non-value supported expression.

Try `lean_multi_attempt` at L2898 and L3008.

### TARGET 3: CCState threading (L3422, L3444, L5116, L5420)

These are about CCState agreement when convertExpr is called on different sub-expressions.
The key property: CCState monotonically increases, and `CCStateAgree` is transitive.

L5116: `convertPropList` over concatenated lists. Need to show:
```lean
CCStateAgree (convertPropList (done ++ [target_changed] ++ rest) ...).snd st_a'
```
Try decomposing with `convertPropList_append` and `convertPropList_append_snd`.

### TARGET 4: Stage Core Fix D (LOWER PRIORITY)

Create `.lake/_tmp_fix/Core_fix_d_plan.lean` with:
1. List of all 28 positions in Core/Semantics.lean that need error propagation
2. For each position, the exact code change (add `.error msg` match arm)
3. List of new Core_step?_*_error theorems needed in CC

This staging file will guide the full Fix D implementation in a future run.

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
