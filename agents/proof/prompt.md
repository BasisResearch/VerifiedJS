# proof — CLOSE THE 6 CCState SORRIES NOW

## GREAT NEWS: Suffices refactor is DONE
The suffices at L1748 now has scope/st/st' as universal args and CCStateAgree in the output.
Your IH calls should now produce `hAgreeIn : CCStateAgree st st_a` and `hAgreeOut : CCStateAgree st' st_a'`.

## YOUR SOLE PRIORITY: Close these 6 sorries

### 1. L1988: let stepping CCState
### 2. L2195: if stepping CCState
### 3. L2284: seq stepping CCState
### 4. L2523: binary lhs stepping CCState
### 5. L2646: getIndex stepping CCState
### 6. L2918: while_ CCState

## THE PATTERN (same for all 6)

Each sorry has the goal:
```
∃ st_a st_a' : Flat.CCState,
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧ CCStateAgree st' st_a'
```

From the IH on the sub-expression, you already have:
- `st_a, st_a'` (from the IH output existential)
- `hconv' : (sub_sf'.expr, st_a') = convertExpr sc_sub'.expr scope envVar envMap st_a`
- `hAgreeIn : CCStateAgree st_orig st_a` (or similar)
- `hAgreeOut : CCStateAgree st_orig' st_a'`

### For let (L1988):
The goal is about `convertExpr (.let name sc_sub'.expr body) scope envVar envMap st_a`.
This unfolds to:
```
let (e1, s1) = convertExpr sc_sub'.expr scope envVar envMap st_a
let (e2, s2) = convertExpr body (name::scope) envVar envMap s1
(.let name e1 e2, s2)
```

You need:
1. `e1 = sub_sf'.expr` (from hconv')
2. `s1 = st_a'` (from hconv')
3. Body part: use `convertExpr_state_determined` with CCStateAgree to show the body converts the same way

Key lemma: `convertExpr_state_determined` — if `CCStateAgree s1 s2`, then
`convertExpr e scope envVar envMap s1` and `convertExpr e scope envVar envMap s2`
produce the same expression (fst) and `CCStateAgree` output states (snd).

### For if (L2195):
Same idea: `convertExpr (.if sc_sub'.expr then_ else_) scope envVar envMap st_a` unfolds.
Sub-expression gives the cond part, then use `convertExpr_state_determined` for then_ and else_ branches.

### For seq (L2284), binary (L2523), getIndex (L2646):
Same pattern, just different sub-expression structure.

### For while_ (L2918):
`convertExpr (.while_ cond body)` duplicates cond and body:
```
let (c, s1) = convertExpr cond scope envVar envMap st
let (b, s2) = convertExpr body scope envVar envMap s1
(.if c (.seq b (.while_ c b)) (.lit .undefined), s2)
```
Since while_ doesn't step its sub-expressions (it unfolds to if), the CCState witnesses are `st` and `st'` directly, with `CCStateAgree st st ∧ CCStateAgree st' st'` via reflexivity.

## ALSO: Install jsspec patches for setProp/setIndex

jsspec prepared patches in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_expr_patches.lean`.
After closing CCState sorries, read that file and apply the setProp (L2584) and setIndex (L2647) patches.

## EXECUTION CHECKLIST
1. Use `lean_goal` at L1988 to see exact goal state
2. Try to close it with the pattern above
3. Repeat for L2195, L2284, L2523, L2646, L2918
4. Each closure = 1 fewer sorry. Target: 20 → 14

## DO NOT TOUCH:
- ANFConvertCorrect, LowerCorrect, Wasm/Semantics
- forIn/forOf at L1132/L1133 (theorem false — stubs)
- Value sub-cases at L2531/L2590/L2653
- The suffices statement itself (it's correct now)

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Use lean_goal + lean_multi_attempt BEFORE every edit.
## Log progress to agents/proof/log.md.
