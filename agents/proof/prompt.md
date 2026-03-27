# proof — Close CC CCState sorries using convertExpr_state_determined (IT'S COMPLETE NOW!)

## BUILD FIX NEEDED FIRST
Line 641 has `simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, hid]` which causes
"simp made no progress" error. Fix by changing to:
```lean
try simp only [Flat.CCState.freshVar, Flat.CCState.addFunc, hid]
```
Or if that doesn't help, just delete the line — the `unfold` on L640 may already do the work.
Then run: `lake build VerifiedJS.Proofs.ClosureConvertCorrect` — must PASS before any sorry work.

## THE KEY LEMMA IS READY — USE IT

`convertExpr_state_determined` (line 548) is COMPLETE with NO sorry. It proves:
```lean
theorem convertExpr_state_determined (e : Core.Expr) (scope envVar envMap) (st1 st2 : CCState)
    (hid : st1.nextId = st2.nextId) (hsz : st1.funcs.size = st2.funcs.size) :
    (convertExpr e scope envVar envMap st1).fst = (convertExpr e scope envVar envMap st2).fst ∧
    CCStateAgree (convertExpr e scope envVar envMap st1).snd (convertExpr e scope envVar envMap st2).snd
```

Use `.1` for expression equality, `.2` for output state agreement.

## PRIORITY 1: 6 CCState sorries — ALL USE THE SAME PATTERN

### Lines: L1973, L2180, L2269, L2508, L2631, L2903

Each sorry is at a point where:
- An inner sub-expression stepped (e.g., cond in if, a in seq, lhs in binary)
- The IH gave a new Flat state with the sub-expression converted under st
- But the REST of the expression was converted under a different CCState (output of converting the sub-expression)
- Need to show the Flat expr matches the Core expr when CCState differs

### Strategy for each:
1. `lean_goal` at the sorry line to see the exact goal
2. The goal should involve `(convertExpr e scope envVar envMap st').fst` vs `(convertExpr e scope envVar envMap st'').fst` where st' and st'' have different nextId/funcs.size
3. Use `convertExpr_state_determined` to rewrite one into the other
4. You need to show `st'.nextId = st''.nextId` and `st'.funcs.size = st''.funcs.size` — these come from `CCStateAgree` in the hypothesis context
5. Try tactics like:
```lean
have hsd := convertExpr_state_determined <subexpr> scope envVar envMap <st1> <st2> <hid> <hsz>
rw [hsd.1]
```
6. `lean_multi_attempt` at each line with:
```
["rw [(convertExpr_state_determined _ scope envVar envMap _ _ (by assumption) (by assumption)).1]",
 "exact (convertExpr_state_determined _ scope envVar envMap _ _ ‹_› ‹_›).1 ▸ rfl",
 "congr 1; exact (convertExpr_state_determined _ scope envVar envMap _ _ ‹_› ‹_›).1"]
```

Start with L2180 (if stepping) — it's the clearest case. Then apply to all others.

## PRIORITY 2: call/newObj (L2509, L2510)
These need sub-expression stepping + argument list reasoning. Try:
```lean
lean_goal at L2509
```
Then attempt `sorry` decomposition if complex.

## PRIORITY 3: objectLit/arrayLit/functionDef (L2784, L2785, L2786)
- objectLit/arrayLit: list-based conversion, may need `convertExprList` lemmas
- functionDef: closure creation, needs `addFunc`/`freshVar` reasoning

## DO NOT TOUCH:
- ANFConvertCorrect (architecturally blocked)
- LowerCorrect (blocked on lowerExpr)
- Wasm/Semantics (wasmspec owns)
- forIn/forOf at L1118/L1119 (conversion is stub → theorem may be false for these)
- Value sub-cases at L2516/L2579/L2638 (heap reasoning, skip for now)

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Use lean_goal + lean_multi_attempt BEFORE every edit.
## Log progress to agents/proof/log.md.
