# proof — CLOSE 30+ SORRIES RIGHT NOW (mechanical fixes)

## PHASE 1: Replace `sorry, sorry` with `hAgreeIn, hAgreeOut` (20 sorry tokens)

These 10 lines each have `sorry, sorry` where `hAgreeIn` and `hAgreeOut` are in scope from the IH obtain.

**The exact edit** on each line: replace `sorry, sorry⟩` with `hAgreeIn, hAgreeOut⟩`

Lines: **2071, 2369, 2466, 2584, 2706, 2795, 2887, 3091, 3229, 3316**

Each line looks like:
```lean
exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, sorry, sorry⟩
```
Replace with:
```lean
exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, hAgreeOut⟩
```

DO THIS FIRST. It is 100% mechanical and closes 20 sorry tokens.

## PHASE 2: Replace `⟨rfl, rfl⟩, sorry⟩` where st' = st (simple base cases)

For var and this cases where `hst_eq : st' = st` is in scope:
- **L1825**: replace `sorry⟩` with `hst_eq ▸ ⟨rfl, rfl⟩⟩`
- **L1848**: same
- **L1876**: same
- **L1899**: same

For cases where `hst` is `st' = (Flat.convertExpr (.lit cv) ... st).snd`:
- **L2019** (assign value): replace `sorry⟩` with `by simp [Flat.convertExpr] at hst; subst hst; exact ⟨rfl, rfl⟩⟩`
- **L2829** (throw value): same pattern
- **L2956, L2979** (break/continue): `hst : st' = st` directly → `hst ▸ ⟨rfl, rfl⟩⟩`

For cases past L2919 (return/yield/await/labeled base cases):
- **L3005, L3035, L3143, L3173, L3260**: check `hst` type, if it's `st' = st`, use `hst ▸ ⟨rfl, rfl⟩`
- If `hst` is more complex, use `by simp [Flat.convertExpr] at hst; subst hst; exact ⟨rfl, rfl⟩`

## PHASE 3: The 6 CCState stepping sorries

Lines: **1989, 2196, 2285, 2524, 2647, 2919**

### Pattern for L1989 (let stepping):
```lean
· -- CCState for let stepping
  have hsd := convertExpr_state_determined body (name :: scope) envVar envMap
    (Flat.convertExpr init scope envVar envMap st).snd st_a' hAgreeOut.1 hAgreeOut.2
  refine ⟨st_a, (Flat.convertExpr body (name :: scope) envVar envMap st_a').snd, ?_, hAgreeIn, hsd.2⟩
  simp only [sc', Flat.convertExpr]
  have h1 := congrArg Prod.fst hconv'.symm  -- sa.expr = (convertExpr sc_sub'.expr ... st_a).fst
  have h2 := congrArg Prod.snd hconv'.symm  -- st_a' = (convertExpr sc_sub'.expr ... st_a).snd
  rw [h1, h2, ← hsd.1]
```

Use `lean_goal` at each line to see the exact goal, then adapt this pattern.

### For L2196 (if stepping): same pattern but with cond/then_/else_
### For L2285 (seq stepping): same pattern but with a/b
### For L2524 (binary lhs stepping): same pattern but with lhs/rhs
### For L2647 (getIndex stepping): same pattern but with obj/idx
### For L2919 (while_): may be simpler since while_ unrolls

## PHASE 4: Compound value-base sorry cases (SKIP for now)
Lines L1932, L2108, L2130, L2228, L2315, L2410, L2741, L3117 — these need architectural analysis.
DO NOT attempt these until Phases 1-3 are done.

## DO NOT TOUCH:
- ANFConvertCorrect, LowerCorrect, Wasm/Semantics
- forIn/forOf at L1132/L1133
- Full-case sorries: L1797, L2525, L2526, L2585, L2648, L2796, L2797, L2798, L2888
- Value sub-cases: L2532, L2591, L2654

## EXECUTION ORDER
1. Phase 1 first (all 10 lines). Build. Verify.
2. Phase 2 next (as many as you can). Build. Verify.
3. Phase 3 if time permits.

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/proof/log.md.
