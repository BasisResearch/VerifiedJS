# wasmspec — Close CC value sub-cases (all-values heap allocation proofs)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! CRITICAL: YOUR LAST TWO SESSIONS GOT STUCK IN WHILE LOOPS !!
Your sessions got PERMANENTLY STUCK in `while pgrep -f "lake build"` because
the while loop's OWN shell command string contains "lake build", so pgrep matches ITSELF.
**YOU HAVE WASTED 24+ HOURS STUCK IN WHILE LOOPS. ZERO WORK DONE IN TWO SESSIONS.**

### ABSOLUTE RULES — VIOLATION = WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for anything, EVER
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop** — you will get stuck forever
4. `lake serve` processes are PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To build: just run `lake build VerifiedJS.Proofs.ClosureConvertCorrect` directly
6. If it fails because another build runs: wait 60s with ONE `sleep 60`, then retry ONCE
7. If it fails again: skip the build and work on something else

## MEMORY: 7.7GB total, NO swap.

## IMPORTANT: jsspec may have changed CCStateAgree since last check
Re-read the sorry lines BEFORE editing. Line numbers may have shifted.
Run `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -30` FIRST.

## STATE (04:05): CC has 17 sorries

### Remaining sorry breakdown:
- **2 unprovable stubs** (L1520-1521 forIn/forOf): DO NOT TOUCH
- **2 convertExpr_not_lit** (L2663, L2773): jsspec (ALREADY PROVED ✓)
- **1 captured variable** (L2933): jsspec owns
- **3 CCState if/while** (L3252, L3274, L5313): jsspec owns — fundamentally blocked
- **1 callee is value** (L3768): YOUR TARGET
- **1 newObj** (L3769): YOUR TARGET
- **1 getIndex mismatch** (L4337): possibly unprovable
- **1 setIndex value sub-case** (L4509): YOUR TARGET
- **1 objectLit all-values** (L4831): YOUR TARGET
- **1 arrayLit all-values** (L5014): YOUR TARGET
- **1 functionDef** (L5192): YOUR TARGET
- **1 tryCatch** (L5282): YOUR TARGET

## YOUR TARGETS (7 sorries) — START WITH EASIEST

### TARGET 1: objectLit all-values (L4831) — EASIEST

When `Core.firstNonValueProp props = none`, ALL props are `.lit _` values.
Both Core and Flat allocate a new heap object in one step.

Key hypotheses in scope:
- `hcfnv : Core.firstNonValueProp props = none`
- `hfexpr : sf.expr = Flat.Expr.objectLit (Flat.convertPropList props ...)`
- `hstep : Flat.step? sf = some (ev, sf')`

APPROACH:
1. ALL props are `.lit _`, so `convertPropList` maps `(k, .lit v)` → `(k, .lit (convertValue v))`
2. Flat `valuesFromExprList?` succeeds → allocates via `allocObjectWithProps`
3. Core `step?_objectLit_val` (in Core/Semantics.lean L13581) gives Core's allocation step
4. HeapInj extends: `HeapInj_push` or similar
5. Result: `sc'.expr = .lit (.object addr)`, `sf'.expr = .lit (.object flatAddr)`

Use `lean_goal` at L4831 first. Then build the proof by:
- Getting the Flat step result via unfolding
- Getting the Core step result via `Core.step?_objectLit_val`
- Constructing HeapInj for the extended heap
- All other invariants (env, noCallFrameReturn, etc.) are trivial since only heap changes
- CCStateAgree: `st_a = st, st_a' = st` since `.lit (.object addr)` converts with unchanged state

Related pattern: see how `getProp` value case (L3776-3867) is proved — similar structure.

### TARGET 2: arrayLit all-values (L5014) — SAME PATTERN

Identical to objectLit but with `firstNonValueExpr` instead of `firstNonValueProp`.
Core has `step?_arrayLit_val` (L13597). Follow the exact same approach.

### TARGET 3: setIndex value sub-case (L4509)

When `exprValue? obj = some cv`, `obj = .lit cv`. Then need nested case split:
- `exprValue? idx`: if none → step idx; if some → check value
- `exprValue? value`: if none → step value; if some → execute setIndex

See `setProp` value sub-case pattern (if it exists) for reference.

### TARGET 4: call callee-is-value (L3768)

When callee `f = .lit cv`, need to check args:
- `allValues args = some vs` → execute call
- `allValues args = none` → step first non-value arg
Core has `step_call_step_arg` (L13621) and `step_call_nonfunc_exact` (L13610).

### TARGET 5: newObj (L3769)
### TARGET 6: functionDef (L5192)
### TARGET 7: tryCatch (L5282) — HARDEST, skip if short on time

## TACTIC PATTERNS (from proved cases):
```lean
-- For value sub-cases:
have hlit : obj = .lit cv := by cases obj <;> simp [Core.exprValue?] at hcev; subst hcev; rfl
subst hlit
simp [Flat.convertExpr] at hfexpr hst
-- Then build sf_eta, rewrite hstep, case-split on step? result
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1520-1521) — unprovable
- CCState threading sorries (L2933, L3252, L3274, L5313) — jsspec owns

## WORKFLOW:
1. `lean_goal` at sorry line → read FULL goal
2. `lean_multi_attempt` with 6-8 tactics
3. If nothing closes it in 15 minutes, MOVE TO THE NEXT ONE
4. Log what you tried and why it failed
5. Build after every successful proof change

## TARGET: Close at least 2 of your 7 assigned sorries → CC from 17 to ~15
