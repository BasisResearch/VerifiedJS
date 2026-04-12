# jsspec — CLOSE CCStateAgreeWeak SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T13:05
- CC has **25 real sorry lines** (5 blocked/axiom, 20 CCStateAgreeWeak)
- The dominant pattern: `convertExpr_state_determined ... st_a' sorry /- hAgreeOut.1 -/ sorry /- hAgreeOut.2 -/`
- These need equality where IH only provides CCStateAgreeWeak (≤)

## THE CORE PROBLEM

At each sorry site, we have:
- `st' = (convertExpr init ... st).snd` — the "real" output state
- `st_a' = (convertExpr sc_sub'.expr ... st_a).snd` — the IH output state
- `CCStateAgreeWeak st st_a` means `st.nextId ≤ st_a.nextId`
- `CCStateAgreeWeak st_a' st'` means `st_a'.nextId ≤ st'.nextId`
- **Need**: `st'.nextId = st_a'.nextId` (equality)

`convertExpr_state_delta` (L1232) shows:
- `st'.nextId = st.nextId + exprFuncCount init`
- `st_a'.nextId = st_a.nextId + exprFuncCount sc_sub'.expr`

Since `init ≠ sc_sub'.expr` (one is pre-step, one is post-step), and `st.nextId ≤ st_a.nextId`,
the delta approach DOES NOT give equality. Monotone approach also FAILS (March 31 analysis).

## THE REAL FIX: Strengthen invariant to CCStateAgree

The invariant at L6858-6860 uses `CCStateAgreeWeak`. Change it to `CCStateAgree` (equality):

```lean
∃ (st_a st_a' : Flat.CCState),
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧ CCStateAgree st_a' st'
```

**Why this might work now**: The initial state `st_a = st` (equality) at the start of simulation.
If each simulation step can produce `st_a = st` (not just ≤), then the cascade problem disappears.

**The cascade problem**: When a compound expression like `.if cond then_ else_` steps and only
one branch is taken, the output state `st'` accounts for BOTH branches (because `convertExpr`
processes both). The IH gives `st_a'` from converting only the TAKEN branch's sub-expression.

**Two approaches to fix the cascade**:

### Approach A: Track the conversion function index directly
Instead of existential `st_a`, use the actual conversion state from the simulation:
```lean
sf'.expr = (Flat.convertExpr sc'.expr scope envVar envMap st).fst ∧
(Flat.convertExpr sc'.expr scope envVar envMap st).snd = st'
```
This would mean `st_a = st` always, so equality is trivially maintained.
BUT: this breaks when sub-expressions step, because the flat expression after stepping
is NOT `convertExpr` applied to the stepped core expression with the same state.

### Approach B: CCExprEquiv-based simulation relation
Replace expression equality with `CCExprEquiv δ` in the simulation:
```lean
CCExprEquiv δ sf'.expr (Flat.convertExpr sc'.expr scope envVar envMap st').fst
```
where δ accounts for the function index shift.
`convertExpr_CCExprEquiv_shifted` (L1854) already handles the expression part.
The state threading would use `convertExpr_state_delta` for state equality on output.

**Recommended: Approach B**, because:
1. `convertExpr_CCExprEquiv_shifted` infrastructure already exists
2. Expression equivalence modulo function indices is the natural invariant
3. State delta gives `output = input + exprFuncCount e`, so output equality follows from input equality

### Concrete Plan for Approach B:
1. Change the invariant to use `CCExprEquiv δ` instead of expression equality
2. At each sorry site, instead of `convertExpr_state_determined`, use `convertExpr_CCExprEquiv_shifted`
3. Prove that the simulation relation is preserved under `CCExprEquiv δ`

This is a significant refactoring but would close all ~20 sorry pairs at once.

## SORRY LOCATIONS (25 real sorry lines):

**A. CCStateAgreeWeak pairs (~20 lines):**
- L7181-7186 (let body), L7461 (if cond), L7610 (assign), L7868 (binary lhs)
- L7944 (call f), L8744 (getProp obj), L9038 (setProp obj), L9350 (setIndex)
- L9426 (deleteProp obj), L8145 (exprList), L9861 (propList), L10077 (arrayLit)
- L8159-8160 (hAgreeOut.symm), L9876, L10092, L10469

**B. Unclassified (2):** L8011, L10117
**C. Multi-step gap (3, BLOCKED):** L6917, L8219, L8230
**D. AXIOM (1, UNPROVABLE):** L8870
**E. While duplication (1, BLOCKED):** L10515

## EXECUTION ORDER:
1. **Analyze**: `lean_hover_info` on `CCExprEquiv` at L1459 and `convertExpr_CCExprEquiv_shifted` at L1854
2. **Prototype**: Pick ONE sorry pair (L7461, if cond). Try replacing `convertExpr_state_determined` with `convertExpr_CCExprEquiv_shifted` + appropriate δ
3. **If it works**: Generalize to all sorry sites
4. **If it doesn't**: The simulation relation needs a deeper refactor

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
