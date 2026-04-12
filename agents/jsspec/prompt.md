# jsspec — CLOSE CCStateAgreeWeak SORRIES VIA CCExprEquiv

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T14:05
- CC has **25 real sorry lines** (unchanged for 12 days)
- 5 blocked/axiom sorries (L6917, L8219, L8230, L8870, L10515) — DO NOT TOUCH
- **20 CCStateAgreeWeak sorries** — YOUR TARGET
- Monotone approach was REJECTED (March 31 analysis confirmed it breaks chaining)

## THE FIX: CCExprEquiv-BASED SIMULATION (Approach B)

### Why this works
- `convertExpr_CCExprEquiv_shifted` (L1854) is ALREADY PROVEN for all expression types
- It requires only `funcs.size` difference, NOT `nextId` equality
- The branching constructs naturally produce states with different `funcs.size`
- CCExprEquiv captures: expressions differ only in makeClosure function indices

### Step 1: Understand the infrastructure (READ FIRST)
```lean
-- L1499-1547: CCExprEquiv definition
lean_hover_info file="VerifiedJS/Proofs/ClosureConvertCorrect.lean" line=1499 column=0

-- L1854: The key theorem
lean_hover_info file="VerifiedJS/Proofs/ClosureConvertCorrect.lean" line=1854 column=0
```

### Step 2: Prototype on ONE sorry pair (L7461 — if cond case)

Current code at L7461:
```lean
(Flat.convertExpr cond scope envVar envMap st).snd st_a' sorry /- hAgreeOut.1 -/ sorry /- hAgreeOut.2 -/
```

This calls `convertExpr_state_determined` which requires CCStateAgree (equality).

**Replace with CCExprEquiv approach:**
```lean
-- Instead of convertExpr_state_determined (needs equality), use:
have h_equiv : CCExprEquiv δ
    (Flat.convertExpr then_ scope envVar envMap (Flat.convertExpr cond scope envVar envMap st).snd).fst
    (Flat.convertExpr then_ scope envVar envMap st_a').fst :=
  convertExpr_CCExprEquiv_shifted then_ scope envVar envMap
    (Flat.convertExpr cond scope envVar envMap st).snd st_a' δ
    (by omega)  -- funcs.size relationship from convertExpr_state_delta
```

**BUT**: You also need to change the simulation invariant at L6858-6861 to use CCExprEquiv instead of expression equality. This is the key refactoring.

### Step 3: Change the simulation invariant (L6858-6861)

Current:
```lean
∃ (st_a st_a' : Flat.CCState),
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgreeWeak st st_a ∧ CCStateAgreeWeak st_a' st'
```

Change to:
```lean
∃ (st_a st_a' : Flat.CCState) (δ : Nat),
  CCExprEquiv δ sf'.expr (Flat.convertExpr sc'.expr scope envVar envMap st_a).fst ∧
  st_a' = (Flat.convertExpr sc'.expr scope envVar envMap st_a).snd ∧
  CCStateAgreeWeak st st_a ∧ CCStateAgreeWeak st_a' st' ∧
  st.funcs.size + δ = st_a.funcs.size
```

With this invariant, the sorry sites transform from needing `convertExpr_state_determined` (needs equality) to needing `convertExpr_CCExprEquiv_shifted` (needs only funcs.size offset).

### Step 4: Verify CCExprEquiv properties exist
Before changing the invariant, verify these exist:
1. `CCExprEquiv.refl`: `CCExprEquiv 0 e e` — for base cases
2. Composition/transitivity — for chaining sub-expressions
3. `CCExprEquiv` compatibility with Flat.step? — for simulation preservation

Check with:
```
lean_local_search query="CCExprEquiv" file="VerifiedJS/Proofs/ClosureConvertCorrect.lean"
```

### CRITICAL WARNING
Changing the invariant at L6858 will break ALL existing proofs that use expression equality.
**DO NOT** change it until you have verified the CCExprEquiv approach works on L7461 as a prototype.

**Prototype plan:**
1. Add a SEPARATE lemma `cc_step_sim_CCExprEquiv_if_cond` that proves the if-cond case with the new invariant
2. If the prototype works, THEN change the invariant
3. If not, document exactly what's missing

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
1. Read CCExprEquiv definition and convertExpr_CCExprEquiv_shifted signature
2. Prototype on L7461 (if cond) with a separate lemma
3. If works: change invariant at L6858 and fix all sorry sites
4. If doesn't work: document what's missing

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
