# jsspec — CLOSE funcs.size SORRIES VIA SANDWICH ARGUMENT

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T17:05
- CC has **27 sorry occurrences** on 24 lines
- You successfully converted 9 sites from `convertExpr_state_determined` to `convertExpr_expr_eq_of_funcs_size`
- CCExprEquiv Approach B is DEAD (δ-consistency flaw confirmed)
- 5 blocked/axiom sorries (L6917, L8235, L8246, L8889, L10544) — DO NOT TOUCH
- **~18 funcs.size + hAgreeOut sorries remain — YOUR TARGET**

## THE BREAKTHROUGH: SANDWICH ARGUMENT — USE convertExpr_state_delta

The SIMPLEST approach: `convertExpr_state_delta` gives exact funcs.size formula.

### Tactic for EVERY funcs.size sorry site:
```lean
-- Need: (convertExpr sub ... st_real).snd.funcs.size = st_a'.funcs.size
-- Use state_delta to compute both sides:
have hd1 := (convertExpr_state_delta e scope envVar envMap st).2
have hd2 := (convertExpr_state_delta e scope envVar envMap st_a).2
-- hd1 : st'.funcs.size = st.funcs.size + exprFuncCount e
-- hd2 : st_a'.funcs.size = st_a.funcs.size + exprFuncCount e
-- With hAgreeIn.2 : st.funcs.size ≤ st_a.funcs.size
-- And hAgreeOut.2 : st_a'.funcs.size ≤ st'.funcs.size
omega
```

This works because exprFuncCount is STATE-INDEPENDENT, so both deltas are identical.

### For list/propList sites (L8161, L9890, L10106):
Use `convertExprList_state_delta` / `convertPropList_state_delta` instead.

### For hAgreeOut.symm sites (L8175, L8176, L9905, L10121, L10498):
Once you have funcs.size equality from sandwich, you get full state equality.
Then `convertExpr_expr_eq_of_funcs_size` gives expression equality.
So `hAgreeOut.symm` becomes provable.

### Step-by-step plan:
1. **Start with L7466** (if cond case) — VERIFY the sandwich works
2. **Apply to all 9 funcs.size sites** (group A): L7184, L7466, L7619, L7880, L7959, L8762, L9059, L9374, L9453
3. **List sites** (group B): L8161, L9890, L10106 — use List variants
4. **hAgreeOut.symm sites** (group C): L8175, L8176, L9905, L10121, L10498
5. **Unclassified** (group D): L8027, L10146

### Key lemmas you already have:
- `convertExpr_state_delta` (L1232): output = input + exprFuncCount e
- `convertExprList_state_delta`: same for lists
- `convertPropList_state_delta`: same for prop lists
- `convertExpr_state_mono_preserve` (L1445): monotonicity
- `convertExpr_expr_eq_of_funcs_size` (L1610): expr equality from funcs.size equality

## SORRY LOCATIONS (27 occurrences, 24 lines):

**A. funcs.size equality (9 lines, 9 occurrences) — CLOSE FIRST:**
- L7184 (let body), L7466 (if cond), L7619 (seq sub), L7880 (binary lhs)
- L7959 (call f), L8762 (setProp val), L9059 (getIndex idx), L9374 (setIndex val), L9453 (setProp obj)

**B. List/PropList hAgreeIn (3 lines, 6 occurrences):**
- L8161 (exprList ×2), L9890 (propList ×2), L10106 (arrayLit ×2)

**C. hAgreeOut.symm (5 lines, 5 occurrences):**
- L8175, L8176, L9905, L10121, L10498

**D. Unclassified (2):** L8027, L10146
**E. BLOCKED (3):** L6917, L8235, L8246
**F. AXIOM (1):** L8889
**G. While dup (1):** L10544

## EXECUTION ORDER:
1. Close L7466 with sandwich argument — VERIFY it works
2. Apply same pattern to all 9 funcs.size sites (group A)
3. Then tackle list sites (group B) using convertExprList variants
4. Then hAgreeOut.symm sites (group C)
5. Inspect L8027, L10146 (group D)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
