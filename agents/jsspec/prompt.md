# jsspec — CLOSE funcs.size SORRIES VIA SANDWICH ARGUMENT

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T16:05
- CC has **27 sorry occurrences** on 24 lines (down ~12 from before your conversion)
- You successfully converted 9 sites from `convertExpr_state_determined` to `convertExpr_expr_eq_of_funcs_size`
- CCExprEquiv Approach B is DEAD (δ-consistency flaw confirmed)
- 5 blocked/axiom sorries (L6917, L8235, L8246, L8889, L10544) — DO NOT TOUCH
- **~18 funcs.size + hAgreeOut sorries remain — YOUR TARGET**

## THE BREAKTHROUGH: SANDWICH ARGUMENT

You already have ALL the infrastructure needed. The funcs.size sorry sites are closable NOW.

### Key insight
At each sorry site you need: `(convertExpr sub ... st_real).snd.funcs.size = st_a'.funcs.size`

You have TWO CCStateAgreeWeak constraints (from the simulation invariant L6858-6860):
1. Input: `CCStateAgreeWeak st st_a` → `st.funcs.size ≤ st_a.funcs.size`
2. Output: `CCStateAgreeWeak st_a' st'` → `st_a'.funcs.size ≤ st'.funcs.size`

Where `st_a' = (convertExpr e ... st_a).snd` and `st' = (convertExpr e ... st).snd`.

**Sandwich:**
- From (1) + `convertExpr_state_mono_preserve` (L1445): `st'.funcs.size ≤ st_a'.funcs.size`
- From (2): `st_a'.funcs.size ≤ st'.funcs.size`
- **Therefore: `st_a'.funcs.size = st'.funcs.size` (and `st_a.funcs.size = st.funcs.size`)**

### Concrete tactic for each sorry site

For any sorry that needs `(convertExpr sub ... st_real_out).snd.funcs.size = st_a'.funcs.size`:

```lean
-- Given: hAgreeIn : CCStateAgreeWeak st st_a
--        hAgreeOut : CCStateAgreeWeak st_a' st'
-- Where st' = (convertExpr e ... st).snd and st_a' = (convertExpr e ... st_a).snd
have h_mono := (convertExpr_state_mono_preserve e scope envVar envMap st st_a hAgreeIn.1 hAgreeIn.2).2
-- h_mono : (convertExpr e ... st).snd.funcs.size ≤ (convertExpr e ... st_a).snd.funcs.size
-- hAgreeOut.2 : st_a'.funcs.size ≤ st'.funcs.size
-- So: st'.funcs.size ≤ st_a'.funcs.size AND st_a'.funcs.size ≤ st'.funcs.size
omega
```

Or even simpler — you can use `convertExpr_state_delta` (L1232) directly:
```lean
have hd1 := (convertExpr_state_delta e scope envVar envMap st).2
have hd2 := (convertExpr_state_delta e scope envVar envMap st_a).2
-- hd1 : st'.funcs.size = st.funcs.size + exprFuncCount e
-- hd2 : st_a'.funcs.size = st_a.funcs.size + exprFuncCount e
omega  -- with hAgreeIn.2 and hAgreeOut.2
```

### Step-by-step plan

1. **Start with L7466** (if cond case) — you already restructured this site, just add the sandwich
2. **Apply to L7184, L7619, L7880, L7959, L8762, L9059, L9374, L9453** — all same pattern
3. **Then tackle L8161, L9890, L10106** (list patterns) — may need `convertExprList_state_delta`
4. **Then L8175, L8176, L9905, L10121, L10498** (hAgreeOut.symm) — same sandwich but reversed direction
5. **Finally L8027, L10146** — unclassified, inspect individually

### Key lemmas you already have:
- `convertExpr_state_delta` (L1232): output = input + exprFuncCount e
- `convertExprList_state_delta` (L1340-ish): same for lists
- `convertExpr_state_mono_preserve` (L1445): monotonicity
- `convertExprList_state_mono_preserve` (L1458): same for lists
- `convertExpr_expr_eq_of_funcs_size` (L1610): expr equality from funcs.size equality

### After funcs.size sorries are closed
The sandwich also proves `st.funcs.size = st_a.funcs.size` (input equality!).
This means `convertExpr_expr_eq_of_funcs_size` applies, giving EXPRESSION EQUALITY.
So the hAgreeOut.symm sites should also close — the expressions are equal, so the output states agree.

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
