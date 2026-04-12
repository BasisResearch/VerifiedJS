# proof — ANF COMPOUND CASES + WHILE/IF/TRYCATCH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T14:05
- ANF has **29 real sorry lines** (unchanged since 13:05)
- 12 are BLOCKED (L11366-L11737) — DO NOT TOUCH
- 4 are wasmspec-owned — DO NOT TOUCH
- 1 is recursive dependency (L31484) — SKIP
- **YOUR TARGET: 12 remaining sorry lines across P0-P3**

## P1: WHILE CONDITION (2 sorries) — START HERE, MOST TRACTABLE

### L24999: Condition-steps case (while condition steps)
This is the MOST tractable sorry. The resulting expression `.seq (.while_ sc.expr d) b` IS normalizeExpr-compatible.

**Concrete approach:**
1. `lean_goal` at L24999 to get exact proof state
2. Use `normalizeExpr_while_decomp` (L24901) to decompose `hnorm`
3. The decomposition gives you `c`, `d`, `b` components from normalizeExpr
4. After condition steps: `sa'.expr = .seq (.while_ sc.expr d) b`
5. Need to show this matches `normalizeExpr (.while_ sc.expr wb) k` for appropriate state
6. Use the IH from the enclosing induction for the condition stepping

**Try this tactic sequence:**
```lean
-- At L24999:
obtain ⟨n1, n2, hc_norm, hd_norm, hk_norm⟩ := normalizeExpr_while_decomp wc wb k _ _ _ _ _ hnorm
-- Now use condition stepping IH to get flat simulation for wc → sc.expr
-- Then reconstruct the while via normalizeExpr_while_decomp applied to sc.expr
```

### L24987: While condition value case
After while unrolls, `sa'.expr` is either `.seq (.seq d (.while_ c d)) b` or `.seq (.trivial .litUndefined) b`.
This is a transient form. **Strategy**: show this needs MULTI-STEP simulation — the `.trivial .litUndefined` case takes 0 more steps (done), the `.seq d (.while_ c d)` case needs the body simulation.

Try `lean_multi_attempt` at L24987 with:
```
["cases toBoolean v <;> simp at * <;> sorry",
 "simp only [Core.toBoolean] at * <;> sorry"]
```

## P0: COMPOUND AWAIT/YIELD/RETURN (5 sorries)

### L24892: return (some val) compound
`normalizeExpr (.return (some val)) k` uses `evalComplex val (fun t => pure (.return (some (.trivial t))))`.
When `val` is compound, this produces `.let` structures.

**Concrete approach:**
1. `lean_goal` at L24892
2. `simp only [ANF.normalizeExpr] at hnorm` to unfold one level
3. The result goes through `evalComplex val ...` which produces `.let name rhs body`
4. Need `evalComplex_let_decomp` or similar to split hnorm
5. Then show the flat step through `.return (some val)` matches

### L24896: yield (some val) compound — same pattern as L24892

### L24897: compound expressions catch-all
This is the hardest. Skip until L24892 and L24896 are done.

### L24663, L24836: compound HasAwaitInHead/HasYieldInHead
Blocked by error propagation infrastructure at L11763. Skip.

## P2: IF-BRANCH (2 sorries) — L25724, L25764
24 sub-cases each, all K-mismatch. These are hard.
**Strategy**: Use `lean_multi_attempt` to test if any sub-case is now closable:
```
["cases sf.expr <;> simp at * <;> sorry",
 "intro h; cases h <;> sorry"]
```

## P3: TRYCATCH (3 sorries) — L26605, L26623, L26626
Lower priority. Skip until P1 is done.

## EXECUTION ORDER:
1. **P1 L24999** (while condition steps) — most tractable, do this FIRST
2. **P1 L24987** (while condition value) — try after L24999
3. **P0 L24892** (return some val) — next priority
4. **P0 L24896** (yield some val) — same pattern
5. **P2** (if-branch) — only if P0/P1 done
6. **P3** (trycatch) — last

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
