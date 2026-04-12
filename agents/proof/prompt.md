# proof — ANF COMPOUND CASES + WHILE/IF/TRYCATCH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T16:05
- ANF has **28 real sorry lines** (unchanged since last session)
- L18163: attempted uncomment of ~450-line proof, reverted due to 39 tactic errors. FIX THIS.
- 12 are BLOCKED (L11366-L11737) — DO NOT TOUCH
- 2 are wasmspec-owned (L19377, L32640) — DO NOT TOUCH
- 1 is recursive dependency (L31484) — SKIP
- **YOUR TARGET: 13 remaining sorry lines across P0-P4**

## P4: FIX L18163 — MOST IMPACTFUL, DO FIRST

### The problem
L18163 has `exact sorry` for `step_error_noNonCallFrameTryCatch_isLit`.
A ~450-line proof exists in the comment block L18164-L18570 but has 39 tactic errors.
You attempted to uncomment it but reverted at 16:04.

### The systematic fix
The errors are all the SAME pattern: after `split at hstep`, the new Lean version generates an extra `h_2` hypothesis. Each case that does `simp at hstep` now needs:
```lean
-- OLD (broken):
· simp at hstep
-- NEW (fixed):
· rename_i h_2; simp at hstep  -- or: simp at hstep h_2
-- or simply:
· simp_all
```

**Approach:**
1. Uncomment the proof block (L18164-L18570): remove `/-` at L18164 and `-/` at end
2. Run `lean_diagnostic_messages` to get the EXACT error lines
3. Fix each error by adding `rename_i h_2; ` before the simp or using `simp_all`
4. This is MECHANICAL — each fix is the same pattern
5. Verify with `lean_diagnostic_messages` after each batch of fixes

**WARNING:** Do NOT try to fix all 39 at once. Fix 5-10, verify, repeat.

## P1: WHILE CONDITION (2 sorries) — AFTER P4

### L24999: Condition-steps case
This IS normalizeExpr-compatible. Use `normalizeExpr_while_decomp` (L24901).

```lean
-- At L24999, proof state has hnorm for .seq (.while_ c d) b
obtain ⟨n1, n2, hc_norm, hd_norm, hk_norm⟩ := normalizeExpr_while_decomp wc wb k _ _ _ _ _ hnorm
-- Then use condition stepping IH for wc → sc.expr
```

### L24987: While condition value case — transient state, needs multi-step SimRel

## P0: COMPOUND AWAIT/YIELD/RETURN (5 sorries) — L24663, L24836, L24892, L24896, L24897
Blocked by error propagation infrastructure. Lower priority.

## P2: IF-BRANCH (2 sorries) — L25724, L25764
24 sub-cases each, K-mismatch. Lower priority.

## P3: TRYCATCH (3 sorries) — L26605, L26623, L26626
Lower priority.

## EXECUTION ORDER:
1. **P4 L18163** — fix 39 tactic errors in commented-out proof (HIGHEST IMPACT)
2. **P1 L24999** (while condition steps) — most tractable
3. **P1 L24987** (while condition value) — try after L24999
4. **P0** — only if P4+P1 done
5. **P2/P3** — last

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
