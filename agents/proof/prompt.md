# proof — ANF COMPOUND CASES + WHILE/IF/TRYCATCH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T17:05
- ANF has **26 sorry lines** (L18163 CLOSED by wasmspec — DO NOT TOUCH)
- 12 are BLOCKED (L11366-L11737) — DO NOT TOUCH
- 2 are wasmspec-owned (L19377, L32634) — DO NOT TOUCH
- **YOUR TARGET: 12 remaining sorry lines across P1-P3**

## !! CRITICAL: P4/L18163 IS DONE !!
Wasmspec closed L18163 (step_error_noNonCallFrameTryCatch_isLit) at 16:35.
The proof is LIVE in the file. DO NOT revert or modify it.
If you are currently working on L18163, STOP IMMEDIATELY and move to P1.

## P1: WHILE CONDITION (2 sorries) — DO THIS FIRST

### L24993: Condition-steps case
This IS normalizeExpr-compatible. Use `normalizeExpr_while_decomp` (around L24901).

```lean
-- At L24993, proof state has hnorm for .seq (.while_ c d) b
obtain ⟨n1, n2, hc_norm, hd_norm, hk_norm⟩ := normalizeExpr_while_decomp wc wb k _ _ _ _ _ hnorm
-- Then use condition stepping IH for wc → sc.expr
```

### L24981: While condition value case — transient state, needs multi-step SimRel
Try `lean_goal` first to see exact proof state.

## P0: COMPOUND AWAIT/YIELD/RETURN (5 sorries) — L24657, L24830, L24886, L24890, L24891
Blocked by error propagation infrastructure. Lower priority than P1.

## P2: IF-BRANCH (2 sorries) — L25718, L25758
24 sub-cases each, K-mismatch. Try after P1.

## P3: TRYCATCH (3 sorries) — L26599, L26617, L26620
Lower priority.

## EXECUTION ORDER:
1. **P1 L24993** (while condition steps) — most tractable, DO FIRST
2. **P1 L24981** (while condition value) — try after L24993
3. **P2 L25718, L25758** (if-branch) — try after P1
4. **P0** — only if P1+P2 done
5. **P3** — last

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
