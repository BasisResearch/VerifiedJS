# proof — TRIVIAL MISMATCH INFRASTRUCTURE + WHILE/IF/TRYCATCH

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T18:05
- ANF has **~29 sorry statements**
- Build is CLEAN (you fixed all 1246 errors last run — GREAT WORK)
- 12 are infrastructure "trivial mismatch" (L11388-L11759) — **NEW P0: THESE ARE YOUR TOP PRIORITY**
- 2 are wasmspec-owned (L19389, L32645) — DO NOT TOUCH
- ~15 are P1-P4 (compound/while/if/tryCatch)

## !! P0: TRIVIAL MISMATCH INFRASTRUCTURE (12 sorries) — DO THIS FIRST !!

These 12 sorries are ALL the same pattern: `¬HasLabeledInHead e label` means the sub-expression is "trivial" (no label in head position), but we can't connect this to the flat simulation.

### The pattern (7 cases at L11388, L11436, L11484, L11534, L11561, L11611, L11663):
```
· -- ¬HasLabeledInHead sub: blocked by trivial mismatch (ANF trivial ≠ flat value)
  sorry
```

### What you need:
A lemma like:
```lean
theorem noLabeledInHead_sim (e : Flat.Expr) (label : String)
    (h : ¬HasLabeledInHead e label)
    (hrel : ANF_SimRel ...) :
    -- The flat expression evaluates to a value without encountering label
    ∃ sf', Flat.Steps sf sf' ∧ sf'.expr.isValue = true ∧ ...
```

Or check: does `¬HasLabeledInHead e label` with the ANF normalization hypothesis give you enough to invoke the IH at depth 0? The sub-expression has no label, so its ANF normalization should be trivial.

### Step-by-step:
1. `lean_goal` at L11388 to see exact proof state
2. Look at what hypotheses you have — especially `hnorm` and the depth argument
3. If `¬HasLabeledInHead lhs label`, then `normalizeExpr lhs` should produce a trivial result
4. Check if there's already a `noLabeledInHead_trivialChain` or similar lemma
5. If not, WRITE ONE — it would close 7 sorries

### List variants (5 cases at L11613, L11665, L11696, L11728, L11759):
Same concept but for args lists and prop lists. May need list-level trivial chain lemma.

## P1: WHILE CONDITION (2 sorries) — L24999, L25011
Try after P0. These need multi-step SimRel.

## P2: IF-BRANCH (2 sorries) — L25736, L25776
24 sub-cases each, K-mismatch.

## P3: COMPOUND (5 sorries) — L24675, L24848, L24904, L24908, L24909
Blocked by error propagation infrastructure.

## P4: TRYCATCH (3 sorries) — L26617, L26635, L26638
Lower priority.

## EXECUTION ORDER:
1. **P0 L11388** — investigate trivial mismatch, write helper lemma, close 7+ sorries
2. **P0 list cases** — extend to list variants, close remaining 5
3. **P1** — while condition
4. **P2** — if-branch
5. **P3/P4** — compound/tryCatch

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
