# wasmspec — Close if compound + HasIfInHead sorries in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9485 (tryCatch step sim) and L9079-9084 (let compound)
- **YOU** work on L9367/9368 and L9440/9441 ONLY
- DO NOT touch lines 9060-9090 or 9475-9490

## STATUS: You analyzed if compound infrastructure last run. NOW CLOSE THE SORRIES.

## YOUR TARGETS (4 sorries)

| Line | What | Difficulty |
|------|------|------------|
| L9367 | if compound condition (true branch) — `| _ => sorry` | Medium |
| L9368 | HasIfInHead (true branch) — `all_goals sorry` | Medium |
| L9440 | if compound condition (false branch) — `| _ => sorry` | Medium |
| L9441 | HasIfInHead (false branch) — `all_goals sorry` | Medium |

## APPROACH: Use exfalso + normalizeExpr contradiction

Last run you identified these need "if normalizeExpr e k produces form X, flat machine can step e to match." But there may be a SIMPLER approach:

### For L9367/L9440 (compound condition):
Use `lean_goal` to see the proof state. The condition `c_flat` is not lit/var/this — it's a compound expression. But `normalizeExpr` of an `if` should produce a condition that is trivial (var or lit). So this case may be **impossible** — try:
```lean
| _ =>
  -- normalizeExpr produces trivial conditions for if
  -- so c_flat can only be lit or var, contradiction
  exfalso
  -- Use normalizeExpr_if_decomp or similar lemma
  sorry
```

Use `lean_local_search "normalizeExpr_if"` to find relevant lemmas about what normalizeExpr produces for if conditions.

### For L9368/L9441 (HasIfInHead compound):
These handle HasIfInHead constructors on compound sub-expressions. Most should be impossible because `normalizeExpr` eliminates nested if-in-head patterns. Try `exfalso` + contradiction from the normalization invariant.

Use `lean_multi_attempt` at L9368 with:
```
["exfalso; exact absurd hnorm (by simp)", "cases hif_head <;> simp_all", "all_goals (exfalso; sorry)"]
```

## TASK 1: Close L9367/9368 (true branch compound)
1. `lean_goal` at L9367 to see the exact state
2. Check if the compound condition case is actually reachable
3. If unreachable: `exfalso` + derive contradiction from normalizeExpr invariant
4. If reachable: use IH on the compound condition sub-expression

## TASK 2: Close L9440/9441 (false branch compound)
Same approach as Task 1 — the false branch is structurally identical.

## PRIORITY ORDER
1. L9367/9368 (true branch if compound) — solve the pattern
2. L9440/9441 (false branch if compound) — copy-paste solution

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
