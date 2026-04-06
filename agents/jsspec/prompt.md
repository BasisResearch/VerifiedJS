# jsspec — Finish list case investigation + CC unblock

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.

## MEMORY: ~800MB free. USE LSP ONLY.

## ===== K-MISMATCH CONFIRMED =====

The second-position sorries AND the list case "no labeled" sub-cases are blocked by K-mismatch. After stepping preceding list elements to values, the continuation changes (trivialOfFlat changes), making the body different from the hypothesis. This is UNSATISFIABLE.

**Your 5 "no labeled" sub-cases (L10248, L10297, L10328, L10360, L10391) are BLOCKED.** Do not invest more time trying to prove them.

## ===== YOUR NEW PRIORITY =====

### P0: ClosureConvertCorrect.lean cleanup (12 actual sorries)

Since ANF list cases are blocked, pivot to CC. The 12 CC sorries need architectural support:

Check the CC sorries by running:
```
grep -nw "sorry" VerifiedJS/Proofs/ClosureConvertCorrect.lean | grep -v "^[0-9]*:.*--.*sorry"
```

For each sorry:
1. `lean_goal` to see the exact proof state
2. Classify: is it architecturally blocked (HeapInj refactor, CCStateAgree) or provable now?
3. For provable cases: attempt proof
4. For blocked cases: document what infrastructure is missing

### P1: Document findings from list case investigation

Write a brief summary to agents/jsspec/log.md documenting:
- Which list sub-cases are blocked by K-mismatch
- Which (if any) first-position sub-cases were successfully proved
- Your partial proofs are good work — document them clearly

## CONCURRENCY
- proof agent owns L11638+ in ANFConvertCorrect.lean (compound cases)
- wasmspec owns L13901+ and L14996+ in ANFConvertCorrect.lean (if_branch)
- **YOU** own ClosureConvertCorrect.lean AND L10248-10391 in ANFConvertCorrect.lean

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
