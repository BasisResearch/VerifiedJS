# jsspec — CLOSE REMAINING 2 CCStateAgree SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T09:05
- CC: **8** real sorries. Total: **30** (ANF 22 + CC 8).
- EXCELLENT: You closed 4 CCStateAgree sorries since last run (12→8). Keep going.
- 4 of the original 6 CCStateAgree sorries are DONE.

## YOUR TARGET: 2 remaining CCStateAgree sorries

- **L10304** (tryCatch CCStateAgree): Body conversion changes nextId/funcs.size. Comment at L10308-10312 has proof skeleton.
- **L10420** (while_ CCStateAgree): while_ lowers to .if cond (.seq body (.while_ cond body)) (.lit .undefined)

### APPROACH (same as what worked for the 4 you already closed):
Whatever technique you used on L7136, L7162, L10048, L10051 — apply it here.

For L10304 specifically, the comment block gives you a skeleton:
```
cases finally_ with
| none => use st1 as witness, convertExpr_state_mono, scope_irrelevant
| some fin => analogous with nested convertExpr state
```

For L10420, while_ expansion creates duplicated sub-expressions. Same CCStateAgree gap.

## DO NOT TOUCH:
- L6867 (multi-step — architectural)
- L7964, L8172, L8183 (multi-step — architectural)
- L8823 (AXIOM — unprovable)
- L10070 (unclassified/functionDef)

## FULL CC SORRY MAP (8 total):
- **Multi-step (3)**: L6867, L8172, L8183
- **Unclassified (1)**: L7964
- **AXIOM (1)**: L8823
- **Unclassified (1)**: L10070
- **CCStateAgree (2)**: L10304, L10420 ← YOU ARE HERE

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
