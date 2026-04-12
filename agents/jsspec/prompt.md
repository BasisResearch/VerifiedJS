# jsspec — CLOSE CCStateAgree SORRIES (6 remaining)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-12T10:05
- CC: **12 real sorry instances** (previous count of 8 missed 4 inline sorries).
- FLAT since 09:05. No progress in the last hour.
- Previous runs were undercounting: sorries embedded in expressions like `sorry⟩` and `sorry,` were missed.

## CORRECTED SORRY MAP (12 total):

**CCStateAgree (6)** — YOUR TARGETS:
- **L7325**: `sorry⟩` — inline, if-true branch, CCStateAgree gap (else_ conversion state included)
- **L7351**: `sorry,` — inline, adjacent to L7325, same CCStateAgree issue
- **L10237**: `sorry⟩` — inline, rw + CCStateAgree for body value with hst'_eq
- **L10240**: `sorry` — CCStateAgree + tryCatch body-value with finally
- **L10314**: `sorry` — CCStateAgree, st vs st_a accounting for tryCatch conversion state
- **L10430**: `sorry` — CCStateAgree, while_ lowers to .if cond (.seq body (.while_ cond body)) (.lit .undefined)

**Multi-step (3)** — DO NOT TOUCH:
- L6877, L8182, L8193 — architectural, requires fundamental design change

**Unclassified (2)** — DO NOT TOUCH:
- L7974, L10080

**AXIOM (1)** — UNPROVABLE:
- L8833 — getIndex string semantic mismatch

## APPROACH

### For L7325 + L7351 (if-branch CCStateAgree pair):
These are inline in a tuple expression. Use `lean_goal` at each position to see what's needed. The issue is that `st'` includes the else_ conversion state but the witness needs to agree only with the taken branch.

Check if `convertExpr_state_mono` exists — it may let you show state monotonicity past the discarded branch.

### For L10237 (body-value with hst'_eq):
The surrounding code has `by rw [hst'_eq]; sorry`. You need CCStateAgree after rewriting with hst'_eq. Check what hst'_eq provides.

### For L10240 (tryCatch + finally):
Similar to L10237 but with a `some fin` finally clause adding another nested conversion.

### For L10314 (tryCatch CCStateAgree):
Comment at L10308-10312 has proof skeleton:
```
cases finally_ with
| none => use st1 as witness, convertExpr_state_mono, scope_irrelevant
| some fin => analogous with nested convertExpr state
```

### For L10430 (while_ CCStateAgree):
while_ expansion creates duplicated sub-expressions. Same CCStateAgree gap.

### EXECUTION ORDER:
1. `lean_goal` at L10314 first — has a proof skeleton
2. Then L10430 — similar pattern
3. Then L7325/L7351 pair
4. Then L10237/L10240 pair

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
