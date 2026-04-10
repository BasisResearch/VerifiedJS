# wasmspec — CLOSE TRYCATCH + LABELED BRANCH SORRIES

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS
- BUILD PASSES. LSP available.
- Cat A break/continue closed (good work).
- Cat B (28 cases) blocked on error propagation (proof agent is adding it).
- ANF: 43 sorries. CC: 15. Total: 58.

## P0: ANALYZE AND CLOSE LABELED_BRANCH SORRIES (L9865-L11000)

There are ~18 sorries in the `normalizeExpr_labeled_branch_step` area (L9865-L11000). These are the LARGEST cluster. Analyze them:

1. Read L9865-L11000 to understand the proof structure
2. Categorize which sorries are:
   - (a) Simple tactic failures (wrong simp lemmas, missing unfold) — FIX THESE
   - (b) Blocked by error propagation — LEAVE
   - (c) Blocked by other architectural issues — DOCUMENT

Focus on (a). Even closing 3-4 simple ones is valuable. The comments suggest:
- L10288: "trivialChain passthrough doesn't apply" — read context, may need different approach
- L10515: "call_args: labeled in args list" — may need list induction lemma
- L10517/L10519: "funcE/envE anonymous variable order mismatch" — this is a rename_i issue, potentially fixable

## P1: TRYCATCH SORRIES (L13950, L13968, L13971)

3 tryCatch sorries:
- L13950: tryCatch body-error — "lifting body steps through tryCatch context"
- L13968: tryCatch body-step — "callStack propagation + counter alignment"
- L13971: compound cases — deferred

Read L13900-L13980 context. Assess if body-error (L13950) is closable — it may just need a step?_tryCatch lemma.

## P2: WHILE SORRIES (L12336, L12348)

2 while sorries. These may be simpler than they look. Read context.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — labeled_branch + tryCatch analysis" >> agents/wasmspec/log.md`
2. Read L9865-L11000, categorize sorries
3. Close what you can with LSP verification
4. Read L13900-L13980, assess tryCatch
5. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
