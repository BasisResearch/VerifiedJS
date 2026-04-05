# proof — Close tryCatch_direct (L10122) and break/continue compounds

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~600MB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## STATUS: HasTryCatchInHead + decomposition DONE. Tasks 1-4 from previous prompt COMPLETE.

## TASK 1: Close tryCatch_direct (L10122) — MAIN TARGET

Line 10122: `| tryCatch_direct => sorry -- MAIN CASE: direct tryCatch simulation`

Context: `sf.expr = .tryCatch body_flat cp_flat cb_flat fin_flat` (from HasTryCatchInHead.tryCatch_direct).
normalizeExpr (.tryCatch body_flat cp_flat cb_flat fin_flat) k normalizes into ANF .tryCatch.

**ANF.step? on .tryCatch**: pushes catch handler to callStack, steps into body.
**Flat.step? on .tryCatch**: same — pushes catch handler, steps into body.

Approach:
1. `lean_goal` at L10122 to see exact proof state
2. `rename_i body_flat cp_flat cb_flat fin_flat` to name the tryCatch components
3. Unfold ANF.step? on .tryCatch in hstep_eq to get the body/catch/finally structure
4. Show Flat.step? on sf also steps into the body with matching semantics
5. Construct ANF_SimRel between the resulting states (body with catch frame on stack)
6. Use `lean_multi_attempt` to try tactics before editing

**Key**: The Flat and ANF tryCatch stepping should be structurally similar. The main work is threading the SimRel hypotheses through.

## TASK 2: Close break/continue compound cases (L11425, L11478) — SECONDARY

These are compound HasBreakInHead/HasContinueInHead cases (seq, let, call, etc.).
They require Flat.step? error propagation through compound expressions.

**Same root cause as all compound cases**: when break/continue appears inside a seq/let/call, Flat.step? steps the inner expression, not the outer break/continue. Need evaluation context lifting.

**Only attempt if Task 1 is done or blocked.**

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9800-9910 (if compound infrastructure) ONLY
- You work on L10122 and L11425/11478. DON'T touch L9800-9910.

## PRIORITY ORDER
1. tryCatch_direct (L10122) — THE most important sorry
2. break compound (L11425)
3. continue compound (L11478)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
