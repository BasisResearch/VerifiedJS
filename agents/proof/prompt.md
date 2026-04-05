# proof — Close tryCatch_direct (L10127) and ANF infrastructure

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

## STATUS: ANF has 27 sorries. hasAbruptCompletion/NoNestedAbrupt infrastructure partially done.

## TASK 1: Close tryCatch_direct (L10127) — MAIN TARGET

Line 10127: `| tryCatch_direct => sorry -- MAIN CASE: direct tryCatch simulation`

Context: `sf.expr = .tryCatch body_flat cp_flat cb_flat fin_flat` (from HasTryCatchInHead.tryCatch_direct).

**ANF.step? on .tryCatch**: pushes catch handler to callStack, steps into body.
**Flat.step? on .tryCatch**: same — pushes catch handler, steps into body.

Approach:
1. `lean_goal` at L10127 to see exact proof state
2. Unfold ANF.step? on .tryCatch in hstep_eq to get body/catch/finally structure
3. Show Flat.step? on sf also steps into body with matching semantics
4. Construct ANF_SimRel between resulting states (body with catch frame on stack)
5. Use `lean_multi_attempt` to try tactics before editing

**Key**: Flat and ANF tryCatch stepping should be structurally similar. Main work is threading SimRel hypotheses through.

## TASK 2: Close hasAbruptCompletion_step_preserved / NoNestedAbrupt_step_preserved (L10131+)
If these are still sorry'd from your previous infrastructure work, complete them. They are needed by anfConvert_steps_star.

## TASK 3: break/continue compound (L11430, L11483) — ONLY if Task 1 done

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9800-9912 (if compound infrastructure) ONLY
- You work on L10127 and L10131+. DON'T touch L9800-9912.

## PRIORITY ORDER
1. tryCatch_direct (L10127) — THE most important sorry
2. hasAbruptCompletion/NoNestedAbrupt infrastructure
3. break/continue compound (L11430/11483)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
