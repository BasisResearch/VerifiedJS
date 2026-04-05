# proof — Close tryCatch_direct (L10127) — infrastructure is DONE, now PROVE IT

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~485MB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## STATUS: ANF has 27 sorries. Your HasTryCatchInHead infrastructure is DONE. Now close the sorry.

## TASK 1: Close tryCatch_direct (L10127) — YOU BUILT THE INFRA, NOW CLOSE IT

Line 10127: `| tryCatch_direct => sorry -- MAIN CASE: direct tryCatch simulation`

You already proved in last run:
- HasTryCatchInHead definition + HasTryCatchInHead_not_value
- normalizeExpr_tryCatch_or_k (via strong induction on depth)
- normalizeExpr_tryCatch_implies_hasTryCatchInHead
- Wired into normalizeExpr_tryCatch_step_sim with generalize hsfe trick
- Split into tryCatch_direct + compound

Now for tryCatch_direct:
1. `lean_goal` at L10127 to see exact proof state
2. sf.expr = .tryCatch body_flat cp_flat cb_flat fin_flat (from HasTryCatchInHead.tryCatch_direct)
3. **ANF.step? on .tryCatch**: pushes catch handler to callStack, steps into body
4. **Flat.step? on .tryCatch**: same — pushes catch handler, steps into body
5. Construct ANF_SimRel between resulting states (body with catch frame on stack)
6. This should be STRUCTURALLY STRAIGHTFORWARD since both Flat and ANF handle tryCatch the same way

**Key**: Use `lean_multi_attempt` at L10127 to try: `simp [Flat.step?, ANF.step?] at *`, `unfold Flat.step? ANF.step? at hstep_eq ⊢`, etc.

## TASK 2: Close compound tryCatch (L10128)
After L10127 is done: `| _ => sorry -- compound cases`
These are expressions where tryCatch is nested in head (via seq/let/etc). May need eval context lifting like the if compound cases.

## TASK 3: break/continue compound (L11430, L11483) — ONLY if Tasks 1-2 done

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9800-9912 (if compound) AND may work on general eval context lifting
- You work on L10127-10128. DON'T touch L9800-9912.

## PRIORITY ORDER
1. tryCatch_direct (L10127) — CLOSE IT THIS RUN
2. compound tryCatch (L10128)
3. break/continue compound (L11430/11483)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
