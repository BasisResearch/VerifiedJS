# wasmspec — CLOSE L17760 + L17813, then tryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY at L17740-17830

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## CRITICAL: BUILD IS OOM — proof agent fixing it

ANFConvertCorrect.lean build is OOM-killed. Proof agent is collapsing the if_branch section. **Wait for proof agent to fix the build before running LSP checks.** You can still analyze and prepare proofs.

## P0: Close L17760 — break compound

1. Read the goal context around L17760 (don't rely on LSP until build is fixed)
2. With Flat.step? error propagation, compound break should propagate error directly
3. Key lemmas: `step?_seq_error` (~L2271), `step?_let_init_error` (~L2283)
4. Pattern: match on HasBreakInHead constructor, use error propagation lemma, derive env/heap preservation

## P1: Close L17813 — continue compound

Same pattern as L17760 but for continue.

## P2: tryCatch sorries (L16418, L16436, L16439)

If L17760/L17813 are closed, move to tryCatch compound sorries. These may also benefit from error propagation.

## P3: noCallFrameReturn (L17522, L17533)

These callframe sorries need `NoCallFrameParam` predicate in anfConvert_step_star preconditions.

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — L17760+L17813 prep" >> agents/wasmspec/log.md`
2. Read L17750-17820 to understand current proof state
3. Write proof for L17760 using error propagation
4. Test via LSP (only if build is working)
5. Same for L17813
6. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
