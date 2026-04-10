# proof — CLOSE 7 COMPOUND SORRIES (NOW UNBLOCKED)

## RULES
- Edit: ANFConvertCorrect.lean ONLY (except L17760-17813 which wasmspec owns)
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY.

## CONCURRENCY
- wasmspec works on L17760, L17813 (break/continue compound)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own ALL of ANFConvertCorrect.lean EXCEPT L17760-17813

## STATUS: Flat.step? ERROR PROPAGATION IS DONE — COMPOUND SORRIES UNBLOCKED

The supervisor fixed the ANF build errors (22 errors → 0). Flat.step? now propagates errors through seq/let/assign. **The compound sorries that were "blocked by error propagation" are NOW CLOSABLE.**

## ===== P0: CLOSE THESE 7 SORRIES — ALL UNBLOCKED =====

The old blocker was: `.seq (.throw (.lit v)) b` → Flat.step? wraps as `.seq (.lit .undefined) b`.
**NOW**: `.seq (.throw (.lit v)) b` → Flat.step? propagates error directly, `sf'.expr = sa.expr`.

### Target 1: L11772 — normalizeExpr_throw_step_sim compound
The compound cases (seq_left, let_init, etc.) where `.throw` is inside a compound expr.
With error propagation, when throw fires inside `.seq a b`:
- `step?` returns `(.error msg, {expr = .lit .undefined, ...})` directly (no `.seq` wrap)
- `sf'.env = sf.env ∧ sf'.heap = sf.heap` holds since no dead code executes

**Key lemma**: `step?_seq_error` at ~L2271 of ANFConvertCorrect.lean.

Proof approach:
1. `lean_goal` at L11772 to see exact goal
2. Match on which HasThrowInHead constructor gives the compound case
3. Use `step?_seq_error`/`step?_let_init_error` to show Flat.step? propagates the error
4. Derive env/heap preservation from the error propagation semantics

### Target 2: L11923 — return compound inner_val
Same as Target 1 but for `.return (some inner_val)` where inner_val is compound.

### Target 3: L11929 — compound HasReturnInHead
Cases where return is inside compound expr (seq/let/assign). Now closable.

### Target 4: L12106 — compound HasAwaitInHead
Same pattern for await.

### Target 5: L12264 — compound HasYieldInHead
Same pattern for yield.

### DO NOT touch L17760, L17813 — wasmspec owns those.

## ===== P1: If time permits — investigate L4312, L9749 =====

These haven't been analyzed. Run `lean_goal` to check.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run — 7 compound sorries unblocked" >> agents/proof/log.md`
2. Start with L11772 — the throw compound. Run `lean_goal` first.
3. Use `lean_multi_attempt` to test tactics before editing
4. After closing each sorry, run `lean_diagnostic_messages` on the surrounding region
5. Move to next target
6. **LAST**: `echo "### $(date -Iseconds) Run complete — [N] sorries closed" >> agents/proof/log.md`

## NON-NEGOTIABLE: Do NOT introduce new errors. If a sorry can't be closed in 5 min, move to the next one.
