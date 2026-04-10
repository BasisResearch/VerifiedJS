# wasmspec — CLOSE L17760 + L17813 (break/continue compound)

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY at L17740-17830

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY
- proof agent works on L11772, L11923, L11929, L12106, L12264
- jsspec fixes CC callers
- **YOU** work on L17760 and L17813 ONLY

## STATUS: Flat.step? NOW PROPAGATES ERRORS — THESE ARE UNBLOCKED

The proof agent changed Flat.step? so that compound expressions (seq/let/assign) propagate errors directly instead of wrapping. The key change:
- OLD: `.seq (.break label) b` → Flat.step? returns `(.error msg, {expr := .seq (.lit .undefined) b})`
- NEW: `.seq (.break label) b` → Flat.step? returns `(.error msg, {expr := .lit .undefined})` (no dead code)

**This means L17760 (break compound) and L17813 (continue compound) are NOW CLOSABLE.**

## ===== P0: Close L17760 — break compound =====

1. Run `lean_goal` at L17760 to see the current proof state
2. The goal should ask for `∃ sf' evs, Flat.Steps sf evs sf' ∧ ...` where the break fires inside a compound expr
3. With error propagation, the compound expr now propagates the error directly
4. Key lemmas (already in the file):
   - `step?_seq_error` (~L2271): seq with error event propagates directly
   - `step?_let_init_error` (~L2283): let with error event propagates directly
5. Pattern match on which `HasBreakInHead` constructor gives the compound case
6. Use the appropriate error propagation lemma
7. Show env/heap preservation (trivial since error propagation skips dead code)

### Proof sketch for seq_left case:
```lean
-- sf.expr = .seq break_expr b, break_expr has break
-- step? fires break_expr → (.error msg, sa)
-- step?_seq_error: .seq break_expr b → (.error msg, {expr := sa.expr, ...})
-- env/heap preserved since no dead code executes
```

## ===== P1: Close L17813 — continue compound =====

Same pattern as L17760 but for continue. The proof structure should be nearly identical.

## ===== P2: If time permits, check L12415, L12427 (while) =====

These while condition sorries may also be affected by the error propagation change.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run — L17760+L17813 unblocked by error propagation" >> agents/wasmspec/log.md`
2. `lean_goal` at L17760
3. Attempt proof using error propagation lemmas
4. If closable, close it. If not, document EXACTLY what's blocking.
5. Do same for L17813
6. **LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
