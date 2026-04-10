# wasmspec — L17873 + L17926 are NOW UNBLOCKED. Close them.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean ONLY at L17850-17930

## MEMORY: ~3.5GB free. USE LSP ONLY — no builds.

## CONCURRENCY
- proof agent is fixing remaining ~20 build errors in L9752-10832
- jsspec fixes CC Flat.step? breakage
- **YOU** work on L17873 and L17926 ONLY

## STATUS: Flat.step? NOW PROPAGATES ERRORS

The proof agent changed Flat.step? so that `.seq a b` with `.error msg` from `a` now propagates the error directly instead of wrapping in `.seq (.lit .undefined) b`. Same for `.let` and `.assign`.

**THIS MEANS**: L17873 (break compound) and L17926 (continue compound) — which were blocked by "Flat.step? wraps results in compound contexts instead of propagating errors" — should now be CLOSABLE.

## ===== P0: Close L17873 and L17926 =====

### L17873 — break compound error propagation
```lean
sorry  -- break compound
```

1. Run `lean_goal` at L17873 to see the current proof state
2. The goal should now be solvable because Flat.step? propagates `.error msg` through seq/let/assign directly
3. The proof pattern: show that after the break produces an error event, the surrounding compound expression (seq/let/assign) propagates it directly (no dead code execution)
4. Key lemma: `step?_seq_error` or similar (defined by proof agent in ANFConvertCorrect.lean)

### L17926 — continue compound error propagation
Same pattern as L17873 but for continue.

## ===== P1: Re-check L16538, L16556, L16559 (tryCatch) =====

After the error propagation fix, re-examine these with `lean_goal`. They were blocked by "callStack propagation + counter alignment" but the error propagation change may have shifted the proof obligations.

## ===== P2: If time permits, explore if_branch sorries =====

There are 24 if_branch sorries (L14148-L15697) that were classified as "blocked by K-mismatch". If L17873/L17926 go quickly, check if any of these are now tractable.

## WORKFLOW
1. **FIRST**: `echo "### $(date -Iseconds) Starting run — L17873+L17926 unblocked" >> agents/wasmspec/log.md`
2. `lean_goal` at L17873 and L17926
3. Attempt proofs based on error propagation
4. If closable, close them. If still blocked, document exactly what's needed.
5. Check L16538/16556/16559 goals
6. **LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
