# wasmspec — YOU HAVE BEEN RUNNING FOR 8+ HOURS WITH ZERO OUTPUT

## STATUS: 18 Wasm sorries. UNCHANGED since 2026-03-28T23:00.

Your last run started at 23:00 on Mar 28. It is now 07:30 on Mar 29.
8.5 hours. Zero sorry reduction. Zero log entries. This is unacceptable.

## CRITICAL: DO NOT attempt large proofs. Small increments ONLY.

The 18 Wasm sorries break down into:

### EASY (try these first):
- **L6864** `return (some t)`: Template exists at L6824-6863 (return none). Follow same pattern.
- **L6867** `yield arg delegate`: Similar control-flow signal pattern
- **L6870** `await arg`: Similar control-flow signal pattern

### MEDIUM:
- **L6798** `let`: Need `LowerCodeCorr.let_inv` inversion
- **L6810** `if cond then_ else_`: Need `LowerCodeCorr.if_inv` inversion
- **L6873** `labeled label body`: Need label frame push
- **L6876** `break label`: Signal pattern
- **L6879** `continue label`: Signal pattern

### HARD (skip these):
- **L6806** `seq`: 1:N stepping framework needed
- **L6813** `while_`: Loop induction
- **L6816** `throw`: Exception handling
- **L6819** `tryCatch`: Complex control flow
- **L10857** `call`: Multi-frame, blocked by hframes_one
- **L10912, L10916** `call` sub-cases: Same blocker
- **L10919** `callIndirect`: Same blocker

## YOUR ONE JOB: Close `return (some t)` at L6864

1. `lean_goal` at L6864 col 9
2. The pattern from return-none (L6824-6863):
   - Invert `LowerCodeCorr` to get the IR code shape
   - Show ANF steps to `.trivial .litUndefined` or error
   - Show IR takes matching step(s)
   - `traceFromCore (.error "return:...") = .silent` by `native_decide`
   - Build new `LowerSimRel`
3. The `t` is an `ANF.Trivial` — need to evaluate it first, then return
4. Check `LowerCodeCorr` for a `return_some` constructor: `lean_hover_info` on `LowerCodeCorr`

If return-some is blocked (no constructor), try break/continue (L6876/6879) instead.

## MEMORY/TIME CONSTRAINTS
- MAX 15 lines of new proof per sorry
- `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
- If build > 5 min, sorry it back IMMEDIATELY
- LOG EVERY 30 MINUTES even if no progress
- If you're stuck for >1 hour on one sorry, MOVE TO THE NEXT ONE

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md — LOG FIRST LINE WITHIN 60 SECONDS OF STARTING
