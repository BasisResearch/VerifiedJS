# wasmspec — Case B sorries + compound Await/Yield

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T15:30
- Total: 60 real sorries (ANF 45, CC 15).
- **step_error_isLit: FULLY PROVED (0 sorries!)**. tryCatch case closed by simp. GREAT WORK.
- **step_nonError: PROVED**. Your infrastructure work is paying off.
- proof agent is on second-position HasReturnInHead (L16490-16501).
- CC: All 15 blocked (jsspec confirmed).

## P0: Case B continuation sorries (L16433, L16489) — 2 sorries

These are in hasReturnInHead_return_steps, in the seq_right case. They handle:
- **Case B**: the return does NOT come from HasReturnInHead on sub-expression `a`, but from the continuation `K` applied after `a` evaluates to value.

Read 20 lines above L16433 and L16489 to see context. They follow from `normalizeExpr_return_none_or_k` / `normalizeExpr_return_some_or_k` rcases.

### The proof strategy for Case B:
1. Sub-expression `a` has NO HasReturnInHead (otherwise it would be Case A)
2. `a` is a "trivial chain" — it evaluates to a value in finite steps without errors
3. After `a` evaluates to value `v`, the seq steps once to produce `K(v)`
4. `K(v)` is then the normalizeExpr of continuation `b`, which has HasReturnInHead
5. By IH on `b` (or `K(v)`), this produces the required error trace

### What you need:
- A lemma: if `a` has no HasReturnInHead AND `a` is well-formed, then `a` evaluates to value (trivial chain terminates)
- Check if `trivialChain_terminates` or similar exists — use `lean_local_search "trivialChain"`
- The seq_right Case A proof (L16399-16431 for none, L16437-16487 for some) shows the first-position pattern
- Case B needs: Steps on `a` → value, then one step of seq, then IH on continuation

### Assessment first
Before writing code:
1. `lean_goal` at L16433 to see the exact goal
2. `lean_local_search "trivialChain"` to find existing infrastructure
3. `lean_local_search "terminates"` to find termination lemmas
4. Read 100 lines above L16433 for context (the seq_right match structure)

If the infrastructure doesn't exist, DOCUMENT what's needed and move to P1.

## P1: compound HasAwaitInHead (L16857) + HasYieldInHead (L17030) — 2 sorries

These are in `hasAwaitInHead_return_steps` and `hasYieldInHead_return_steps`. They follow the SAME pattern as HasReturnInHead compound cases. Check if the first-position infrastructure (ctx/error lemmas) exists for these.

Use lean_local_search:
- `lean_local_search "HasAwaitInHead"`
- `lean_local_search "HasYieldInHead"`

If these follow the same `Steps_compound_error_lift` pattern, they may be closable using the exact same approach as the HasReturnInHead cases. Even splitting the monolithic sorry into per-constructor cases (like was done for HasReturnInHead) would be progress.

## P2: Break/continue list cases (L4906, L6044) — 2 sorries

These are `makeEnv_values | objectLit_props | arrayLit_elems => sorry` in break/continue head-position theorems. Check if list-stepping infrastructure can close them.

## DO NOT WORK ON:
- L16490-16501 (second-position HasReturnInHead — proof agent is on this)
- L10664-L11035 (trivialChain zone — LSP timeout)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — Case B sorries + compound await/yield" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
