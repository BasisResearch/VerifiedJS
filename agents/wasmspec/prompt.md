# wasmspec — Case B sorries + compound Await/Yield

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T16:05
- Total: 58 real sorries (ANF 46, CC 12). DOWN 2 from last run.
- jsspec closed 3 Or.inr sorries — great progress on CC side.
- proof agent targeting second-position (L16494-16505).
- You own Case B + compound await/yield.

## P0: Case B continuation sorries (L16437, L16493) — 2 sorries

These are in hasReturnInHead_return_steps, in the seq_right case. They handle:
- **Case B**: return does NOT come from HasReturnInHead on sub-expression `a`, but from continuation `K` applied after `a` evaluates to value.

### Updated line numbers (verified 16:05):
- L16437: Case B for `none` arg case (in seq_right)
- L16493: Case B for `some arg_t` case (in seq_right)

### The proof strategy for Case B:
1. Sub-expression `a` has NO HasReturnInHead (otherwise it would be Case A)
2. `a` is a "trivial chain" — it evaluates to a value in finite steps without errors
3. After `a` evaluates to value `v`, the seq steps once to produce `K(v)`
4. `K(v)` is then the normalizeExpr of continuation `b`, which has HasReturnInHead
5. By IH on `b` (or `K(v)`), this produces the required error trace

### What you need:
- A lemma: if `a` has no HasReturnInHead AND `a` is well-formed, then `a` evaluates to value (trivial chain terminates)
- Check if `trivialChain_terminates` or similar exists — use `lean_local_search "trivialChain"`
- The Case A proof (L16440-16493) shows the first-position pattern — Case B extends it

### Assessment first
Before writing code:
1. `lean_goal` at L16437 to see the exact goal
2. `lean_local_search "trivialChain"` to find existing infrastructure
3. `lean_local_search "terminates"` to find termination lemmas
4. Read 100 lines above L16437 for context

If the infrastructure doesn't exist, DOCUMENT what's needed and move to P1.

## P1: compound HasAwaitInHead (L16863) + HasYieldInHead (L17036) — 2 sorries

These are in `hasAwaitInHead_return_steps` and `hasYieldInHead_return_steps`. Check if the same `Steps_compound_error_lift` + ctx/error lemma pattern works.

Use lean_local_search:
- `lean_local_search "HasAwaitInHead"`
- `lean_local_search "HasYieldInHead"`

## P2: Break/continue list cases (L4906, L6044) — 2 sorries

These are `makeEnv_values | objectLit_props | arrayLit_elems => sorry` in break/continue head-position theorems.

## DO NOT WORK ON:
- L16494-16505 (second-position HasReturnInHead — proof agent is on this)
- L10690-L11061 (trivialChain zone — LSP timeout)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — Case B sorries + compound await/yield" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
