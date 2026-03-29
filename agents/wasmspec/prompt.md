# wasmspec — RETURN SOME IS YOUR ONLY TARGET

## STATUS: 18 Wasm sorries. You proved return-none last run. Good.

## The return-some case (L6864) is the natural next step.

## PRIORITY 0: Prove step_sim for `return (some t)` at L6864

You already proved `return none` (L6824-6863). The `return (some t)` case at L6864 follows similar structure:

1. Use `lean_goal` at L6864 to see the exact goal
2. `t` is a `ANF.Trivial`, so it has a concrete value
3. ANF step: evaluates `t` to a value `v`, produces `.error ("return:" ++ valueToString v)`
4. IR code: from `LowerCodeCorr.return_some_inv`, should be `argCode ++ [return_]`
5. `traceFromCore (.error ("return:" ++ s)) = .silent` — you already proved this simp lemma

The key difference from `return none`:
- `t` is a trivial expr that evaluates immediately (ANF.Trivial → value in 0 steps)
- Need `LowerCodeCorr.return_some` constructor or inversion
- IR needs to execute argCode (evaluate t) then return_

If `LowerCodeCorr` doesn't have a `return_some` constructor, check with `lean_hover_info` on `LowerCodeCorr`.

## PRIORITY 1: If return-some is blocked, triage ALL 18 sorries

Read 5 lines around each sorry. Write one line per sorry:
```
L6798: [blocked/easy/medium] - [reason]
```
Log this triage. Pick the easiest unblocked sorry.

## MEMORY CONSTRAINTS
- MAX 20 lines of new proof per sorry
- `lake build VerifiedJS.Wasm.Semantics` after every edit
- If build > 5 minutes, sorry it back
- Do NOT unfold large definitions
- Use `decide`, `omega`, `rfl`, `exact`, `native_decide` — simple tactics only

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
## LOG: agents/wasmspec/log.md — LOG FIRST, PROVE SECOND
