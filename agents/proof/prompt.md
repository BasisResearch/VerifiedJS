# proof — Close ANF expression cases + unblock CC for wasmspec

## FIRST ACTION (before anything else):
```bash
chmod g+w VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
This file is owned by you (proof) but wasmspec needs write access to apply hnoerr guards.
DO THIS IMMEDIATELY. wasmspec has been BLOCKED for 3+ hours because of this.

## RULES
- Edit: ANFConvertCorrect.lean (primary), ClosureConvertCorrect.lean (chmod only)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (14:05 Mar 30)
- ANF: 17 sorries. UNCHANGED from last hour. We need ACTUAL CLOSURES.
- Break/continue compound sub-cases: ALL 66 proved ✓
- hasBreakInHead/ContinueInHead helper theorems (L3935, L3951): sorry'd but used 33× each
- 7 depth-induction sorries (L3825, L3829, L3840, L3891, L3895, L3906, L3918)
- 8 expression-case sorries (L4036, L4038, L4040, L4060, L4062, L4064, L4066, L4068)

## PRIORITY 1: Close expression cases NOW (L4035-4068)

These have been sorry'd for hours. Each is independent. Work from easiest:

### `let` (L4036) — Current line numbers:
```
| «let» name rhs body =>
    sorry -- let-binding: evalComplex evaluates rhs, extends env, continues with body
```
Strategy: `rhs` is either a value or not.
- Value: `Flat.exprValue? rhs = some v`. Flat.step? evaluates to value, extends env with `v`, body continues. ANF.normalizeExpr `.let name rhs body` where rhs is value does `normalizeExpr body (k extended)`. Use IH.
- Not value: Flat.step? steps inner rhs. Use `step?_let_sub_step` or equivalent.
Use `lean_goal` at L4036 to see what you have in context. Then `lean_multi_attempt` with candidate tactics.

### `seq` (L4038) — Same pattern as let but simpler (no env extension)

### `if` (L4040) — After ANF, cond is trivial. Evaluate, branch.

### `throw` (L4060) — Structure already built (L4050-4060). Just need Flat steps.
The `all_goals sorry` at L4060 has 2 goals (ok/error from evalTrivial). For each:
- Construct Flat.Steps from sf producing matching trace
- Key: sf.expr should be normalizeExpr of `.throw arg`, which gives `.throw (trivial t)` after ANF
- Use `lean_goal` at L4060 to see exact goals

### `return` (L4064), `yield` (L4066), `await` (L4068) — Trivial arg evaluation

### `tryCatch` (L4062) — Hardest, do last

## PRIORITY 2: Partial proof of hasBreakInHead_flat_error_steps (L3935)
Decompose by structural induction on `HasBreakInHead`:
```lean
  induction h with
  | break_direct => -- trivial: Flat.step? on .break produces error event directly
    sorry
  | seq_left hsub ih => -- need: Flat.Steps from (.seq sub b) via context-stepping sub, then error propagation
    sorry
  | let_init hsub ih => -- same pattern through .let
    sorry
  | _ => sorry -- other compound cases need Fix D extension
```
Even proving `break_direct` + `seq_left` + `let_init` reduces the monolithic sorry to specific sub-cases.

## PRIORITY 3: Depth induction sorries — skip for now, lower impact

## VERIFICATION
- [ ] chmod g+w on CC FIRST
- [ ] Build passes: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- [ ] At least 2 sorries closed this run
- [ ] Log to agents/proof/log.md with sorry count before/after
