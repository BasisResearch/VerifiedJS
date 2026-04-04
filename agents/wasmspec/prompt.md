# wasmspec — Close compound throw/return/await/yield sorries OR help with hasAbruptCompletion

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2.9GB available right now.
- You CAN edit ANFConvertCorrect.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS: Last run was ANALYSIS ONLY with 0 closures. That is NOT acceptable.

You spent an entire run analyzing and writing no code. The sorry count did NOT change. We need CODE CHANGES.

## STRATEGY CHANGE: You are no longer doing analysis. You are writing proofs.

### Option A: Fix the call/newObj/getEnv "have bindings" issue

The hasAbruptCompletion_step_preserved theorem (L9383) and NoNestedAbrupt_step_preserved (L9662) both have proof attempts in block comments. The remaining sorry cases (call, newObj, getEnv, objectLit, tryCatch) all fail because `split at hstep` doesn't work when `Flat.step?` uses `have` bindings.

**Your job**: Figure out how to handle `have` bindings in `Flat.step?` unfolding.

1. Use `lean_hover_info` on `Flat.step?` to see its definition
2. Look at how `call`, `newObj`, `getEnv` cases work in `Flat.step?`
3. Try alternatives to `split at hstep`:
   - `simp only [Flat.step?] at hstep`
   - `dsimp only [Flat.step?] at hstep`
   - `unfold Flat.step? at hstep; dsimp at hstep`
   - Extract the `have` bindings manually with `match` on the step result

4. Test with `lean_multi_attempt` at the call sorry position

If you crack this, it unblocks 10 sorries across both theorems.

### Option B: Close compound sorries (7 total)

If Option A is too hard:
- **L8523**: throw compound
- **L8673, L8676**: return compound
- **L8846, L8849**: await compound
- **L9000, L9003**: yield compound

Use `lean_goal` at each sorry. If they all need "eval context stepping" infrastructure, pick the SIMPLEST one and write the proof.

### Option C: tryCatch step sim (L9375)
Another standalone sorry. Use `lean_goal` to assess.

## DO NOT just analyze. WRITE CODE. Close at least 1 sorry.

## DO NOT EDIT L9377-9662 (proof agent region) unless doing Option A

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
