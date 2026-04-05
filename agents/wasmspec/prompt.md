# wasmspec — Close 4 remaining sorries: trivialChain seq + seq_right

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~5GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING — BUILD COORDINATION
proof agent is ALSO building ANFConvertCorrect. Check before building:
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, DO NOT BUILD. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L8557-9940, L10030-10042, L12373-13761
- **YOU** own L10944-11532 ONLY (trivialChain/exotic zone)
- DO NOT touch lines outside your range

## GREAT WORK: Exotic catch-alls CLOSED! (-2 sorries)
You closed L11211 and L11532 (exotic catch-all cases for true/false). Only 4 sorries remain in your zone.

## YOUR 4 SORRIES (verified 19:05):

| Line | Category | Description |
|------|----------|-------------|
| L11053 | trivialChain seq (true) | Combine steps from helper + if branch step |
| L11104 | seq_right (true) | eval a + seq discard + IH on b |
| L11376 | trivialChain seq (false) | Same as L11053, false branch |
| L11425 | seq_right (false) | Same as L11104, false branch |

## CONCRETE APPROACH FOR L11053 (trivialChain seq, true branch)

I read the goal. You have:
- `a_tc b_tc : Flat.Expr` with `htc : isTrivialChain (a_tc.seq b_tc) = true`
- `hc_no_if : ¬HasIfInHead (a_tc.seq b_tc)`
- Need to step `.if (a_tc.seq b_tc) then_flat else_flat` to a state where expr normalizes to `then_`

**Step-by-step proof sketch:**

```lean
-- 1. isTrivialChain (.seq a b) = true implies both parts trivialChain
have htc_a : isTrivialChain a_tc = true := by simp [isTrivialChain] at htc; exact htc.1
have htc_b : isTrivialChain b_tc = true := by simp [isTrivialChain] at htc; exact htc.2
-- 2. Use trivialChain_eval_value to evaluate the whole seq condition to a value
obtain ⟨v_cond, evs_tc, hsteps_tc, hnoerr_tc, hobs_tc, hpres_tc⟩ :=
  trivialChain_eval_value (trivialChainCost (a_tc.seq b_tc)) (a_tc.seq b_tc)
    env heap trace funcs cs htc (le_refl _)
    (fun x hfx => hewf x (VarFreeIn.if_cond _ _ _ _ hfx))
-- 3. Lift through .if [·] then_flat else_flat context
obtain ⟨ws, hwsteps, hwexpr, hwenv, hwheap, hwfuncs, hwcs, hwtrace⟩ :=
  Steps_if_cond_ctx_b then_flat else_flat hsteps_tc
    (fun ev hev msg => by have := hnoerr_tc ev hev msg; exact absurd rfl this)
    hpres_tc
-- 4. Now sf' has expr = .if (lit v_cond) then_flat else_flat
-- 5. Wire up: env/heap/funcs/cs preserved, trace correct
-- 6. For normalizeExpr: .if (lit v_cond) then_flat else_flat K produces (if (.lit v_cond) then_ else_)
--    since lit is trivialChain. Connect back to hnorm.
-- 7. ExprWellFormed: straightforward from hewf
```

**Key insight**: `trivialChain_eval_value` does ALL the seq stepping internally (it handles seq case by induction). You don't need to manually step a→value then discard then b. Just call it on the whole `a_tc.seq b_tc`.

After getting Steps through if-cond context, the tricky part is proving the normalizeExpr condition. Look at how `if_cond` case at L11056-11073 (right above your sorry) does it — it uses `ih` on the condition. Your case doesn't have IH (it's trivialChain not HasIfInHead), so instead you need to show normalizeExpr of `lit v_cond` with K produces the right thing. Use:
```lean
simp [ANF.normalizeExpr, StateT.run, pure, Pure.pure, StateT.pure, Except.pure]
```
to simplify normalizeExpr of a literal.

### L11376 (false branch) — IDENTICAL approach, just use the false-branch theorem names.

## CONCRETE APPROACH FOR L11104 (seq_right, true branch)

You have: `.seq a b` where `HasIfInHead b` (not a), inside `.if`.
- `a` has no HasIfInHead → check if trivialChain
- Use `trivialChain_eval_value` on `a` to evaluate it
- Lift through `.seq [·] b` context → `.seq (lit v_a) b`
- One seq-discard step: `.seq (lit v_a) b → b` (silent)
- IH on `b` (since `HasIfInHead b` and `b.depth ≤ d`)

Look at how `seq_left` at L11080-11102 (right above you) does it — it's the mirror image. Copy that pattern but:
- Use `trivialChain_eval_value` on `a` instead of `ih` on `a`
- After getting to `b`, use `ih` on `b` since `HasIfInHead b`

### L11425 (false branch) — IDENTICAL approach.

## PRIORITY ORDER
1. L11053 + L11376 (trivialChain seq) — should be mechanical with the sketch above
2. L11104 + L11425 (seq_right) — mirror of seq_left

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
