# jsspec — Close L3384 (Core_step_preserves_supported remaining cases)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS UPDATE
- **L4333 is CLOSED** ✓ — consoleLog case now uses `exact hcore`. Great work!
- **L7791 is CLOSED** ✓ — proof agent handled it.
- **L3384** is the new target: `| _ => sorry -- remaining cases need case analysis on step?`

## CC has 13 actual sorry statements. Your target: L3384.

## TASK 1 — Complete Core_step_preserves_supported (L3384)

L3384 is inside `Core_step_preserves_supported` at line 3372. The theorem proves that `Core.step?` preserves the `.supported` property. Base cases (lit, var, forIn, forOf, yield, await) are done.

The wildcard `| _ => sorry` needs expanding into per-constructor cases. Most cases follow this pattern:

1. `unfold Core.step? at hstep` (or `simp [Core.step?] at hstep`)
2. Split on sub-expression value checks
3. For value results: `simp [Flat.State.expr, Core.Expr.supported]` or `simp_all`
4. For step results: `simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]` then use `hsupp` which after unfold gives sub-expression supported

**Strategy**: Replace `| _ => sorry` with explicit cases. Start with the easy ones:

```lean
  | this => simp [Core.step?] at hstep; split at hstep <;> simp_all [Core.Expr.supported]
  | «break» _ => simp [Core.step?] at hstep; simp_all [Core.Expr.supported]
  | «continue» _ => simp [Core.step?] at hstep; simp_all [Core.Expr.supported]
  | «return» _ => unfold Core.step? at hstep; split at hstep <;> (try simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]) <;> simp_all [Core.Expr.supported]
  | throw _ => unfold Core.step? at hstep; split at hstep <;> (try simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]) <;> simp_all [Core.Expr.supported]
  | unary _ _ => unfold Core.step? at hstep; split at hstep <;> (try simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]) <;> simp_all [Core.Expr.supported]
  | typeof _ => unfold Core.step? at hstep; split at hstep <;> (try simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]) <;> simp_all [Core.Expr.supported]
  | assign _ _ => unfold Core.step? at hstep; split at hstep <;> (try simp at hstep; obtain ⟨_, rfl⟩ := hstep; simp [Core.State.expr, Core.Expr.supported]) <;> simp_all [Core.Expr.supported]
```

For compound constructors (seq, let, if, binary, call, etc.):
1. Use `lean_hover_info` on `Core.Expr.supported` to see its definition
2. Use `lean_goal` at the sorry position to see what's needed
3. `unfold Core.step? at hstep; unfold Core.Expr.supported at hsupp`
4. Split on sub-expression values
5. For sub-step cases: the result has the same outer constructor but with a stepped sub-expression — supported is preserved because the outer constructor's supported recurses

If too many cases are hard, use `| _ => sorry` for the hard ones but close as many as possible. Even replacing 1 wildcard sorry with 5 proved + 3 sorry is progress.

**IMPORTANT**: Use `lean_multi_attempt` at L3384 to quickly test if `simp_all [Core.step?, Core.Expr.supported, Core.State.expr]` or `aesop` closes any cases.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
