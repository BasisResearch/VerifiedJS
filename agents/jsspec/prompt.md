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
- **L4333 is CLOSED** ✓
- **L7791 is CLOSED** ✓
- **L3384** is the target: `| _ => sorry -- remaining cases need case analysis on step?`
- CC has 13 actual sorries. Your target: L3384.

## TASK 1 — Complete Core_step_preserves_supported (L3384)

L3384 is inside `Core_step_preserves_supported` at line 3372. The wildcard `| _ => sorry` needs expanding into per-constructor cases.

### Strategy: Replace `| _ => sorry` with explicit constructor cases.

**Easy cases** (single sub-expression, same pattern):
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

**Medium cases** (compound with 2-3 sub-expressions): seq, let, if, binary, deleteProp, getProp, getIndex, setProp, setIndex, while_, labeled. For these:
1. `unfold Core.step? at hstep; unfold Core.Expr.supported at hsupp`
2. Split on `exprValue?` of first sub-expression
3. Value case: result is simpler → `simp_all` or use `hsupp` components
4. Step case: result has same constructor with one stepped sub-expression → supported from `hsupp` components

**Hard cases** (list args): call, newObj, objectLit, arrayLit. These need list induction via `firstNonValueExpr`. Try `sorry` on these if they don't yield quickly.

### Efficient approach:
1. Use `lean_multi_attempt` at L3384 to quickly test if any single tactic closes it
2. Replace `| _ => sorry` with all explicit constructors
3. Start with easy cases — get as many as possible proved
4. Use `| _ => sorry` as fallback for hard cases

**IMPORTANT**: Use `lean_hover_info` on `Core.Expr.supported` (in Core/Syntax.lean or similar) to see its full definition. This tells you which constructors return `true` and how supported recurses.

Even replacing 1 wildcard sorry with 10 proved + 5 sorry is great progress.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
