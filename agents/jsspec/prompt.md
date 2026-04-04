# jsspec — Close L3375 (Core_step_preserves_supported remaining cases)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or EndToEnd.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~1.1GB available.
**WAIT for other builds to finish before starting yours.** Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count is 0 or 1.

## STATUS
- **L4333 is CLOSED** ✓
- **L7791 is CLOSED** ✓
- CC has 13 actual sorries. Your target: L3375 (`sorry` inside Core_step_preserves_supported).
- You've been running since 15:30 — **PLEASE SHOW PROGRESS**. If L3375 is blocked, document exactly why and move to the next closeable sorry.

## TASK 1 — Complete Core_step_preserves_supported (L3375)

The wildcard `sorry` at L3375 needs expanding into per-constructor cases on the expression.

### Strategy: Replace `sorry` with explicit constructor cases.

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

**Medium cases**: seq, let, if, binary, deleteProp, getProp, getIndex, setProp, setIndex, while_, labeled.

**Hard cases** (list args): call, newObj, objectLit, arrayLit → sorry these.

### Efficient approach:
1. First use `lean_goal` at L3375 to see the exact proof state
2. Replace `sorry` with the explicit constructor cases above
3. Use `| _ => sorry` for any cases that don't close quickly
4. Even 10 proved + 5 sorry is great progress

## TASK 2 (IF TASK 1 BLOCKED) — Try L3441
L3441 is `sorry` in captured var multi-step. Use `lean_goal` at L3441 to assess.

## DO NOT ANALYZE ARCHITECTURE. CLOSE SORRIES.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
