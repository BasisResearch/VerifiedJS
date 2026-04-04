# jsspec — Close L3408 and L7787. Two easy wins.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 14 real sorries. Your targets: L3408 and L7787.

## TASK 1 — Close L3408 (Core.step preserves supported) — HIGHEST PRIORITY

L3408 is:
```lean
have hsupp' : sc'.expr.supported = true := sorry /- TODO: prove Core.step preserves supported -/
```

This is inside the forward simulation proof. `sc` stepped to `sc'` via `Core.step?`. We need `sc'.expr.supported = true` given `sc.expr.supported = true`.

### APPROACH: Write a standalone lemma above the sorry site.

You need to find `Core.step?` definition. Use `lean_local_search "Core.step?"` or `lean_hover_info` on it. Core.step? will have the same structure as Flat.step? — case split on `sc.expr`, then for each case show the resulting expression is `.supported = true`.

The `Core.Expr.supported` definition likely returns `false` for forIn/forOf and `true` for everything else (with recursive checks on sub-expressions). Check with `lean_hover_info` on `Core.Expr.supported`.

**CRITICAL**: The proof has the EXACT same structure as `NoNestedAbrupt_step_preserved` in ANFConvertCorrect.lean — case analysis on the expression, showing the property is preserved through each step.

```lean
private theorem Core_step_preserves_supported (sc sc' : Core.State) (ev : Core.TraceEvent)
    (hsupp : sc.expr.supported = true)
    (hstep : Core.step? sc = some (ev, sc')) :
    sc'.expr.supported = true := by
  obtain ⟨expr, ...⟩ := sc  -- destruct state
  simp only [Core.step?] at hstep
  cases expr with
  | lit v => simp at hstep  -- lit doesn't step
  | var name =>
    -- steps to .lit v; .lit.supported = true by definition
    simp [Core.Expr.supported]
    -- extract the stepped state from hstep, show expr is .lit
    sorry  -- fill in
  -- etc for each constructor
```

For each constructor:
1. `simp [Core.step?] at hstep` to unfold
2. Case split on value/non-value sub-expressions
3. Value case: result is usually `.lit` or a sub-expression from `hsupp`
4. Non-value case: result wraps the stepped sub-expression — use `Core.Expr.supported` inversion on `hsupp` to get sub-expression supported, apply IH (via WF induction on depth)

**Even if you can only close the simple cases and leave some sorry sub-cases, write the lemma and use it at L3408.** This structurally improves the proof.

Then replace L3408 sorry with:
```lean
have hsupp' : sc'.expr.supported = true := Core_step_preserves_supported sc sc' ev hsupp hcstep
```

## TASK 2 — Close L7787 (h_supp parameter) — QUICK WIN

L7787 is:
```lean
have h_supp : s.body.supported = true := sorry /- TODO: add h_supp param when EndToEnd.lean is updated -/
```

This is in `closureConvert_correct` (L7779). Fix:
1. Add `(h_supp : s.body.supported = true)` as a parameter to `closureConvert_correct`
2. Delete the sorry line at L7787
3. Find callers: use `lean_local_search "closureConvert_correct"` — likely called from EndToEnd.lean
4. Check EndToEnd.lean: `grep -n "closureConvert_correct" VerifiedJS/Proofs/EndToEnd.lean`
5. In EndToEnd.lean the caller should have `h_supported : js.body.supported = true` from the top-level theorem. Pass it as argument.
6. **BUT** you don't own EndToEnd.lean. Check if you can edit it or if someone else does.

Alternative if EndToEnd.lean is read-only: keep the sorry but add a comment that it just needs the parameter threaded. The jsspec agent IS allowed to edit CC.

**WAIT**: re-read the rules. You edit CC only. Check who owns EndToEnd.lean. If nobody owns it, just edit it — add `h_supp` argument at the call site.

## TASK 3 (ONLY AFTER 1-2): L3435 captured variable
Use `lean_goal` at L3435 to see the exact proof state. Determine if a 2-step simulation lemma is needed.

## DO NOT:
- Touch L4549, L4557 (semantic mismatch — compiler bug)
- Touch L6437 (functionDef — HeapInj blocked)
- Touch L5195 (unprovable)
- Touch L3764, L3787 (CCStateAgree architecture issue)
- Touch L6594, L6595, L6667 (CCStateAgree blocked)
- Touch L6775 (while_ CCState threading)
- Touch L4341 (FuncsCorr blocked)
- Edit ANFConvertCorrect.lean

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
