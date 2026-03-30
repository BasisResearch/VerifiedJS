# wasmspec — Close CC sorries (BOTTOM half)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## CRITICAL: Your last run applied hnoerr guards — great work! Now PROVE them.
The 16 `have hnoerr : ∀ msg, t ≠ .error msg := by sorry` you added all need actual proofs.

## STATUS (17:05 Mar 30)
- CC: 44 sorries. 20 are hnoerr/hev_noerr. You handle BOTTOM half.
- Fix D: APPLIED ✓
- hnoerr guards: APPLIED ✓ (sorry'd — need proofs NOW)

## YOUR TASK: PROVE hnoerr sorries (BOTTOM half of file)

### How to prove each hnoerr sorry

At each sorry, context looks like:
```lean
match hm : Flat.step? { sf with expr := subexpr } with
| some (t, sa) =>
    have hnoerr : ∀ msg, t ≠ .error msg := by sorry
    have heq := Flat_step?_XXX_step sf ... t sa hm hnoerr
    rw [heq] at hstep; simp at hstep; ...
```

If `t = .error msg`, then `Flat_step?_XXX_error` applies instead, giving a different `sf'` shape (`.lit .undefined` instead of the wrapped expression). This contradicts `hstep` which expects the non-error shape.

### Proof pattern
```lean
intro msg heq
subst heq
-- Now t = .error msg. Apply the _error variant theorem:
rw [Flat_step?_XXX_error sf ... msg sa hm] at hstep
-- hstep becomes contradictory (wrong sf' shape)
simp at hstep  -- or: exact absurd hstep (by simp)
```

Use `lean_goal` at each sorry FIRST to see which expression form you're in, then find the matching `_error` theorem name with `lean_local_search "step?_XXX_error"`.

### Your targets (BOTTOM half — jsspec handles top):
L4643, L4718, L4886, L4976, L5054, L5153, L5343, L5550, L5689, L5777

### Also target these non-hnoerr sorries if time permits:
- L5069: ExprAddrWF objectLit propagation
- L5168: ExprAddrWF arrayLit propagation
- L5116: CCState threading convertPropList

### DO NOT TOUCH:
- L1369/1370 (forIn/forOf stubs — unprovable by design)
- L5298 (functionDef), L5389 (tryCatch), L5420 (while CCState) — complex
- ANFConvertCorrect.lean — proof agent owns this
- hnoerr sorries above L4643 — jsspec is handling those

### Workflow
1. Start with L5777 (bottom-most, likely simplest context)
2. `lean_goal` at sorry line
3. Identify parent expression form
4. `lean_local_search "step?_FORM_error"` to find the _error theorem
5. `lean_multi_attempt` with the proof pattern above
6. Edit file, build after every 3-4 closures
7. Work UPWARD: L5777 → L5689 → L5550 → ...

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- DO NOT edit ANFConvertCorrect.lean
- LOG to agents/wasmspec/log.md

## TARGET: Close at least 5 hnoerr sorries → CC from 44 to ≤39
