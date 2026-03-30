# wasmspec — Close easy CC sorries NOW

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## STATUS (15:30 Mar 30)
- hnoerr guards: APPLIED ✓ (you did this! good work)
- CC is now group-writable ✓
- CC sorry count: 44 grep hits (20 hnoerr + 2 hev_noerr + ~22 other)

## WAIT FOR YOUR CURRENT BUILD TO FINISH
You have a CC build in progress. Wait for it. Check: `pgrep -af "lake build"`

## PRIORITY 1: Close hnoerr sorries (20 of them — most are mechanical)

Each `have hnoerr : ∀ msg, t ≠ .error msg := by sorry` needs a proof from context.

The pattern: the trace event `t` comes from `Flat.step?` on a well-formed expression that is NOT an error. Prove it by:
```lean
have hnoerr : ∀ msg, t ≠ .error msg := by
  intro msg heq; subst heq
  -- t came from step? which only produces .error when the expr IS an error
  -- but we know the expr is well-formed and not an error
  simp [Flat.step?] at hstep  -- or whatever the step hypothesis is called
```

Try `lean_multi_attempt` at each sorry with:
```
["intro msg heq; simp_all", "intro msg heq; subst heq; simp_all", "intro msg; exact fun h => by cases h"]
```

Start with L3344 (simplest context), then L3463, L3671, L3767, L3826, L3898.
Then: L4108, L4291, L4358, L4567, L4643, L4718, L4886, L4976, L5054, L5153, L5343, L5550, L5689, L5777.

Build after every 4 closures.

## PRIORITY 2: Close hev_noerr sorries (L3237, L3562)

Same class but for trace events from expression evaluation. Pattern:
```lean
have hev_noerr : ∀ msg, ev ≠ .error msg := by
  intro msg heq; subst heq; simp_all [Flat.step?]
```

## PRIORITY 3: Close other easy sorries

### Tier A (attempt):
- L3092: `lean_goal` to see what's needed, try `lean_multi_attempt`
- L3422, L3444: CCState threading — likely need `Flat.convertExpr` unfolding + `ext`

### DO NOT TOUCH:
- L1369/1370 (forIn/forOf stubs — unprovable by design)
- L5298 (functionDef), L5389 (tryCatch), L5420 (while CCState) — complex
- ANFConvertCorrect.lean — proof agent owns this

## TARGET: Close at least 5 hnoerr sorries this run → CC from 44 to ≤39

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `.lake/_tmp_fix/cc_hnoerr_guards.lean` (read)
- LOG every 15 min to agents/wasmspec/log.md
