# wasmspec — Prove step?_preserves_funcs + close ANF step sim sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~3.8GB available right now.
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Flat: `lake build VerifiedJS.Flat.Semantics`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## STATUS: GREAT WORK fixing all if_step_sim errors! Zero errors in L1-9400 of ANF. You also added step?_preserves_funcs stub.

## TASK 1: PROVE step?_preserves_funcs (Flat/Semantics.lean L2041-2043) — HIGHEST PRIORITY

**NOTE**: proof agent is ALSO assigned this. Whoever gets it first wins. Check if it's still sorry before starting:
```bash
grep -n "step?_preserves_funcs" VerifiedJS/Flat/Semantics.lean
```

If still sorry, prove it:
```lean
theorem step?_preserves_funcs (sf : Flat.State) (ev : Core.TraceEvent) (sf' : Flat.State)
    (h : step? sf = some (ev, sf')) : sf'.funcs = sf.funcs := by
  unfold step? at h
  -- step? is a big match on sf.expr. Every branch either returns none or
  -- constructs {s with expr := ..., env := ..., heap := ..., trace := ...}
  -- without setting funcs. So sf'.funcs = sf.funcs.
  --
  -- Try these approaches in order:
  -- 1. simp + split:
  split at h <;> simp_all [pushTrace, allocFreshObject]
  -- 2. If goals remain after split, each one is: extract sf' from h, show .funcs unchanged
  all_goals { try { simp only [Option.some.injEq, Prod.mk.injEq] at h; obtain ⟨-, rfl⟩ := h; rfl } }
```

Use `lean_multi_attempt` at L2043 with:
```
["unfold step? at h; split at h <;> simp_all [pushTrace, allocFreshObject]",
 "unfold step? at h; cases sf.expr <;> simp_all [pushTrace, allocFreshObject]",
 "simp [step?] at h; aesop"]
```

Add `set_option maxHeartbeats 800000 in` before the theorem if needed.

Build: `lake build VerifiedJS.Flat.Semantics`

## TASK 2: Close L9050 (let step sim in ANF)

```lean
sorry -- Need characterization of what produces .let, flat simulation
```

Use `lean_goal` at L9050 to see the exact proof state. The pattern:
- ANF has `.let name init body` with `exprValue? init = none`
- ANF.step? steps init to get sa'
- Flat should also step the normalized init

Key: `lean_hover_info` on normalizeExpr for the `.let` case. The normalization of `.let name init body k` should produce something like `normalizeExpr init (fun init' => .let name init' (normalizeExpr body k))`.

## TASK 3: Fix hasAbruptCompletion_step_preserved objectLit/arrayLit (pre-existing errors ~L9839+)

wasmspec log says these are pre-existing errors in hasAbruptCompletion_step_preserved. The break/continue compound cases at L9851-9859 (eval context list) + L9863/9916 have issues with pushTrace patterns.

Use `lean_diagnostic_messages` at line 9860 to see what the actual errors are. Likely needs the same fix pattern you used for the earlier cases: replace `by simp [hasAbruptCompletion]` with hypothesis names + pushTrace_expand.

## TASK 4: Close L9140, L9152 (while step sim) — IF TIME

These need multi-step Flat simulation:
- L9140: while condition value — transient form not normalizeExpr-compatible
- L9152: condition-steps — Flat desugars while→if, needs 2-step simulation

## PRIORITY ORDER
1. step?_preserves_funcs (check if still sorry first) — quick, unblocks proof agent
2. L9050 (let step sim)
3. L9839+ (objectLit/arrayLit hasAbruptCompletion errors)
4. L9140, L9152 (while, harder)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
