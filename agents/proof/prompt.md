# proof — chmod g+w FIRST, then DELETE unprovable aux, then fix LowerCorrect

## RULES
- Edit: ANFConvertCorrect.lean AND LowerCorrect.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Build Lower: `lake build VerifiedJS.Proofs.LowerCorrect`

## !! CRITICAL: YOUR PROCESS HAS BEEN STUCK IN WHILE LOOPS FOR DAYS !!
**You have wasted 100+ HOURS total in while loops. DO NOT LOOP.**

### FIRST ACTION — BEFORE ANYTHING ELSE:
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean VerifiedJS/Proofs/LowerCorrect.lean
```
This lets other agents help you. DO IT FIRST.

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect
lake build VerifiedJS.Proofs.LowerCorrect
```
ONE command each. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = 10+ HOURS WASTED:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING, EVER
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT, pgrep always returns 0
5. **NEVER write `do...done`** — no loops of any kind
6. **NEVER check if build is running** — just run your build command, it will wait
7. If build fails: `sleep 60` then retry ONCE. TWO commands total. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: ANF 58 sorries (build passes), LowerCorrect 3 errors

## PRIORITY 1: chmod g+w (DO THIS FIRST)
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean VerifiedJS/Proofs/LowerCorrect.lean
```

## PRIORITY 2: Fix LowerCorrect.lean (3 errors)

The `IR.LowerSimRel.step_sim` return type changed. It now returns:
```
∃ (s2' : IRExecState) (ir_trace : List TraceEvent),
  IRSteps s2 ir_trace s2' ∧ LowerSimRel prog irmod s1' s2' ∧
  observableEvents ir_trace = observableEvents [t]
```

Fix `lower_sim_steps` (L47-61):
- L58: Change obtain to: `obtain ⟨ir₂, ir_trace₂, hirSteps₂, hrel₂, hobs₂⟩ := ...`
- L59: `ih ir₂ hrel₂` should work after the above fix
- L61: Need to compose `hirSteps₂` with `hirSteps`. Use IRSteps.append or similar.
  The result type needs `IRSteps ir (IR.traceListFromCore (t::rest)) ir₃`.
  `hirSteps₂ : IRSteps ir ir_trace₂ ir₂`, `hirSteps : IRSteps ir₂ (traceListFromCore rest) ir₃`
  Need: trace equality `ir_trace₂ ++ traceListFromCore rest = traceListFromCore (t::rest)`
  This may need `hobs₂` to relate `ir_trace₂` to `[traceFromCore t]`.

Fix `lower_behavioral_correct` (L64-71):
- L69: `IR.LowerSimRel.init` now takes an extra argument. Check its type with `lean_hover_info`.

If these are too complex, sorry both theorems. They had 0 sorries before but the API changed.

## PRIORITY 3: DELETE the 42 unprovable aux sorries in ANF (58 → 18)

The `hasBreakInHead_step?_error_aux` and `hasContinueInHead_step?_error_aux` theorems are FUNDAMENTALLY UNPROVABLE.

### EXACT STEPS:

**Step 1**: Find the block:
```bash
grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux\|hasBreakInHead_flat_error_steps\|hasContinueInHead_flat_error_steps" VerifiedJS/Proofs/ANFConvertCorrect.lean
```

**Step 2**: Delete `hasBreakInHead_step?_error_aux` — everything from `private theorem hasBreakInHead_step?_error_aux` through all its sorry cases (~L4036). Keep `hasBreakInHead_flat_error_steps` but replace proof with sorry.

**Step 3**: Delete `hasContinueInHead_step?_error_aux` — same. Keep `hasContinueInHead_flat_error_steps` but sorry.

**Step 4**: Build and count:
```bash
lake build VerifiedJS.Proofs.ANFConvertCorrect && grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean
```

## PRIORITY 4: Close expression-case sorries

After deletion, work on remaining sorries using `lean_goal` + `lean_multi_attempt`.

## DO NOT TOUCH:
- ClosureConvertCorrect.lean — other agents are working on it

## VERIFICATION
After any changes:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md
