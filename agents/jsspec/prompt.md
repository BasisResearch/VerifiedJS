# jsspec — Close newObj sorries, then re-close consoleLog

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️⚠️⚠️ DO NOT TOUCH CCStateAgree ⚠️⚠️⚠️
The CCStateAgree-blocked sorries are PARKED. Your OWN analysis confirmed the invariant change would break 14 working cases. DO NOT WORK ON THEM.

## STATE: CC has 14 real sorry tokens.

## SORRY MAP (14 tokens):

### UNPROVABLE (3) — SKIP:
- L1507: forIn stub
- L1508: forOf stub
- L5144: getIndex string (Float.toString opaque)

### CCStateAgree BLOCKED (6) — PARKED:
- L3715: if-then
- L3738: if-else
- L6382: functionDef
- L6537: tryCatch finally
- L6608: tryCatch error (9/10 goals proved, only CCStateAgree remains)
- L6715: while_

### ACTIONABLE (5):
- **L4280**: consoleLog (`exact sorry`) — was "closed" but sorry remains! RE-CLOSE THIS.
- **L4498**: newObj f not a value
- **L4506**: newObj non-value arg
- **L3387**: captured var (multi-step gap)
- **L4292**: non-consoleLog call (needs FuncsCorr)

## YOUR TASKS (in priority order):

### TASK 1: Re-close consoleLog sorry at L4280

L4280 currently reads: `exact sorry /- Core_step?_call_consoleLog_flat_msg args argVals sc.env sc.heap sc.trace sc.funcs sc.callStack hallv -/`

The block comment shows what the proof SHOULD be but doesn't typecheck. Investigate the type mismatch:
1. Use `lean_goal` at L4280 to see the exact goal
2. Use `lean_hover_info` on `Core_step?_call_consoleLog_flat_msg` to see its type
3. The issue is likely dependent match normalization — use `show` to fix the goal type, or restructure to avoid dependent match on `hfvals`
4. Your previous fix attempt used `show Core.step? ... = some ...; exact Core_step?_call_consoleLog_flat_msg ...` — try that again or use `lean_multi_attempt` to find what works

### TASK 2: Close newObj sorries (L4498/L4506)

You already proved arrayLit all-values. newObj has similar structure.

For the ALL-VALUES sub-case:
- Same pattern as your arrayLit proof
- Both Core and Flat allocate, HeapInj via `alloc_both`
- CCStateAgree satisfied trivially when sub-exprs are all values

For the NON-VALUE sub-cases (L4498/L4506):
- Core allocates immediately regardless
- Flat needs to step f or arg first
- Check if this is the same structural issue as arrayLit non-value case

### TASK 3: Build FuncsCorr infrastructure for L4292

Only START if Tasks 1-2 are done.

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738, L6382, L6537, L6608, L6715 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
