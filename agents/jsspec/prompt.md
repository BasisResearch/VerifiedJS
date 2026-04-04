# jsspec — Close newObj sorries, then build FuncsCorr infrastructure

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️⚠️⚠️ DO NOT TOUCH CCStateAgree ⚠️⚠️⚠️
The 6 CCStateAgree-blocked sorries (if-then, if-else, tryCatch×2, while_, functionDef) are PARKED.
Your OWN analysis confirmed the invariant change would break 14 working cases.

## STATE: CC has 14 sorry tokens. Unchanged from last run.

## SORRY MAP (14 tokens):

### UNPROVABLE (3) — SKIP:
- L1507: forIn stub
- L1508: forOf stub
- L5144: getIndex string (Float.toString opaque)

### CCStateAgree BLOCKED (7) — PARKED:
- L3715: if-then
- L3738: if-else (2 sorries on one line)
- L6382: functionDef
- L6537: tryCatch finally
- L6608: tryCatch error (9/10 goals proved, only CCStateAgree remains)
- L6715: while_

### ACTIONABLE (4):
- **L4498**: newObj f not a value
- **L4506**: newObj non-value arg
- **L3387**: captured var (multi-step gap)
- **L4292**: non-consoleLog call (needs FuncsCorr)

## YOUR TASKS (in priority order):

### TASK 1: Close newObj sorries (L4498/L4506)

You already proved arrayLit all-values. newObj has similar structure.

Read L4480-4510 to understand the proof state. The key issue: Core allocates immediately (newObj with all values produces the object in one step) but Flat may need to step sub-expressions first.

For the ALL-VALUES sub-case:
- Same pattern as your arrayLit proof
- Both Core and Flat allocate, HeapInj via `alloc_both`
- CCStateAgree satisfied trivially when sub-exprs are all values

For the NON-VALUE sub-cases (L4498/L4506):
- Core allocates immediately regardless
- Flat needs to step f or arg first
- Can you show that when Core steps, the Flat simulation catches up via multi-stepping?
- If this is structurally the same as arrayLit non-value case, reuse that approach

### TASK 2: Build FuncsCorr infrastructure for L4292

L4292 is the non-consoleLog function call sorry. It needs a correspondence between `sf.funcs[idx]` and `sc.funcs[idx]`.

Steps:
1. Read the CC_SimRel definition (grep for `CC_SimRel` or the simulation relation structure)
2. Check if there's any existing function correspondence invariant
3. If not, define one:
```lean
def FuncsCorr (sf_funcs : Array Flat.FuncDef) (sc_funcs : Array Core.FuncDef) : Prop :=
  sf_funcs.size = sc_funcs.size ∧
  ∀ i (h : i < sf_funcs.size),
    (sf_funcs[i]).params = (sc_funcs[i]'(by omega)).params ∧
    (sf_funcs[i]).body = convertExpr (sc_funcs[i]'(by omega)).body ...
```
4. Add FuncsCorr to the simulation relation
5. Prove it's preserved by each stepping case

This is a LARGE task. Only START it if Task 1 is done. Even just DEFINING FuncsCorr and adding it to the relation (with sorry for preservation) unblocks L4292.

### TASK 3: Investigate captured var (L3387)

Read around L3380-3395. The sorry needs closure environment object correspondence. Check if the existing EnvCorr + HeapInj gives enough to prove this. If the captured variable is in the closure's environment object on the heap, HeapInj should map it.

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5144 getIndex string — UNPROVABLE
- L3715, L3738, L6382, L6537, L6608, L6715 — CCStateAgree blocked, PARKED

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
