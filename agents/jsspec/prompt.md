# jsspec — Close CC call function case (L4090)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE (13:05): CC has 18 grep-sorry hits. Build PASSING.

## SORRY MAP (run `grep -n sorry` to get CURRENT lines):
```
PROVABLE (1 target):
  L4090  call function all-values ← YOUR ONLY TARGET

ALL OTHERS ARE BLOCKED — DO NOT TOUCH:
  L1507, L1508: forIn/forOf stubs (unprovable)
  L3211: captured var (needs HeapInj refactor)
  L3546: CCStateAgree if-then (blocked)
  L3570: CCStateAgree if-else x2 (blocked)
  L4290: newObj (blocked — heap + semantic mismatch)
  L4872: getIndex string (semantic mismatch)
  L5667: objectLit all-values (blocked — heap size)
  L5851: arrayLit all-values (blocked — heap size)
  L6030: functionDef (multi-step, blocked)
  L6198: tryCatch value+finally CCState (BLOCKED — CCState, NOT easy)
  L6213: tryCatch error catch (BLOCKED — CCState threading)
  L6318: while_ CCState (BLOCKED — CCState threading)
```

## CALL FUNCTION CASE (L4090) — CRITICAL ANALYSIS

**Goal state** (from lean_goal):
```
case ind.call.some.some.inl
-- Core side: sc.expr = .call (.lit (.function idx)) args
-- Flat side: sf.expr = .call (.lit (.closure idx 0)) (.lit .null) flatArgs
-- hallv : Core.allValues args = some argVals  (all args are values)
-- hstep : Flat.step? sf = some (ev, sf')
```

**What Flat.step? does for call with `.closure idx 0`**:
1. All args values → `valuesFromExprList? flatArgs = some flatArgVals`
2. Callee `.closure idx 0` → looks up `sf.funcs[idx]?` for funcDef
3. Binds params to args, envParam to `.null`, self-ref closure
4. Wraps body in tryCatch, pushes env to callStack
5. Returns `.silent` trace

**Use this existing theorem**: `Flat.step?_call_closure` in `VerifiedJS/Flat/Semantics.lean:1106`

**What Core.step? does for call with `.function idx`**:
1. Looks up `sc.funcs[idx]?` for FuncClosure
2. Binds params to args, captures closure env
3. Wraps body in tryCatch, pushes env to callStack
4. Returns `.silent` trace

**Use**: `Core.step_functionCall_exact` or similar in `VerifiedJS/Core/Semantics.lean:12728`

**KEY CHALLENGE**: Relating `sc.funcs[idx]` (Core FuncClosure) to `sf.funcs[idx]` (Flat FuncDef).
Search for `FuncCorr`, `funcsCorr`, or `CC_SimRel` to find the function table invariant.
The CC_SimRel or `closureConvert_step_simulation` suffices block should thread this.

**PROOF STRATEGY**:
1. Extract the Flat step result using `step?_call_closure` or manual unfolding
2. Construct Core step result
3. For the convertExpr obligation on bodies: the Core body converts to Flat body via closure conversion
4. For CCState: call enters new scope, so CCState from body conversion applies

### TACTIC PATTERNS (from non-function call case at L4011-L4039):
```lean
-- For constructing result:
let sc' : Core.State := ⟨resultExpr, newEnv, sc.heap,
  sc.trace ++ [.silent], newFuncs, sc.env :: sc.callStack⟩
refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· show Core.step? sc = some (.silent, sc')
  have hsc' : sc = { sc with expr := .call (.lit (.function idx)) args } := by
    obtain ⟨_, _, _, _, _, _⟩ := sc; simp only [] at hsc; subst hsc; rfl
  rw [hsc']; exact Core_step?_call_func ...
· simp [sc', htrace]
· exact hinj  -- heap unchanged
· -- EnvCorrInj for new body env
· -- remaining invariants
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- ALL sorries except L4090 — they are all blocked (see sorry map above)

## WORKFLOW:
1. `grep -n sorry` to find CURRENT line numbers (they shift!)
2. `lean_goal` at target line (LSP takes ~3 min, just WAIT)
3. Study nearby proved cases for patterns
4. Build after each change
5. Move to next target

## CRITICAL: LOG YOUR WORK
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`

## TARGET: Close call function case (L4090) → CC grep from 18 to 17
