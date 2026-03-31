# jsspec — Close CC call + non-heap sub-cases

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE (07:47): CC has 18 grep-sorry hits, build PASSES.
- **Supervisor closed L2019 + L2032** (Flat_step?_call_value_step_arg and Flat_step?_call_nonclosure). -2 sorries!
- proof and wasmspec STILL STUCK (while loops). You're the only active agent.

## CRITICAL FINDING: objectLit/arrayLit all-values are BLOCKED
- Both sides allocate on heap. HeapInj is currently HeapCorr (prefix relation).
- `HeapInj_alloc_both` requires `ch.objects.size = fh.objects.size` — but Flat heap
  can be BIGGER due to env objects from prior closure conversions.
- Until HeapInj is upgraded to real injection (L2988 sorry), objectLit/arrayLit
  all-values CANNOT be proved. **DO NOT waste time on L4900 or L5083.**

## SORRY MAP (current after supervisor fixes):
```
L1504  forIn stub (SKIP — unprovable)
L1505  forOf stub (SKIP — unprovable)
L2939  HeapInj refactor staging (SKIP)
L2992  captured var (SKIP — needs HeapInj)
L3311  CCStateAgree if-then (SKIP — blocked)
L3333  CCStateAgree if-else x2 (SKIP — blocked)
L3835  call all-values ← YOUR TARGET (highest priority)
L3837  call non-value arg ← YOUR TARGET
L3838  newObj ← YOUR TARGET (heap alloc — may be blocked like objectLit)
L4406  getIndex string (SKIP — semantic mismatch)
L4578  setIndex value sub-case ← YOUR TARGET
L4900  objectLit all-values (SKIP — BLOCKED by heap size)
L5083  arrayLit all-values (SKIP — BLOCKED by heap size)
L5261  functionDef ← YOUR TARGET
L5351  tryCatch ← YOUR TARGET (hardest)
L5382  CCState while_ (SKIP — blocked)
```

## YOUR PROVABLE TARGETS (5 sorries):
1. **L3835 — call callee-is-value, all args values** (HIGHEST PRIORITY)
   - When cv is not a function: both sides return .undefined (no heap alloc, similar to getProp primitive)
   - When cv IS a function: need to set up call frame, complex but no heap alloc
   - Use the now-proved `Flat_step?_call_nonclosure` for non-function case
2. **L3837 — call non-value arg** (standard IH pattern like getProp non-value)
   - Step the first non-value arg using IH, same as the `| none =>` case for getProp
3. **L4578 — setIndex value sub-case** (may need heap for object mutation)
4. **L5261 — functionDef** (complex — involves addFunc, makeEnv, makeClosure)
5. **L5351 — tryCatch** (hardest, skip if short on time)

### HOW TO PROVE L3835 (call all-values):

Context: `hlit : f = .lit cv` already proved, `hallv : Core.allValues args = some argVals`.

Strategy: Case split on `cv`:
- **Non-function** (null, undefined, bool, number, string, object): Both Core and Flat return .undefined.
  ```lean
  -- Core side: Core.step?_call_nonfunction or similar
  -- Flat side: Flat_step?_call_nonclosure (NOW PROVED!)
  -- Result: refine ⟨injMap, sc', ⟨?_⟩, ...⟩ like getProp primitive case
  ```
- **Function idx**: Core looks up function, creates call frame. Flat has `.closure idx 0` and looks up function too.
  This sub-case is complex — skip if too hard, focus on non-function first.

### HOW TO PROVE L3837 (call non-value arg):
Follow the exact pattern of getProp `| none =>` case (~L3950-3968):
1. Get `convertExprList_firstNonValueExpr_some` for the Flat firstNonValueExpr
2. Get `Flat.step?` decomposition via `Flat_step?_call_value_step_arg` (NOW PROVED!)
3. Apply IH on the first non-value arg
4. Construct Core result using `Core_step?_call_arg_step` or similar

### TACTIC PATTERNS (from proved cases):
```lean
-- For constructing result (9 obligations + CCState):
refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· show Core.step? sc = some (ev, sc')    -- Core step
· simp [sc', htrace]                     -- trace
· exact hinj                             -- HeapInj
· exact henvCorr                         -- EnvCorr
· exact henvwf                           -- EnvWF
· exact hheapvwf                         -- HeapVWF
· simp [sc', noCallFrameReturn]          -- noCallFrameReturn
· simp [sc', ExprAddrWF, ValueAddrWF]    -- ExprAddrWF
· refine ⟨st, st, ?_, ⟨rfl, rfl⟩, ...⟩  -- CCState
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs — unprovable
- CCState threading sorries — architecturally blocked
- getIndex string mismatch — Flat/Core semantic mismatch
- objectLit/arrayLit all-values — BLOCKED by heap size issue

## WORKFLOW:
1. `grep -n sorry` to find CURRENT line numbers (they shift!)
2. `lean_goal` at target line (LSP takes ~3 min, just WAIT)
3. Study nearby proved cases for patterns
4. Build after each change
5. Move to next target

## CRITICAL: LOG YOUR WORK
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`

## TARGET: Close L3835 (non-function sub-case) + L3837 → CC grep from 18 to ~16
