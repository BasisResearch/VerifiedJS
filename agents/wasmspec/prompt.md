# wasmspec — Close CC call sub-cases (share with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! ABSOLUTE RULE: NEVER USE WHILE/UNTIL LOOPS !!
**YOU HAVE WASTED 40+ HOURS STUCK IN WHILE LOOPS. YOUR LAST 5 SESSIONS DID ZERO WORK.**

### RULES — VIOLATION MEANS ANOTHER WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop**
4. `lake serve` is PERMANENT. `pgrep -x lake` will ALWAYS return 0.
5. To build: just run `lake build VerifiedJS.Proofs.ClosureConvertCorrect` directly
6. If build fails: ONE `sleep 60`, then retry ONCE. If fails again, skip.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has 18 sorry-grep-hits, build PASSES.
- Supervisor closed 2 helper lemmas (Flat_step?_call_value_step_arg, Flat_step?_call_nonclosure)
- objectLit/arrayLit all-values are BLOCKED by heap size issue (HeapCorr prefix ≠ equal sizes)
- jsspec is actively working on call cases

## FIRST ACTION: Check what jsspec already closed
```bash
grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
Then pick up whatever jsspec DIDN'T finish.

## CRITICAL: objectLit/arrayLit all-values are BLOCKED
HeapInj_alloc_both requires equal heap sizes. HeapCorr only guarantees ≤.
Flat heap can be bigger from env objects. DO NOT attempt L4900 or L5083.

## PROVABLE TARGETS (pick up whatever jsspec didn't finish):
1. **call all-values** (~L3835) — case split on cv, non-function returns .undefined
2. **call non-value arg** (~L3837) — standard IH pattern
3. **setIndex value** (~L4578)
4. **functionDef** (~L5261) — complex state changes
5. **tryCatch** (~L5351) — hardest

### PROOF PATTERN for call non-function (from getProp primitive ~L3930):
```lean
let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
  sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· -- Core step: Core.step?_call_nonfunction or unfold
· simp [sc', htrace]
· exact hinj
· exact henvCorr
· exact henvwf
· exact hheapvwf
· simp [sc', noCallFrameReturn]
· simp [sc', ExprAddrWF, ValueAddrWF]
· refine ⟨st, st, ?_, ⟨rfl, rfl⟩, by subst hst; exact ⟨rfl, rfl⟩⟩
  simp [sc', Flat.convertExpr, Flat.convertValue]
```

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns
- forIn/forOf stubs — unprovable
- CCState sorries — architecturally blocked
- getIndex string mismatch — Flat/Core semantic mismatch
- objectLit/arrayLit all-values — BLOCKED by heap size

## CRITICAL: LOG YOUR WORK
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`

## TARGET: Close at least 2 value sub-cases → reduce CC sorry count
