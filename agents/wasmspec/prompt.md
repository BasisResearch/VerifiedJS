# wasmspec — Close CC value sub-cases (share with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! CRITICAL: YOUR PROCESS HAS BEEN STUCK FOR 18+ HOURS !!
**PID 2750345 has been in `while pgrep -f "lake build"` since yesterday 14:30.**
This is the WORST case yet. You have wasted 60+ HOURS total in while loops.

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```
That's it. ONE command. No waiting, no checking, no loops.

### ABSOLUTE RULES — VIOLATION = ANOTHER WASTED SESSION:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT, pgrep always matches itself
5. **NEVER write `do...done`** — no loops of any kind
6. **NEVER check if build is running** — just run your build command
7. If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC has ~17 grep-sorry-hits. Build should be PASSING (jsspec may have changes).

**SUPERVISOR CHANGES** (during 09:05 run):
- Added 8 Flat/Core setIndex helper lemmas (after getIndex helpers section)
- Expanded setIndex value sorry (old L4583) into full proof with 3 sub-cases
- jsspec working on call all-values + call non-value arg

## FIRST ACTION:
```bash
grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
Check what jsspec already closed, then pick up remaining targets.

## CRITICAL: objectLit/arrayLit all-values are BLOCKED
HeapInj_alloc_both requires equal heap sizes. HeapCorr only guarantees ≤.
Flat heap can be bigger from env objects. DO NOT attempt objectLit/arrayLit all-values.

## PROVABLE TARGETS (pick up whatever jsspec didn't finish):
1. **newObj** — similar pattern to call
2. **functionDef** — complex state changes (addFunc, makeEnv, makeClosure)
3. **tryCatch** — hardest, skip if short on time

### PROOF PATTERN for non-function call (from getProp primitive):
```lean
let sc' : Core.State := ⟨.lit .undefined, sc.env, sc.heap,
  sc.trace ++ [.silent], sc.funcs, sc.callStack⟩
refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
· -- Core step
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
