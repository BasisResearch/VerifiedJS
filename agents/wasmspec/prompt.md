# wasmspec — Close CC value sub-cases (share CC file with jsspec)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! CRITICAL: YOUR PROCESS HAS BEEN STUCK FOR 19+ HOURS !!
**You have wasted 60+ HOURS total in while loops. DO NOT LOOP.**

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

## STATE (10:05): CC has 17 grep-sorry-hits. Build PASSING. jsspec is also editing CC file.

## SORRY MAP:
```
SKIP (unprovable/blocked): 11
  L1507, L1508: forIn/forOf stubs
  L3160: captured var (needs multi-step getEnv)
  L3479, L3501(x2): CCStateAgree (blocked)
  L4775: getIndex string mismatch
  L5557: objectLit all-values (BLOCKED by heap size)
  L5740: arrayLit all-values (BLOCKED by heap size)
  L5918: functionDef (multi-step makeClosure+makeEnv)
  L6039: CCState while_ (blocked)

PROVABLE: 3 (jsspec may be working on these)
  L4010: call function all-values (jsspec's PRIMARY target)
  L4207: newObj
  L6008: tryCatch
```

## FIRST ACTION:
```bash
grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean
```
Check what jsspec already closed, then pick up remaining targets.

## CRITICAL: objectLit/arrayLit/functionDef are ALL BLOCKED
- objectLit/arrayLit: HeapInj_alloc_both requires equal heap sizes (blocked)
- functionDef: multi-step (makeClosure + makeEnv evaluation), not single-step sim

## YOUR TARGETS (pick up whatever jsspec didn't finish):
1. **newObj** (~L4207) — similar to call case
2. **tryCatch** (~L6008) — hardest, complex multi-step

### For newObj: Check for `Flat.step?_newObj*` and `Core.step?_newObj*` lemmas:
```bash
grep -n "step?_newObj\|step_newObj" VerifiedJS/Flat/Semantics.lean VerifiedJS/Core/Semantics.lean VerifiedJS/Proofs/ClosureConvertCorrect.lean
```

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
- functionDef — multi-step, skip

## CRITICAL: LOG YOUR WORK
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`

## TARGET: Close at least 1 CC sorry → reduce CC grep count
