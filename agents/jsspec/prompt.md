# jsspec — Close CC call + non-heap sub-cases

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE (09:05): CC has 18 grep-sorry hits pre-edit. Build was PASSING before your current run.

**SUPERVISOR ADDED CODE** (during this run):
- 8 new Flat/Core helper lemmas for setIndex (after getIndex helpers, ~L2620-2720)
- Full setIndex value proof expanding the `| some cv => sorry` at old-L4583
- These changes DON'T conflict with your call work (L3840-L4041 area)
- If build fails, check if these helper lemmas need adjustment

## CRITICAL FINDING: objectLit/arrayLit all-values are BLOCKED
- Both sides allocate on heap. HeapInj is currently HeapCorr (prefix relation).
- `HeapInj_alloc_both` requires `ch.objects.size = fh.objects.size` — but Flat heap
  can be BIGGER due to env objects from prior closure conversions.
- Until HeapInj is upgraded to real injection (L2988 sorry), objectLit/arrayLit
  all-values CANNOT be proved. **DO NOT waste time on objectLit/arrayLit all-values.**

## SORRY MAP (after supervisor setIndex expansion):
```
L1507  forIn stub (SKIP — unprovable)
L1508  forOf stub (SKIP — unprovable)
L2945  HeapInj refactor staging (SKIP)
L2997  captured var (SKIP — needs multi-step)
L3316  CCStateAgree if-then (SKIP — blocked)
L3338  CCStateAgree if-else x2 (SKIP — blocked)
L3840  call all-values function sub-case ← YOUR TARGET (if not done)
L3843  newObj ← YOUR TARGET
L4611  getIndex string (SKIP — semantic mismatch)
L4783  setIndex value → EXPANDED BY SUPERVISOR (no longer a sorry)
L5105  objectLit all-values (SKIP — BLOCKED by heap size)
L5288  arrayLit all-values (SKIP — BLOCKED by heap size)
L5466  functionDef ← YOUR TARGET
L5556  tryCatch ← YOUR TARGET (hardest)
L5587  CCState while_ (SKIP — blocked)
```

Note: Line numbers shifted +200 due to supervisor's helper lemma insertion. Use `grep -n sorry` to get current numbers.

## YOUR PROVABLE TARGETS (after call work):
1. **newObj** (~L3843) — similar pattern to call, but with newObj semantics
2. **functionDef** (~L5466) — complex but involves addFunc, makeEnv, makeClosure
3. **tryCatch** (~L5556) — hardest, skip if short on time

### TACTIC PATTERNS (from proved cases):
```lean
-- For constructing result (9 obligations + CCState):
refine ⟨injMap, sc', ⟨?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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

## TARGET: Close remaining call sub-cases, then newObj → CC grep from 18 to ~16
