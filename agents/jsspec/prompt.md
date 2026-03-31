# jsspec — Close CC tryCatch + call sorries

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 29 grep-sorry hits, build passing.

## YOUR TARGETS (in priority order)

### Target 1: tryCatch noCallFrameReturn (L5740-5742) — EASY

These 3 sorries extract facts from `hncfr : noCallFrameReturn (.tryCatch body catchParam catchBody finally_) = true`.

`noCallFrameReturn` for tryCatch (L957-960):
```lean
| .tryCatch body cp cb fin =>
    cp != "__call_frame_return__" &&
    noCallFrameReturn body && noCallFrameReturn cb &&
    match fin with | some f => noCallFrameReturn f | none => true
```

**L5740** (`catchParam ≠ "__call_frame_return__"`):
```
lean_multi_attempt at L5740:
["simp [noCallFrameReturn] at hncfr; exact hncfr.1",
 "simp [noCallFrameReturn, bne_iff_ne] at hncfr; exact hncfr.1",
 "simp [noCallFrameReturn, Bool.and_eq_true, bne_iff_ne] at hncfr; exact hncfr.1",
 "have := hncfr; simp [noCallFrameReturn] at this; exact this.1",
 "simp only [noCallFrameReturn, Bool.and_eq_true, bne_iff_ne, ne_eq] at hncfr; exact hncfr.1"]
```

**L5741** (`noCallFrameReturn body = true`):
```
lean_multi_attempt at L5741:
["simp [noCallFrameReturn] at hncfr; exact hncfr.2.1",
 "simp [noCallFrameReturn, Bool.and_eq_true] at hncfr; exact hncfr.2.1",
 "have := hncfr; simp [noCallFrameReturn] at this; exact this.2.1"]
```

**L5742** (`noCallFrameReturn catchBody = true`):
```
lean_multi_attempt at L5742:
["simp [noCallFrameReturn] at hncfr; exact hncfr.2.2.1",
 "simp [noCallFrameReturn, Bool.and_eq_true] at hncfr; exact hncfr.2.2.1",
 "have := hncfr; simp [noCallFrameReturn] at this; exact this.2.2.1"]
```

### Target 2: call non-function case (L4133) — MEDIUM

Was previously proved before hsf_eta correction. Pattern:
1. `lean_goal` at L4133 to see current state
2. Need: rw hsf_eta at hstep, then Flat_step?_call_nonclosure, then Core.step_call_nonfunc
3. The 10 refine bullets are: hinj, henvCorr, henvwf, hheapvwf, hheapna, noCallFrameReturn, ExprAddrWF, CCState
4. `lean_multi_attempt` at L4133 with candidate approaches

### Target 3: setProp/setIndex sorry bullets (L5100-5108) — if time

These are in the setIndex all-values case. Use `lean_goal` to check what's needed.

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs (theorem is false)
- L3262: captured var (HeapInj refactor)
- L3590, L3613: CCStateAgree threading
- L4131: call consoleLog (FuncsCorr needed)
- L4302: newObj
- L4892: getIndex string semantic mismatch
- L5440, L5543: heap allocation
- L5640: functionDef
- L5745, L5748: tryCatch body stepping (complex)
- L5780: while_ CCState

### COLLISION AVOIDANCE
wasmspec is also editing CC. You work on lines L4100-4200 and L5700-5800. wasmspec works on L5000-5650. Do NOT edit the same regions.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
