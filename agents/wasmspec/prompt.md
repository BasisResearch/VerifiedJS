# wasmspec — Close CC setProp/setIndex/deleteProp/objectLit/arrayLit sorry bullets

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 29 grep-sorry hits, build passing.

## YOUR TARGETS (in priority order)

### Target 1: setProp sorry bullets (around L5096-5108)

These are in the setIndex case (all-three-values sub-case). For each sorry:
1. `lean_goal` at the sorry line to see what's needed
2. `lean_multi_attempt` with these candidates:
```
["exact hheapna'", "simp [sc', hheapna]", "exact hinj", "exact henvCorr",
 "exact henvwf", "exact hheapvwf", "simp [sc', noCallFrameReturn]",
 "simp [sc', ExprAddrWF]", "simp [sc', ExprAddrWF, ValueAddrWF]",
 "exact ⟨st_a, st_a', by simp [sc', Flat.convertExpr]; exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, by first | (rw [hst]; exact hAgreeOut) | (rw [hconv.2]; exact hAgreeOut)⟩"]
```

### Target 2: objectLit sorry bullets (around L5527-5536)

Same approach — `lean_goal` + `lean_multi_attempt`.

### Target 3: arrayLit sorry bullets (around L5627-5639)

Same approach.

### Target 4: deleteProp sorry (if any fixable, around L5436-5440)

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs
- L3262: captured var (HeapInj)
- L3590, L3613: CCStateAgree
- L4131, L4133: call function/non-closure (jsspec handles)
- L4302: newObj
- L4892: getIndex string
- L5440: objectLit all-values heap allocation
- L5543: arrayLit all-values heap allocation
- L5640: functionDef
- L5740-5748: tryCatch (jsspec handles)
- L5780: while_ CCState

### COLLISION AVOIDANCE
jsspec is also editing CC. You work on lines L5000-5650. jsspec works on L4100-4200 and L5700-5800. Do NOT edit the same regions.

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target line
3. `lean_multi_attempt` with candidate tactics
4. Edit the file with the working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Move to next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
