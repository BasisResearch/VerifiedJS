# jsspec — Close CC L4133 and tryCatch body-value (L5855)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC 22 grep-sorry hits. You closed 2 helper lemma sorries last run. Good work.

## YOUR TARGETS (in priority order)

### Target 1: call non-function case (L4133) — MEDIUM

The goal: callee is NOT a function (all args values). Non-function call should produce a runtime error on both sides.

Current context at L4133:
- `hnotfunc : ∀ idx, cv ≠ .function idx` — callee is not a function
- `hallv : Core.allValues args = some argVals` — all args are values
- `hcev : Core.exprValue? f = some cv` — callee is a value
- Need: Flat step matches Core step

Pattern:
1. `lean_goal` at L4133 to see full state
2. Core should step `call (lit cv) [lit v1, ..., lit vn]` to error since cv is not a function
3. Flat should do the same with converted values
4. The key tactic sequence:
```
lean_multi_attempt at L4133:
["have : ∀ idx, cv ≠ .function idx := hnotfunc; sorry",
 "simp [Core.step?, Core.exprValue?, hcev, hallv] at hcstep; sorry"]
```
Use `lean_goal` first to understand what's needed, then build the proof step by step.

### Target 2: tryCatch body-value (L5855) — MEDIUM

When body is a value `some v`, tryCatch immediately produces the value (skipping catch, running finally).
- `hbv : Core.exprValue? body = some v`
- Core steps: tryCatch (lit v) catchParam catchBody finally → v (or sequence with finally)
- Flat steps: similarly with converted expressions

Approach:
1. `lean_goal` at L5855
2. Prove `body = .lit v` from `hbv`
3. Show both Core and Flat step tryCatch of a literal
4. Use `lean_multi_attempt` with candidates

### Target 3: tryCatch body-stepping (L5858) — HARD, may be BLOCKED

Body is not a value. Need IH to step body, then wrap in tryCatch context.
- Uses `ih` on body, then reconstruct
- LIKELY BLOCKED by CCState threading (body conversion uses st, but catch/finally use st1/st2)
- Only attempt if L4133 and L5855 are done

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs (theorem is false)
- L3262: captured var (HeapInj refactor)
- L3590, L3613: CCStateAgree threading
- L4131: call function (FuncsCorr needed)
- L4302: newObj
- L4892: getIndex string semantic mismatch
- L5212, L5215: setIndex sub-stepping
- L5547, L5643, L5650: heap allocation
- L5746: arrayLit CCState
- L5747: functionDef
- L5890: while_ CCState

### COLLISION AVOIDANCE
wasmspec is also editing CC. You work on lines L4100-4200 and L5800-5900. wasmspec works on L5000-5650. Do NOT edit the same regions.

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
