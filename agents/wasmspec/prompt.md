# wasmspec — Fix CC sorry regression (38 → reduce)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**You have wasted 80+ HOURS total in while loops. DO NOT LOOP.**

### BUILD — THE ONLY WAY:
```bash
lake build VerifiedJS.Proofs.ClosureConvertCorrect
```
ONE command. No waiting, no checking, no loops.

### ABSOLUTE RULES:
1. **NEVER write `while`** — not for pgrep, not for sleep, not for ANYTHING
2. **NEVER write `until`** — same infinite loop problem
3. **NEVER write `sleep` inside any loop**
4. **NEVER write `pgrep`** — lake serve is PERMANENT
5. **NEVER write `do...done`** — no loops of any kind
6. If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## SITUATION
- **CC: 38 sorries, BUILD PASSES.** Many fixable sorry regressions.
- **ANF: 58 sorries — FILE LOCKED.** DO NOT TOUCH.
- **LowerCorrect: FILE LOCKED.** DO NOT TOUCH.

## YOUR PLAN: Fix CC sorry regressions

Focus on setProp, setIndex, deleteProp, objectLit, arrayLit sorry bullets.

### Target: setProp sorry bullets (around L4590-4596)
These are individual refine bullets that were sorry'd. Pattern:
1. `lean_goal` at each sorry
2. `lean_multi_attempt` with: `["exact hheapna'", "simp [sc', hheapna]", "simp [sc', noCallFrameReturn]", "simp [sc', ExprAddrWF, ValueAddrWF]"]`
3. Edit with working tactic

### Target: setIndex sorry bullets (around L5084-5241)
Same pattern. The setIndex case has several sorry'd sub-branches.

### Target: deleteProp sorry bullets (around L5507-5509)

### Target: objectLit / arrayLit sorry bullets (around L5607-5609)

### SKIP (architecturally blocked):
- L1507-1508: forIn/forOf stubs
- L3258: captured var (HeapInj)
- L3586, L3609: CCStateAgree
- L4127: call function (FuncsCorr)
- L4298: newObj
- L4876: getIndex semantic mismatch
- L5416, L5516: heap allocation
- L5610: functionDef
- L5750: while_ CCState

## WORKFLOW:
1. `grep -n sorry ClosureConvertCorrect.lean` to find CURRENT line numbers
2. `lean_goal` at target
3. `lean_multi_attempt` with candidates
4. Edit file with working tactic
5. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
6. Next target

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
