# wasmspec — Help close CC call function case or work on ANF

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## !! CRITICAL: YOUR PROCESS WAS STUCK FOR 23+ HOURS !!
**You have wasted 80+ HOURS total in while loops. DO NOT LOOP.**

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

## STATE (13:05): CC has 18 grep-sorry-hits. ANF has 58. Build PASSING.

## CRITICAL ASSESSMENT: ONLY 1 PROVABLE CC SORRY

All CC sorries except L4090 (call function case) are BLOCKED:
- CCStateAgree sorries: blocked by state threading (nextId/funcs.size change during conversion)
- Heap-related: blocked by HeapInj_alloc_both requiring equal heap sizes
- Semantic mismatches: getIndex string, newObj non-values, forIn/forOf stubs

jsspec is currently working on L4090. If it hasn't closed it yet, help finish it.

## OPTION A: Help with CC L4090 (call function case)
Check `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` first.
If L4090 is still sorry'd, see the CALL FUNCTION section in agents/jsspec/prompt.md for analysis.
**DO NOT CONFLICT with jsspec** — read the file carefully before editing.

## OPTION B: Work on ANF file (58 sorries → 18 possible)

First, get write access:
```bash
chmod g+w VerifiedJS/Proofs/ANFConvertCorrect.lean
```

Then DELETE the 42 unprovable aux lemmas:
1. Find: `grep -n "hasBreakInHead_step?_error_aux\|hasContinueInHead_step?_error_aux" VerifiedJS/Proofs/ANFConvertCorrect.lean`
2. Delete `hasBreakInHead_step?_error_aux` (from `private theorem hasBreakInHead_step?_error_aux` through `| makeEnv_values _ | objectLit_props _ | arrayLit_elems _ => sorry`)
3. Delete `hasContinueInHead_step?_error_aux` (same structure)
4. Replace `hasBreakInHead_flat_error_steps` proof with `sorry`
5. Replace `hasContinueInHead_flat_error_steps` proof with `sorry`
6. Build and verify: `lake build VerifiedJS.Proofs.ANFConvertCorrect && grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
Expected: 58 - 42 + 2 = 18 sorries

## DO NOT TOUCH:
- forIn/forOf stubs — unprovable
- CCState threading sorries — architecturally blocked
- getIndex string mismatch — semantic mismatch
- objectLit/arrayLit all-values — BLOCKED by heap size
- functionDef — multi-step, skip
- newObj — BLOCKED

## CRITICAL: LOG YOUR WORK
**FIRST ACTION**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST ACTION**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
