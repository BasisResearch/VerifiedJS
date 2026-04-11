# jsspec — FuncsCorr DEFINITION (L1469, L1473) + TRACTABLE SORRIES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 15 real sorries. ANF: 40. Total: 55.
- CCStateAgreeWeak confirmed NOT viable.
- FuncsCorr stub defined at L1455-1473 but both properties sorry'd.

## P0: FuncsCorr — CLOSE L1469 AND L1473

These two sorries define what it means for Core and Flat function definitions to correspond after closure conversion.

**DO THIS:**
1. Run `lean_goal` at L1469 to see the exact goal type
2. Run `lean_hover_info` on `FuncsCorr` to see the current stub definition
3. The body property (L1469) should state: `fc.body` equals the result of closure-converting `fd.body`
4. The params property (L1473) should relate parameter lists via `injMap` or similar
5. If these are DEFINITIONS (not proofs), fill in the correct predicate

## P1: HeapInj SORRY (L4898 area)

This was "temporarily sorry'd during HeapInj refactor" per comment at L4898. Check if the old proof structure is recoverable:
1. Run `lean_goal` near L4898 to find the actual sorry
2. Check if it's a simple proof that was disrupted by type changes

## P2: TRACTABLE SORRIES — CHECK THESE WITH lean_goal

Check whether any of these are actually closable (not all are CCStateAgree-blocked):
- L5146, L5245: sub-expression stepping sorries
- L5484: may be error-case or CCStateAgree
- L5930: check what blocks it
- L8042: functionDef sorry — check if FuncsCorr (from P0) would help

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5327, L5353, L8199, L8202, L8276, L8392: CCStateAgree architectural issue (6 total)
- L4978, L6138, L6149: multi-step simulation gap (3 total)
- L6789: semantic mismatch (getIndex string) — UNPROVABLE

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr L1469 L1473" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
