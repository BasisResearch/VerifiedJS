# jsspec — FuncsCorr DEFINITION (L1469, L1473) + HeapInj SORRY (L4888)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 17 sorries. ANF: 42. Total: 59.
- **NO PROGRESS SINCE LAST RUN.** You must close at least 1 sorry this run.
- CCStateAgreeWeak confirmed NOT viable (breaks 10+ proved cases).
- FuncsCorr stub defined at L1455-1473 but both properties sorry'd.

## P0: FuncsCorr — CLOSE L1469 AND L1473

These two sorries define what it means for Core and Flat function definitions to correspond after closure conversion.

**DO THIS:**
1. Run `lean_goal` at L1469 to see the exact goal type
2. Run `lean_hover_info` on `Flat.convertExpr` to understand how functionDef is converted
3. Run `lean_hover_info` on `FuncsCorr` to see the current stub definition
4. The body property (L1469) should state: `fc.body` equals the result of closure-converting `fd.body`
5. The params property (L1473) should relate parameter lists via `injMap` or similar

If the properties are actually DEFINITIONS (not proofs), then fill in the correct predicate. If they're proofs of existing predicates, prove them.

## P1: HeapInj SORRY (L4888-L4891)

Line 4888 says "proof temporarily sorry'd during HeapInj refactor" with "Previous proof in git history." This sounds like a regression.

1. Run `lean_goal` at L4888 (or nearby sorry) to see what's needed
2. Check git: `git log --oneline -5 -- VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find the last commit that changed this
3. If the old proof is recoverable, restore it

## P2: L5117, L5216, L5455 — if/while sub-expression sorries

These are NOT CCStateAgree-blocked. Check with `lean_goal` whether they're tractable.

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5298, L5324, L8170, L8173, L8247, L8363: CCStateAgree architectural issue
- L4949, L6109, L6120: multi-step simulation gap
- L6760: semantic mismatch (getIndex string)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr L1469 L1473" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
