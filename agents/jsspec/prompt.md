# jsspec — BULK-CLOSE ~70 FuncsCorr sorry⟩ THEN INIT/CALL

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — CRITICAL DISCOVERY
- CC has **87 real sorries** (not 17!). 72 of them are `sorry⟩` at the end of `refine ⟨..., sorry⟩`.
- These 72 `sorry⟩` are ALL the FuncsCorr field you just added to CC_SimRel.
- **FuncsCorr does NOT use injMap** — check the definition at L1455. injMap is a parameter but UNUSED in the body.
- For ALL cases except functionDef, `sc'.funcs = sc.funcs` (Core doesn't change funcs).
- Therefore `sorry⟩` → `hfuncCorr⟩` should close ~70 of 72 sorries in ONE PASS.

## P0: BULK-CLOSE FuncsCorr sorry⟩ (HIGHEST PRIORITY — ~70 sorries)

**Strategy**: Replace every `sorry⟩` at the end of refine patterns with `hfuncCorr⟩`.

**EXACT STEPS:**
1. For lines with `refine ⟨injMap, sc', ..., sorry⟩`: replace `sorry⟩` with `hfuncCorr⟩`
2. For lines with `refine ⟨injMap', sc', ..., sorry⟩`: try `hfuncCorr⟩` first. If that fails (because Lean can't unify FuncsCorr injMap with FuncsCorr injMap'), use `(by unfold FuncsCorr at hfuncCorr ⊢; exact hfuncCorr)⟩`
3. For the line at ~L5333 and similar inline sorry patterns, same approach
4. For functionDef case (~L8044): this needs REAL work (funcs change). Leave sorry for now.
5. VERIFY with lean_diagnostic_messages after each batch of ~10 changes

**WARNING**: Also check sf'.funcs = sf.funcs for each case. Flat.Step should not change funcs for non-functionDef. If a case fails, it means Flat changed funcs there — investigate.

**DO NOT** try to close all 72 in one edit. Do 10 at a time, verify, continue.

## P1: CLOSE L1519 (FuncsCorr initial state)

FuncsCorr for initial state. Initial funcs should be empty/trivially matching.
Run `lean_goal` at L1519. If initial funcs are `#[]`, FuncsCorr is trivially true.

## P2: CLOSE L5935 (call case, now unblocked)

`hfuncCorr` is in scope. Extract matching Flat.FuncDef, step to function body.

## KNOWN BLOCKED (DO NOT ATTEMPT):
- L5335, L5361, L8203, L8206, L8278, L8394: CCStateAgree (6 total)
- L4984, L6141, L6152: multi-step simulation gap (3 total)
- L5152, L5251, L5490: error structural mismatch (3 total)
- L6792: semantic mismatch (UNPROVABLE)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — BULK FuncsCorr close" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
