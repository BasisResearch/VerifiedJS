# jsspec — Close real CC sorries (22 "Fix D reverted" sorries ALREADY PROVED by supervisor)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- **NEVER** use `while` loops waiting for processes. Single check, then proceed.
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## STATE (23:30): CC has 18 grep-sorry, 14 real sorries

The supervisor ALREADY proved all 22 "Fix D reverted" sorries with:
`simp [Flat.step?, hss]; split <;> simp_all [Flat.exprValue?]`
(5 complex ones use: `cases fe with | lit v => simp [Flat.exprValue?] at hnv | _ => simp [Flat.step?, hss]`)

Also proved L3176 CCState threading with `by simp [sc']`.

### Remaining sorry breakdown (14 real):
- **2 unprovable stubs** (L1502-1503 forIn/forOf): DO NOT TOUCH
- **2 convertExpr_not_lit** (L2663, L2773): needs helper for 3 stub constructors
- **1 CCState threading L2857**: captured variable case — needs getEnv stepping
- **2 CCState threading L3198**: if-false branch — needs `CCStateAgree` reasoning
- **1 CCState threading L5237**: while_ lowering
- **2 callee/newObj** (L3692, L3693): wasmspec owns these
- **1 getIndex mismatch** (L4261): possibly unprovable
- **3 value sub-cases** (L4433, L4755, L4938): wasmspec owns these
- **1 functionDef** (L5116): wasmspec owns
- **1 tryCatch** (L5206): wasmspec owns

## YOUR TARGETS (5 sorries):

### TARGET 1: L2663 + L2773 (convertExpr_not_lit)
These need a lemma: `convertExpr_not_lit` for the 3 stub constructors (forIn, forOf, and one more).
`lean_goal` at L2663 → understand what's needed → prove or add the helper.

### TARGET 2: L2857 (captured variable)
Goal: When a variable is captured (lookupEnv returns some idx), the Flat expression is
`.getEnv (.var envVar) idx`. Need to show Flat stepping this corresponds to Core stepping `.var name`.
`lean_goal` → understand the EnvCorrInj invariant → construct the Core step witness.

### TARGET 3: L3198 (two sorries, if-false CCStateAgree)
First sorry: `CCStateAgree st (Flat.convertExpr then_ scope envVar envMap st).snd`
This requires showing converting `then_` preserves nextId and funcs.size — or choosing
a different st_a. Consider: can you use `st` instead, then use `convertExpr_state_determined`?

Second sorry: `CCStateAgree st' st_a'` — likely `⟨rfl, rfl⟩` since st' = st_a'.

### TARGET 4: L5237 (while_ CCState threading)
Similar to if-false: CCState diverges because while_ duplicates sub-expressions.

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf sorries (L1502-1503) — unprovable stubs
- L3692, L3693, L4261, L4433, L4755, L4938, L5116, L5206 — wasmspec owns these

## TARGET: Close at least 3 of your 5 assigned sorries → CC from 18 to ~13
