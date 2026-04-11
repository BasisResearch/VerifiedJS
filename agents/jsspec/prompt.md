# jsspec — α-equivalence for CCStateAgree fix

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T20:05
- CC: 12 real sorries. Total: **49** (ANF 37 + CC 12).
- Path A (position-based naming): assessed as INSUFFICIENT — funcs.size has same branching problem.
- You implemented `noFunctionDef` + `convertExpr_state_id_no_functionDef` — good foundation.
- ClosureConvert.lean is owned by `proof` with 640 permissions — YOU CANNOT WRITE TO IT.
- ALL 12 CC sorries are architecturally blocked by CCStateAgree or multi-step.

## THE REAL FIX: Expr-level equivalence relation

### Why monotone was rejected:
Output expressions embed `funcIdx = st.funcs.size` via `makeClosure funcIdx`. If `st1.funcs.size ≠ st2.funcs.size`, the converted expressions are literally different terms. Simple `≤` doesn't make them equal.

### Why Path A is insufficient:
Removing `nextId` doesn't help because `funcs.size` dependency remains through `makeClosure`.

### The way forward: `CCExprEquiv`
Define an equivalence relation on Flat.Expr that says "same structure, possibly different funcIdx in makeClosure calls". Two expressions are CCExprEquiv if they differ only in:
- The `funcIdx` argument to `makeClosure`
- The `nextId`-derived fresh variable names (if any remain)

Then change the CC simulation theorem to prove `CCExprEquiv (convertExpr e ... st1) (convertExpr e ... st2)` when `st1` and `st2` differ only in nextId/funcs.size.

### THIS RUN: Feasibility study + prototype

1. **Define `CCExprEquiv`** (mutual inductive on Flat.Expr):
   - All constructors match structurally
   - `makeClosure` case: allows different funcIdx
   - `var` case: allows renamed fresh variables if they follow a consistent renaming

2. **Prove `convertExpr_CCExprEquiv`**: if `st1.nextId ≤ st2.nextId` and `st1.funcs.size ≤ st2.funcs.size`, then `CCExprEquiv (convertExpr e scope envVar envMap st1).fst (convertExpr e scope envVar envMap st2).fst`

3. **Prove that `CCExprEquiv` preserves stepping**: if `CCExprEquiv e1 e2` and `Flat.step? ⟨e1, ...⟩ = some (t, s1')`, then `Flat.step? ⟨e2, ...⟩ = some (t, s2')` and `CCExprEquiv s1'.expr s2'.expr`.

4. **Replace CCStateAgree** with `CCExprEquiv`-based invariant.

### REALITY CHECK: This is a multi-run effort.
- This run: define CCExprEquiv, start proving convertExpr_CCExprEquiv for simple cases
- If CCExprEquiv is too complex, consider: just prove `noFunctionDef branch → convertExpr_state_id` for the *specific* sorry sites where the branch might be noFunctionDef at runtime
- Even partial progress (just the definition + a few cases) is valuable

### ALTERNATIVE: Case-split noFunctionDef approach
For each CCStateAgree sorry, check if you can add `noFunctionDef` as a hypothesis to a helper lemma and discharge it from the `supported` context. Even if `supported` includes `functionDef`, maybe the SPECIFIC expression contexts (if/while/tryCatch branches) can be shown noFunctionDef in certain cases.

## DO NOT ATTEMPT:
- Multi-step simulation sorries (L5728, L6606, L6825, L7033, L7044)
- L7684 (getIndex semantic mismatch — unprovable)
- L8931 (functionDef — needs multi-step)
- Editing ClosureConvert.lean (no write permission)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCExprEquiv feasibility" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
