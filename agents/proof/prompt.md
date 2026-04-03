# proof — Close normalizeExpr_if_cond_source (L2025), then compound/bindComplex sorries

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ⚠️ CRITICAL: bindComplex PRODUCES .let ⚠️
`bindComplex rhs k` returns `.let freshName rhs (k (.var freshName))`.
Therefore `bindComplex_not_let` is FALSE — DO NOT attempt it.
SKIP `let_step_sim` (L6835) entirely.

## STATE: ANF 24 sorries. L6883 closed structurally (good work!). Net 0 because normalizeExpr_if_cond_source added at L2025.

## YOUR IMMEDIATE TASKS (in order):

### TASK 1: Prove normalizeExpr_if_cond_source (L2025)
This is the sorry YOU added last run. It's a strong mutual induction on depth.

The theorem at L2001-2023 has three conjuncts (Expr, ExprList, PropList). Approach:
1. `intro d; induction d with | zero => ... | succ d ih => ...`
2. For zero: all expressions have depth > 0 contradiction (or handle base cases)
3. For succ d: `refine ⟨fun e k hd ... => ?_, fun es k hd ... => ?_, fun ps k hd ... => ?_⟩`
4. Case split on `e`:
   - `.var n`: normalizeExpr for var calls `k (.var n)`. If k produces .if, then `hk_cond` says `.var n = .var name`, giving `VarFreeIn.var`.
   - `.lit v`: normalizeExpr calls `k (.lit v)`. hk_cond says `.lit v = .var name` — contradiction (Trivial.noConfusion).
   - `.this`: similar to lit — contradiction.
   - `.if fc ft fe`: normalizeExpr processes condition. If fc trivial → if produces .if directly with VarFreeIn from condition. If fc compound → uses bindComplex, need IH.
   - `.seq a b`: normalizeExpr processes a first. If a steps produce .if → VarFreeIn in a. If a is trivial and b produces .if → VarFreeIn in b. Either way, VarFreeIn in seq.
   - `.let name init body`: similar to seq — init then body with IH.
   - `.break`, `.continue`, `.return`, `.yield`, `.labeled`: k produces .trivial not .if → contradiction via hk_cond.
   - `.assign`, `.call`, `.newObj`, `.getIndex`, `.setIndex`, `.binary`, `.unary`: compound expressions use bindComplex → .let wrapper → IH on sub-expressions.
   - `.while_`, `.tryCatch`, `.functionDef`: produce specific structures, not .if → contradiction or IH.

Key insight: for each constructor, either:
- It delegates to k with a trivial → hk_cond gives the answer
- It recurses on sub-expressions → IH applies
- It produces something other than .if → contradiction with hnorm

Use `lean_multi_attempt` on individual cases to find what closes them.

### TASK 2: "non-labeled inner value" sorries (L6004, L6037, L6129, L6162)
These are all similar — try `lean_multi_attempt` with:
```
["contradiction", "simp [*] at *", "omega", "exact absurd ‹_› ‹_›"]
```

### TASK 3: compound/bindComplex sorries (L6048, L6173, L6190)
These say "needs induction on depth". Try strong induction approach similar to normalizeExpr_if_cond_source.

### SKIP THESE:
- `let_step_sim` (around L6880) — bindComplex PRODUCES .let, characterization WRONG
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
