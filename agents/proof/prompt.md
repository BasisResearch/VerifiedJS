# proof — Close normalizeExpr_if_cond_source, then compound/bindComplex sorries

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

## STATE: ANF 23 sorries. L6883 closed structurally. normalizeExpr_if_cond_source added at ~L2025 (sorry).

## YOUR IMMEDIATE TASKS (in order):

### TASK 1: Prove normalizeExpr_if_cond_source (~L2025) — HIGHEST PRIORITY
This is blocking the L6883 fix from being complete. Strong mutual induction on depth.

The theorem has three conjuncts (Expr, ExprList, PropList). Approach:
1. `intro d; induction d with | zero => ... | succ d ih => ...`
2. For zero: all expressions have depth > 0 contradiction (or handle base cases)
3. For succ d: `refine ⟨fun e k hd ... => ?_, fun es k hd ... => ?_, fun ps k hd ... => ?_⟩`
4. Case split on `e`:
   - `.var n`: k gets (.var n). If k produces .if, hk_cond says `.var n = .var name` → VarFreeIn.var
   - `.lit v`, `.this`: k gets literal. hk_cond says `.lit v = .var name` → contradiction (noConfusion)
   - `.if fc ft fe`: normalizeExpr processes condition. If fc trivial → produces .if with VarFreeIn from condition. If compound → bindComplex, need IH
   - `.seq a b`: processes a first. IH on sub-expressions
   - `.let name init body`: similar to seq
   - `.break`, `.continue`, `.return`, `.yield`, `.labeled`: k produces .trivial not .if → contradiction via hk_cond
   - `.assign`, `.call`, `.newObj`, `.getIndex`, `.setIndex`, `.binary`, `.unary`: compound → bindComplex → .let wrapper → IH
   - `.while_`, `.tryCatch`, `.functionDef`: produce specific structures, not .if → contradiction or IH

Key: for each constructor, either delegates to k (hk_cond gives answer), recurses (IH), or produces non-.if (contradiction with hnorm).

Use `lean_multi_attempt` on individual cases to find what closes them.

### TASK 2: "non-labeled inner value" sorries (~L6405, L6438, L6530, L6563)
Try `lean_multi_attempt` with:
```
["contradiction", "simp [*] at *", "omega", "exact absurd ‹_› ‹_›"]
```

### TASK 3: compound/bindComplex sorries (~L6449, L6574, L6591)
These say "needs induction on depth". Try strong induction similar to normalizeExpr_if_cond_source.

### SKIP THESE:
- `let_step_sim` (around L6880) — bindComplex PRODUCES .let, characterization WRONG
- ClosureConvertCorrect.lean — other agents own it

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
