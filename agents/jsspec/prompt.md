# jsspec — FuncsCorr DEFINITION + CCStateAgree ANALYSIS

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 17 sorries. ANF: 42. Total: 59.
- FuncsCorr stub defined at L1455-1473 (your run at 00:12).
- CCStateAgreeWeak defined at L566.
- convertExpr_state_mono proved at L767.

## CRITICAL: CCStateAgreeWeak IS NOT A SIMPLE SWAP

Previous prompts said "change CCStateAgree to CCStateAgreeWeak in the invariant." **THIS WILL BREAK PROVED CASES.**

The invariant at L4914:
```lean
CCStateAgree st st_a ∧ CCStateAgree st' st_a'
```

The PROVED cases (L6043-6050, L7762-7771, L7978, L8311-8327) use CCStateAgree EQUALITY to call `convertExpr_state_determined`, which requires `st1.nextId = st2.nextId`. With CCStateAgreeWeak (≤), these break.

**INSTEAD**, the fix requires:
1. Keep CCStateAgree in the invariant
2. For the 6 sorry sites (if/while/tryCatch), find DIFFERENT `st_a/st_a'` witnesses that satisfy equality
3. OR: prove a `convertExpr_state_determined_weak` that works with ≤ (but this seems impossible since different nextId → different variable names → different expressions)
4. OR: define an expression equivalence up to variable renaming and show simulation preserves it

Since option 3/4 are very large refactors, focus on option 1: can you find witnesses that DO satisfy equality?

For if-true (L5298): Currently uses `st_a = st` and `st_a' = (convertExpr then_ ... st).snd`. The issue: `st' = (convertExpr else_ ... st_a').snd ≠ st_a'`. **Can we pick a different `st_a`?**

Key question: is there a state `st_a` with `st_a.nextId = st'.nextId` such that `(convertExpr then_ ... st_a).fst` still equals the then-branch expression? This would require knowing that `convertExpr then_` is insensitive to the starting nextId for producing the same expression. But it IS sensitive (generates fresh vars from nextId).

**Verdict: THIS IS A GENUINE ARCHITECTURAL ISSUE.** Document it precisely.

## P0: FuncsCorr DEFINITION (L1469, L1473)

The FuncsCorr stub is defined but both properties are sorry'd. Fill in the actual definition:

1. `lean_goal` at L1469 to see what's needed
2. The first property should relate `fd.body` (Core function closure body) to `fc.body` (Flat function definition body) via closure conversion
3. The second property should relate function parameter lists via `injMap`

Concrete: look at how functions are closure-converted in `Flat.convertExpr`:
```lean
| .functionDef fname params body => ...
```
Check `lean_hover_info` on `Flat.convertExpr` and read the functionDef case. The FuncsCorr body property should say something like:
```lean
fc.body = (Flat.convertExpr fd.body params envVar envMap st).fst
```

## P1: Document CCStateAgree architectural issue

Write a detailed comment (5-10 lines) above L4914 explaining:
1. WHY CCStateAgree (equality) is needed for the proved cases
2. WHY it's unprovable for if/while/tryCatch
3. What a real fix would look like (expression equivalence up to fresh var renaming)

This documentation is valuable for future work even if we can't fix it now.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — FuncsCorr def + CCStateAgree analysis" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
