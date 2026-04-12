# proof — K' REFACTOR (12 sorries) THEN COMPOUND THROW (1 sorry)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T01:05
- ANF: 30 real sorries. CC: 12. Total: **42**.
- You are working on K' refactor for normalizeExpr_labeled_branch_step. CONTINUE.
- `normalizeExpr_labeled_step_sim` (L11176) already has the K' pattern. Copy it.

## P0: REFACTOR normalizeExpr_labeled_branch_step (HIGHEST PRIORITY — 12 sorries)

### The Problem
`normalizeExpr_labeled_branch_step` (L10304) conclusion requires:
```lean
(∃ n' m', (ANF.normalizeExpr sf'.expr K).run n' = .ok (body, m'))
```
This fixes K. When a non-head trivial steps (`.var "x"` → `.lit v`), the body changes. Blocks 12 sorries.

### The Solution (ALREADY WORKING in normalizeExpr_labeled_step_sim)
```lean
(∃ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
  (ANF.normalizeExpr sf'.expr k').run n' = .ok (body, m') ∧
  (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (k' arg).run n'' = .ok (.trivial arg, m'')))
```

### Step-by-step:
1. **Change conclusion** at L10304: replace fixed K with existential K' + trivial-preserving witness
2. **Add precondition**: `(hk_triv : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (K arg).run n' = .ok (.trivial arg, m'))`
3. **Fix proved cases**: wrap existing K with `⟨K, n, m', hnorm_inner, hk_triv⟩`
4. **Fix 12 sorry cases**: construct K' that accounts for the trivial representation change
5. **Update ~7 callers**: destructure `⟨K', n', m', hnorm', hk'_triv⟩`

### VERIFICATION after each step:
After changing the signature (Step 1+2), immediately check ONE proved case compiles, THEN fix sorry cases one at a time.

**Expected: -7 to -12 sorries**

## P1: COMPOUND THROW (L14196) — only if P0 done or blocked

`HasThrowInHead_Steps_steppable` is provable (~550 lines). Key insight you already found: unlike HasReturnInHead, HasThrowInHead does NOT go through tryCatch, so no `¬HasNonCallFrameTryCatchInHead` needed.

Pattern: copy `HasReturnInHead_Steps_steppable_core` structure but for throw. Cases:
- throw_direct: immediate
- seq_left, let_binding, labeled_body: induction
- NO tryCatch cases (throw doesn't compose through try)

**Expected: -1 sorry**

## P2: IF-BRANCH K-MISMATCH (L23213, L23253) — only if P0+P1 done

These 2 sorries have similar K-mismatch to P0. If K' refactor succeeds, these may become closeable with the same pattern.

## DO NOT WORK ON:
- L16877 (wasmspec P1)
- ClosureConvertCorrect.lean
- L21749+ compound cases (too deep)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — K' refactor continued" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
