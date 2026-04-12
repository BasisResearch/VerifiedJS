# proof — REFACTOR normalizeExpr_labeled_branch_step WITH K' FLEXIBILITY (12 sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T00:05
- ANF: 30 real sorries. CC: 12. Total: **42**.
- You spent 2 runs investigating trivial mismatch. Found: theorem design issue.
- `normalizeExpr_labeled_step_sim` (L11176) already solves this with K' flexibility.
- **The fix is to apply the SAME K' pattern to normalizeExpr_labeled_branch_step.**

## P0: REFACTOR normalizeExpr_labeled_branch_step (HIGHEST PRIORITY — 12 sorries)

### The Problem
`normalizeExpr_labeled_branch_step` (L10304) conclusion requires:
```lean
(∃ n' m', (ANF.normalizeExpr sf'.expr K).run n' = .ok (body, m'))
```
This fixes K. When a non-head trivial steps (`.var "x"` → `.lit v`), the trivial representation changes, so `normalizeExpr sf'.expr K` produces a DIFFERENT body. Blocks 12 sorries.

### The Solution (ALREADY WORKING in normalizeExpr_labeled_step_sim)
`normalizeExpr_labeled_step_sim` (L11176) conclusion uses:
```lean
(∃ (k' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
  (ANF.normalizeExpr sf'.expr k').run n' = .ok (body, m') ∧
  (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (k' arg).run n'' = .ok (.trivial arg, m'')))
```
This allows a DIFFERENT k' (as long as it's trivial-preserving). **This is exactly what we need.**

### Step-by-step plan:

**Step 1: Change the conclusion** of `normalizeExpr_labeled_branch_step` (L10304):
Change line ~10322 from:
```lean
(∃ n' m', (ANF.normalizeExpr sf'.expr K).run n' = .ok (body, m')) ∧
```
to:
```lean
(∃ (K' : ANF.Trivial → ANF.ConvM ANF.Expr) (n' m' : Nat),
  (ANF.normalizeExpr sf'.expr K').run n' = .ok (body, m') ∧
  (∀ (arg : ANF.Trivial) (n'' : Nat), ∃ m'', (K' arg).run n'' = .ok (.trivial arg, m''))) ∧
```

**ALSO ADD** a precondition that K is trivial-preserving:
```lean
(hk_triv : ∀ (arg : ANF.Trivial) (n' : Nat), ∃ m', (K arg).run n' = .ok (.trivial arg, m')) →
```

**Step 2: Fix the existing proofs** (cases that already work):
- The `labeled_direct` case (L~10338): currently returns `⟨n, m', hnorm_inner⟩` — change to `⟨K, n, m', hnorm_inner, hk_triv⟩`
- Similar for other already-proved cases — just wrap the K witness

**Step 3: Fix the 12 sorry cases**:
In the `¬HasLabeledInHead` branches (e.g., binary_rhs at L10799):
- The non-head element `e` steps to value `v` (via existing IH or trivial stepping)
- After stepping, `sf'.expr` has `.lit v` instead of `e`
- `normalizeExpr sf'.expr K'` works with K' = a continuation that accounts for the value change
- The KEY: since `e` was trivial (non-head means it's a trivialChain), after stepping it to `.lit v`:
  - Original: `normalizeExpr e (fun t => ...)` inlines `t = trivialOfExpr e`
  - After step: `normalizeExpr (.lit v) (fun t => ...)` inlines `t = trivialOfFlatValue v`
  - K' = original K but with `t` replaced — this is constructible because K is trivial-preserving

**Step 4: Update callers** (~7 callers that destructure the result):
Currently they do: `obtain ⟨..., ⟨n', m', hnorm'⟩, ...⟩`
Change to: `obtain ⟨..., ⟨K', n', m', hnorm', hk'_triv⟩, ...⟩`
Then pass K' and hk'_triv downstream instead of K and hk_triv.

### VERIFICATION: Check normalizeExpr_labeled_step_sim callers
The caller at L25197 already handles K' flexibility:
```lean
obtain ⟨evs, sf', hsteps, ⟨k', n', m', hbody, hk'⟩, ...⟩ :=
  normalizeExpr_labeled_step_sim ...
```
This SAME pattern should work for normalizeExpr_labeled_branch_step callers.

### DO THIS FIRST:
1. `lean_hover_info` at L10304 col 19 to confirm current signature
2. `lean_goal` at L10799 to see the current sorry goal
3. Make the signature change (Step 1)
4. Fix ONE already-proved case (Step 2) to verify the approach works
5. Then tackle sorry cases one at a time

**Expected: -7 to -12 sorries if the refactor succeeds.**

## P1: COMPOUND THROW (L13809) — only if P0 done
HasThrowInHead_Steps_steppable is provable (~550 lines, no tryCatch constructors). Only attempt after P0.

## DO NOT WORK ON:
- L16451 (wasmspec P2)
- ClosureConvertCorrect.lean
- L21749+ compound cases

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — normalizeExpr_labeled_branch_step K' refactor" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
