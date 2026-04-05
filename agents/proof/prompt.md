# proof — Close 8 UNLOCK sorries in compound_true/false_sim

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~3.6GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L10944-11461 (normalizeExpr_if_branch_step inner cases)
- **YOU** own L11764-11987 (compound_true/false_sim, UNLOCK sorries) AND L12015+ (tryCatch, break/continue)
- DO NOT touch lines outside your range

## YOUR PRIMARY TARGET: 8 UNLOCK sorries

These are in `normalizeExpr_if_compound_true_sim` (L11764) and `normalizeExpr_if_compound_false_sim` (L11879).

### KEY INSIGHT: How to bridge normalizeExpr_if_branch_step → ANF_SimRel

`normalizeExpr_if_branch_step` (L11020) gives:
```
∃ sf' evs,
  Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf' ∧
  (∀ ev ∈ evs, ev = .silent) ∧
  sf'.env = env ∧ sf'.heap = heap ∧ sf'.funcs = funcs ∧ sf'.callStack = cs ∧
  sf'.trace = trace ++ evs ∧ hpres ∧
  (∃ n' m', (normalizeExpr sf'.expr K).run n' = .ok (then_, m')) ∧
  ExprWellFormed sf'.expr sf'.env
```

`normalizeExpr_if_compound_true_sim` (L11764) needs:
```
∃ sf' evs,
  Steps ⟨sf_expr, env, heap, trace, funcs, cs⟩ evs sf' ∧
  observableTrace [.silent] = observableTrace evs ∧
  ANF_SimRel s t ⟨then_, env, heap, sa_trace ++ [.silent]⟩ sf' ∧
  ExprWellFormed sf'.expr sf'.env
```

Where `ANF_SimRel` (L64) is:
```
sa.heap = sf.heap ∧ sa.env = sf.env ∧
observableTrace sa.trace = observableTrace sf.trace ∧
∃ k n m, (normalizeExpr sf.expr k).run n = .ok (sa.expr, m) ∧ ∀ arg n', ∃ m', (k arg).run n' = .ok (.trivial arg, m')
```

The bridge is straightforward:
1. **Steps**: same
2. **observableTrace [.silent] = observableTrace evs**: Both sides are `[]` because `.silent` events are filtered. Since all evs are silent, `observableTrace evs = []`. And `observableTrace [.silent] = []`. So `rfl` or `by simp [observableTrace]`.
3. **ANF_SimRel**:
   - `heap`: `sf'.heap = heap` from output ✓
   - `env`: `sf'.env = env` from output ✓
   - `trace`: Need `observableTrace (sa_trace ++ [.silent]) = observableTrace sf'.trace`. Since `sf'.trace = trace ++ evs` and all evs silent: `observableTrace (trace ++ evs) = observableTrace trace`. And `observableTrace (sa_trace ++ [.silent]) = observableTrace sa_trace`. So reduces to `htrace : observableTrace sa_trace = observableTrace trace`. ✓
   - `normalizeExpr`: output gives `∃ n' m', (normalizeExpr sf'.expr K).run n' = .ok (then_, m')`. Use `K` from hypothesis `hk`. ✓

### VERIFIED LINE NUMBERS (17:30):
- L11627: UNLOCK seq true
- L11635: UNLOCK if true
- L11637: UNLOCK condition true
- L11639: UNLOCK all_goals true
- L11741: UNLOCK seq false
- L11748: UNLOCK if false
- L11750: UNLOCK condition false
- L11752: UNLOCK all_goals false

### EASIEST: L11639 + L11752 (all_goals sorry — non-if_direct cases)

These are the non-if_direct HasIfInHead cases. `normalizeExpr_if_branch_step` applies DIRECTLY to `sf_expr`.

**Step 1**: Use `lean_goal` to see exact goals:
```
lean_goal at L11639 column 14
lean_goal at L11752 column 14
```

**Step 2**: The proof for L11639 (true branch):
```lean
all_goals (
  obtain ⟨sf', evs, hsteps, hsil, henv, hheap, hfuncs, hcs, htrace_sf, hpres, ⟨n', m', hnorm'⟩, hewf'⟩ :=
    normalizeExpr_if_branch_step sf_expr.depth sf_expr (Nat.le_refl _) ‹HasIfInHead sf_expr›
      env heap trace funcs cs k n m cond then_ else_ v hnorm hewf heval hbool
  refine ⟨sf', evs, hsteps, ?_, ?_, hewf'⟩
  · -- observableTrace [.silent] = observableTrace evs
    simp only [observableTrace]
    induction evs with
    | nil => rfl
    | cons ev evs' ih =>
      have := hsil ev (List.mem_cons_self _ _)
      rw [this]; simp [observableTrace]; exact ih (fun e he => hsil e (List.mem_cons_of_mem _ he))
  · -- ANF_SimRel
    refine ⟨by rw [hheap], by rw [henv], ?_, k, n', m', hnorm', hk⟩
    rw [htrace_sf]
    simp [observableTrace_append]
    have : observableTrace evs = [] := by
      induction evs with
      | nil => rfl
      | cons ev evs' ih =>
        have := hsil ev (List.mem_cons_self _ _)
        rw [this]; simp [observableTrace]; exact ih (fun e he => hsil e (List.mem_cons_of_mem _ he))
    rw [this, List.append_nil]
    simp [observableTrace_append, observableTrace_silent, observableTrace_nil] at htrace ⊢
    exact htrace
)
```

**Try with lean_multi_attempt first** to test parts of this. If the observableTrace lemmas don't exist by those names, use `lean_hover_info` to find the right ones, or prove inline.

**Step 3**: L11752 (false branch) is symmetric — use `normalizeExpr_if_branch_step_false` instead.

### MEDIUM: L11635/L11637 + L11748/L11750 (if_direct sub-cases with eval context)

For L11635 (`.if c' t' e'` case) and L11637 (`| _` catch-all):
1. Extract `HasIfInHead` for the condition sub-expression
2. Compute `K_if` (the if-continuation used by normalizeExpr_if')
3. Apply `normalizeExpr_if_branch_step` on the condition with `K_if`
4. Lift steps through `Steps_if_cond_ctx_b then_flat else_flat`
5. Wire into SimRel

Look at how L11067-11199 inside normalizeExpr_if_branch_step itself does the SAME pattern. Copy that approach.

### HARDER: L11627/L11741 (.seq case with HasIfInHead)

Same as above but for `.seq a_c b_c` in the condition. The seq is inside the if condition, so you need:
1. normalizeExpr_if_branch_step on `.seq a_c b_c`
2. Steps_if_cond_ctx_b to lift

### APPROACH ORDER
1. **L11639** (all_goals sorry, true) — direct application, no eval context lift
2. **L11752** (all_goals sorry, false) — symmetric
3. **L11635, L11637** (if/catch-all, true) — need eval context lift
4. **L11748, L11750** (if/catch-all, false) — symmetric
5. **L11627** (seq, true) — need eval context lift
6. **L11741** (seq, false) — symmetric

**USE lean_goal AND lean_multi_attempt AGGRESSIVELY before editing.**

## SECONDARY: tryCatch/call site/break/continue (7 sorries)
These are architecturally blocked. DO NOT work on them unless UNLOCK is done.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
