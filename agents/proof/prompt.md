# proof — Steps_*_ctx are BUILT. Now USE them to close Group D sorries.

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

## STATE: ANF has 22 sorries. Steps_ctx_lift + 7 wrappers are BUILT at L1737-1853. EXCELLENT WORK.

## SORRY MAP (22 tokens, CURRENT line numbers):

### Group A — normalizeExpr_labeled_step_sim (7): L6531, L6564, L6575, L6656, L6689, L6700, L6717
- BLOCKED: needs continuation-independence (Task 2). Do NOT attempt yet.

### Group D — throw/return/await/yield compound flat_arg (4 sorries, 4 HasXInHead sorries = 8 total):
- **L6894**: throw compound flat_arg ← YOUR #1 TARGET
- **L6897**: HasThrowInHead compound cases
- **L7047**: return compound inner_val ← YOUR #2 TARGET
- **L7050**: HasReturnInHead compound cases
- **L7220**: await compound inner_arg ← YOUR #3 TARGET
- **L7223**: HasAwaitInHead compound cases
- **L7374**: yield compound inner_val ← YOUR #4 TARGET
- **L7377**: HasYieldInHead compound cases

### Group F — let/seq/if/tryCatch (5): L7404, L7452, L7483, L7486, L7530
- DEFER: needs characterization lemmas.

### Group G — anfConvert_step_star break/continue dead code (2): L7891, L7942
- DEFER: needs hasBreak/hasContinue reformulation (wasmspec working on this).

## YOUR TASKS (in strict priority order):

### TASK 1: Close Group D compound flat_arg sorries using Steps_*_ctx (DO THIS FIRST)

You have Steps_throw_ctx at L1799, Steps_return_some_ctx at L1828, Steps_await_ctx at L1848, Steps_yield_some_ctx at L1838.

**Start with L6894** (throw compound flat_arg). The pattern:
1. The IH gives you `Flat.Steps` for the sub-expression (flat_arg stepping to a value)
2. Apply `Steps_throw_ctx` to lift those steps through `.throw [·]`
3. The result gives you `Flat.Steps` for `.throw flat_arg` stepping to `.throw val`
4. Then one more step handles `.throw val` → emit throw event

Read L6860-6897 to understand the proof state. The sorry at L6894 is inside a match on `sf.expr` cases — the compound cases (seq, let, assign, if, call, etc.) need the sub-expression to step first, then the throw context wrapping.

Use `lean_goal` at L6894 to see the exact proof state. Then try:
```lean
    | _ =>
      -- Use IH to step sub-expression, then Steps_throw_ctx to lift
      obtain ⟨sf_mid, evs_sub, hsteps_sub, hsf_mid⟩ := ih_sub ...
      exact ⟨_, _, Steps_throw_ctx hsteps_sub hpres, ...⟩
```

Use `lean_multi_attempt` at each sorry to test closing tactics.

After L6894, do the same for L7047 (return), L7220 (await), L7374 (yield), adapting the context wrapper.

### TASK 2: Continuation-independence (if time permits)

For Group A (labeled sorries), `.throw X` discards outer continuation:
```lean
normalizeExpr (.throw e) k = normalizeExpr e (fun v => .throw (.trivial v))
```
This means k is irrelevant and can be trivialK for the IH. Prove ONE case.

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
