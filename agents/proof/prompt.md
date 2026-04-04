# proof — YOU HAVE BEEN STUCK ON GROUP D FOR 3 RUNS. CLOSE THEM NOW.

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

## STATE: ANF has 22 sorries. Steps_ctx_lift + 7 wrappers are BUILT (L1737-1853). You built them 3 RUNS AGO. USE THEM.

## SORRY MAP (22 tokens, CURRENT line numbers as of 03:05 UTC):

### Group A — normalizeExpr_labeled_step_sim (7): L6531, L6564, L6575, L6656, L6689, L6700, L6717
- BLOCKED: needs continuation-independence. Do NOT attempt yet.

### Group D — throw/return/await/yield compound (8 sorries):
- **L7122**: throw compound flat_arg ← TARGET #1
- **L7125**: HasThrowInHead compound cases ← TARGET #2
- **L7275**: return compound inner_val ← TARGET #3
- **L7278**: HasReturnInHead compound cases ← TARGET #4
- **L7448**: await compound inner_arg ← TARGET #5
- **L7451**: HasAwaitInHead compound cases ← TARGET #6
- **L7602**: yield compound inner_val ← TARGET #7
- **L7605**: HasYieldInHead compound cases ← TARGET #8

### Group F — let/seq/if/tryCatch (5): L7632, L7680, L7711, L7714, L7758
- DEFER until Group D is done.

### Group G — break/continue dead code (2): L8119, L8170
- DEFER: wasmspec is working on reformulation.

## YOUR ONE AND ONLY TASK: Close Group D sorries (8 sorries → 0)

You have ALL the tools. They compile. You built them. Now USE them.

### How L7122 works (throw compound flat_arg):

The proof state at L7122 is inside `normalizeExpr_throw_step_sim`. The match on `sf.expr` has handled literal, var, this, break, continue cases. The `| _ =>` catches compound expressions (seq, let, assign, if, call, etc.).

For compound flat_arg (L7122):
1. `sf.expr` is compound (not a value/var/this/break/continue)
2. The normalizeExpr produced `.throw (some (.trivial t))` from this compound expr
3. This means sf.expr must have `.throw` at its eval head (HasThrowInHead)
4. The sub-expression (flat_arg) needs to step first
5. Use `Steps_throw_ctx` (L1799) to lift sub-expression steps through the throw context

**CONCRETE APPROACH for L7122:**
```lean
    | _ =>
      -- The sub-expression inside .throw needs to step.
      -- Use HasThrowInHead to get that sf.expr = .throw sub for some sub,
      -- then sub takes a step, and Steps_throw_ctx lifts it.
      sorry
```

Use `lean_goal` at L7122 col 7 to see the EXACT proof state. Then use `lean_multi_attempt` to try tactics.

For L7125 (HasThrowInHead compound): similar — the HasThrowInHead inductive gives compound constructors. Use `lean_goal` at L7125 to see the proof state.

### WORKFLOW:
1. `lean_goal` at L7122 to see proof state
2. `lean_multi_attempt` with candidate tactics
3. If needed, read the HasThrowInHead definition to understand what constructors appear
4. Write the proof, build `lake build VerifiedJS.Proofs.ANFConvertCorrect`
5. Repeat for L7275, L7448, L7602 (same pattern, different context wrapper)
6. Then L7125, L7278, L7451, L7605 (HasXInHead compound cases)

### IF YOU CANNOT CLOSE THEM:
Tell me EXACTLY what the proof state is at L7122 (copy the `lean_goal` output) and what tactic you tried that failed. Do NOT just say "it's hard" — show me the goal.

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
