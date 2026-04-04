# proof — Steps_*_ctx is STILL your #1 priority. BUILD THEM NOW.

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

## STATE: ANF has 28 sorry tokens across 12 theorems. Decomposition from hasBreak/hasContinue was GOOD — break_direct + continue_direct are proved.

## SORRY MAP (28 tokens):

### Group A — normalizeExpr_labeled_step_sim (7 sorries): L6531, L6564, L6656, L6689, L6575, L6700, L6717
- BLOCKED: needs continuation-independence (Task 3). Do NOT attempt yet.

### Group B — hasBreakInHead compound (4): L6751, L6753, L6755, L6759
### Group C — hasContinueInHead compound (4): L6781, L6782, L6783, L6784
- BLOCKED: theorem is FALSE as stated for compound cases (wasmspec confirmed). SKIP.

### Group D — throw/return/await/yield compound flat_arg (4): L6937, L7090, L7263, L7417
- CLOSABLE via Steps_*_ctx. YOUR #1 TARGET after building the lifting lemmas.

### Group E — throw/return/await/yield HasXInHead compound (4): L6940, L7093, L7266, L7420
- BLOCKED: needs hasBreak fix first. SKIP.

### Group F — let/seq/if/tryCatch (5): L7447, L7495, L7526, L7529, L7573
- DEFER: needs characterization lemmas.

## YOUR TASKS (in strict priority order):

### TASK 1: BUILD Steps_*_ctx multi-step context lifting lemmas (DO THIS FIRST)

You have been assigned this for 2 runs and haven't built them yet. DO IT NOW.

Single-step versions exist:
- `step?_seq_ctx` at ~L1452
- `step?_let_init_ctx` at ~L1566
- `step?_throw_ctx` at ~L1549

Build multi-step versions. Place them after the single-step versions (~L1600).

**EXACT CODE to write** — start with the simplest one:

```lean
private theorem Steps_throw_ctx
    (hsteps : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs ⟨e', env', heap', trace', funcs', cs'⟩)
    (hnoerr : ∀ ev ∈ evs, ∀ msg, ev ≠ .error msg)
    (hnotval : ∀ (sf_i : Flat.State), Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ _ sf_i →
       sf_i ≠ ⟨e', env', heap', trace', funcs', cs'⟩ → Flat.exprValue? sf_i.expr = none) :
    Flat.Steps
      ⟨.throw e, env, heap, trace, funcs, cs⟩
      evs
      ⟨.throw e', env', heap', trace', funcs', cs'⟩ := by
  induction hsteps with
  | refl => exact .refl _
  | tail hsteps hstep ih =>
    have hmid_notval := hnotval _ (sorry) sorry -- intermediate state not final
    exact .tail (ih (sorry) (sorry)) (step?_throw_ctx hmid_notval.symm ▸ hstep)
```

If the `hnotval` hypothesis is too complex, try a simpler version:

```lean
private theorem Steps_throw_ctx_simple
    (hsteps : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs ⟨e', env', heap', trace', funcs', cs'⟩)
    (hnotval_all : ∀ (sf_i : Flat.State) (evs_i : _),
       Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs_i sf_i →
       Flat.exprValue? sf_i.expr = none) :
    Flat.Steps
      ⟨.throw e, env, heap, trace, funcs, cs⟩
      evs
      ⟨.throw e', env', heap', trace', funcs', cs'⟩ := by
  induction hsteps with
  | refl => exact .refl _
  | tail hsteps hstep ih =>
    exact .tail (ih fun sf evs h => hnotval_all sf evs h) (step?_throw_ctx (hnotval_all _ _ hsteps) ▸ hstep)
```

Use `lean_multi_attempt` to test different formulations. Once Steps_throw_ctx works, adapt for Steps_return_ctx, Steps_await_ctx, Steps_yield_ctx.

### TASK 2: Close Group D compound flat_arg sorries using Steps_*_ctx

After Task 1 is done, use the lifting lemmas to close:
- **L6937** (throw compound flat_arg): IH gives sub-expression steps, Steps_throw_ctx lifts
- **L7090** (return compound inner_val): Steps_return_ctx lifts
- **L7263** (await compound inner_arg): Steps_await_ctx lifts
- **L7417** (yield compound inner_val): Steps_yield_ctx lifts

### TASK 3: Continuation-independence (if time permits)

For Group A (labeled sorries), `.throw X` discards outer continuation:
```lean
normalizeExpr (.throw e) k = normalizeExpr e (fun v => .throw (.trivial v))
```
This means k is irrelevant and can be trivialK for the IH. Prove ONE case.

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
