# proof — Build Steps_*_ctx multi-step lifting lemmas, then close compound sorries

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
SKIP `let_step_sim` entirely.

## STATE: ANF has 22 sorries, ALL in L6400-7414. Down 1 from last run (closed L7135 await .this).

## YOUR EXCELLENT ANALYSIS from last run is correct:
- hasBreakInHead/hasContinueInHead (L6612, L6625) are FALSE as stated — SKIP THEM
- All remaining compound sorries need eval context lifting
- Continuation-independence approach for .return/.yield/.throw/.await is the key

## YOUR TASKS (in priority order):

### TASK 1: Build Steps_*_ctx multi-step context lifting lemmas (HIGHEST PRIORITY)

Single-step versions already exist:
- `step?_seq_ctx` at L1452
- `step?_let_init_ctx` at L1566
- `step?_throw_ctx` at L1549
- `step?_if_cond_step` at L1469

Build multi-step versions by induction on `Flat.Steps`. Place them after the single-step versions (~L1600).

**Template** (adapt for each context):
```lean
private theorem Steps_seq_ctx
    (b : Flat.Expr)
    (hsteps : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs ⟨e', env', heap', trace', funcs', cs'⟩)
    (hnoerr : ∀ ev ∈ evs, ∀ msg, ev ≠ .error msg)
    (hnotval : ∀ sf_mid, -- each intermediate state's expr is not a value
       ... ) :
    Flat.Steps
      ⟨.seq e b, env, heap, trace, funcs, cs⟩
      evs
      ⟨.seq e' b, env', heap', trace', funcs', cs'⟩ := by
  induction hsteps with
  | refl => exact .refl _
  | tail hsteps hstep ih =>
    exact .tail (ih ...) (step?_seq_ctx ...)
```

**Important**: The `hnotval` hypothesis needs to state that EVERY intermediate expression is not a value (not just the initial one). Use `Flat.Steps` induction carefully.

Build these 4 (in order):
1. `Steps_seq_ctx` — uses `step?_seq_ctx`
2. `Steps_throw_ctx` — uses `step?_throw_ctx`
3. `Steps_let_init_ctx` — uses `step?_let_init_ctx`
4. `Steps_if_cond_ctx` — uses `step?_if_cond_step`

### TASK 2: Use Steps_*_ctx to close compound Type A sorries

After building the multi-step lemmas, use them to close:
- **L6778** (throw compound flat_arg): sub-expression steps via IH, lift through `.throw [·]` context
- **L6931** (return compound inner_val): lift through `.return (some [·])` context
- **L7104** (await compound inner_arg): lift through `.await [·]` context
- **L7258** (yield compound inner_val): lift through `.yield (some [·]) d` context

Pattern for each: IH gives multi-step reduction of sub-expr. Steps_*_ctx lifts it through the context. Then single-step rule applies.

### TASK 3: Continuation-independence lemmas (if time permits)

For Categories 2-3 (non-labeled inner value, compound/bindComplex), you identified:
- `.return (some X)`, `.yield (some X)`, `.throw X`, `.await X` all DISCARD outer continuation
- So `normalizeExpr (.return (some X)) k = normalizeExpr X returnK` regardless of k
- This means the IH can use k' = trivialK (satisfying trivial-preserving) for these wrappers

Build ONE continuation-independence lemma for `.throw`:
```lean
private theorem normalizeExpr_throw_k_independent (e : Flat.Expr) (k1 k2 : ...) (n : Nat) :
    (ANF.normalizeExpr (.throw e) k1 n).fst = (ANF.normalizeExpr (.throw e) k2 n).fst
```
If this works, do the same for return/yield/await.

### SKIP THESE (confirmed not provable or blocked):
- L6612 (hasBreakInHead) — FALSE as stated
- L6625 (hasContinueInHead) — FALSE as stated
- L7288 (.let characterization) — bindComplex produces .let
- L6781, L6934, L7107, L7261 (Type B compound — HasXInHead cases) — need break fix first
- L7336, L7367, L7370 (if simulation) — separate approach needed
- L7414 (final sorry) — depends on everything else
- L6409, L6442, L6534, L6567 (non-labeled inner value) — need continuation-independence first
- L6453, L6578, L6595 (compound/bindComplex) — need continuation-independence first

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
