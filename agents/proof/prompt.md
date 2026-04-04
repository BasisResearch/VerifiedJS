# proof — Build multi-step context lifting lemmas, then close compound sorries

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

## STATE: ANF has 22 sorries, ALL in L6400-7414.

## ⚠️⚠️⚠️ KEY FINDING FROM WASMSPEC ⚠️⚠️⚠️

**hasBreakInHead_flat_error_steps (L6612) is NOT PROVABLE as stated.**
Error events do NOT short-circuit eval contexts in Flat semantics. When `.break label` is inside `.seq (.break label) b`, Flat.step? produces `.seq (.lit .undefined) b`, then steps to `b` — NOT to `.lit .undefined`.

**DO NOT waste time on L6612 or L6625 (hasContinueInHead).**

**Instead**: All 12 compound sorries + 4 non-labeled sorries share ONE common blocker: missing multi-step context lifting lemmas.

## YOUR TASKS (in order):

### TASK 1: Build Steps_*_ctx multi-step context lifting lemmas (HIGHEST PRIORITY)

These are MECHANICAL — just induction on `Flat.Steps` using existing single-step lemmas.

Build these lemmas (add them near the existing single-step versions around L1450-1650):

```lean
-- Multi-step seq context: if e steps to e' in multiple steps, then .seq e b steps to .seq e' b
private theorem Steps_seq_ctx
    (sf : Flat.State) (evs : List Core.TraceEvent) (sf' : Flat.State)
    (b : Flat.Expr)
    (hsteps : Flat.Steps sf evs sf')
    (hsf : sf.expr = .seq e₁ b → False) -- maybe not needed
    : Flat.Steps
        ⟨.seq sf.expr b, sf.env, sf.heap, sf.trace, sf.funcs, sf.callStack⟩
        evs
        ⟨.seq sf'.expr b, sf'.env, sf'.heap, sf'.trace, sf'.funcs, sf'.callStack⟩ := by
  induction hsteps with
  | refl _ => exact Flat.Steps.refl _
  | tail hsteps hstep ih =>
    exact Flat.Steps.tail ih (by -- use step?_seq_ctx here)
```

You need multi-step versions for:
1. `Steps_seq_ctx` — `.seq [·] b` (use `step?_seq_ctx` at L1452)
2. `Steps_let_init_ctx` — `.let name [·] body` (use `step?_let_init_ctx`)
3. `Steps_throw_ctx` — `.throw [·]` (use `step?_throw_ctx`)
4. `Steps_return_some_ctx` — `.return (some [·])` (use `step?_return_some_ctx`)
5. `Steps_await_ctx` — `.await [·]` (use `step?_await_ctx`)
6. `Steps_yield_some_ctx` — `.yield (some [·]) d` (use `step?_yield_some_ctx`)

First `grep -n "step?_seq_ctx\|step?_let_init_ctx\|step?_throw_ctx\|step?_return_some_ctx\|step?_await_ctx\|step?_yield_some_ctx"` to find exact locations of single-step versions. Read them. Then build multi-step versions by induction on Flat.Steps.

### TASK 2: Use Steps_*_ctx to close compound Type A sorries (L6778, L6931, L7104, L7258)

Pattern for each: the sub-expression is compound (not a value). Apply IH to get multi-step reduction to value. Lift through context with Steps_*_ctx. Then apply the final single-step rule.

### TASK 3: Close non-labeled inner value sorries (L6409, L6442, L6534, L6567)

These need TWO-LAYER context lifting (e.g., `.return (some (.return (some [·])))`). Build by composing two Steps_*_ctx calls.

### SKIP THESE:
- L6612 (hasBreakInHead) — NOT PROVABLE as stated
- L6625 (hasContinueInHead) — NOT PROVABLE as stated
- L7288 (.let characterization) — bindComplex PRODUCES .let
- L6781, L6934, L7107, L7261 (Type B compound — HasXInHead cases) — depend on fixing HasBreakInHead first
- L7336, L7367, L7370 (if simulation) — separate approach needed
- L7414 (final sorry) — depends on everything else

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
