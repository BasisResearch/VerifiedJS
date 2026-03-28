# wasmspec — STOP TRYING return-some IN step_sim. IT IS 1:N.

## CRITICAL CORRECTION

**L6801 (`| some t => sorry`) in `step_sim` is UNPROVABLE.**

`step_sim` proves `∃ s2', irStep? s2 = some (t, s2')` — a SINGLE IR step.
But `return (some triv)` emits `argCode ++ [return_]` = 2+ IR steps. This is 1:N, not 1:1.

**step_sim_stutter (L7370) ALREADY handles return-some correctly.** All 9 per-trivial lemmas are already wired in there. No work needed on return-some.

The L6801 sorry stays. Move on.

## ACTUAL PRIORITY 0: Prove 1:1 cases in step_sim

Some expression forms in step_sim ARE 1:1 (single IR instruction). Focus on these:

### yield (L6804) and await (L6807)
Check: does ANF `yield`/`await` map to a single IR instruction? Look at `LowerCodeCorr` constructors for `.yield` and `.await`. If the IR is a single instruction, it's 1:1 and provable following the return-none pattern (L6764-6800).

### break (L6813) and continue (L6816)
Check: do these map to single IR instructions (`br label` / `br_if` something)? If so, prove them 1:1 following the return-none pattern.

### labeled (L6810)
Check: does `.labeled label body` map to a single IR `block` instruction? If so, prove 1:1.

### How to check: Use `lean_hover_info` on LowerCodeCorr constructors, or grep for `yield_inv|await_inv|break_inv|continue_inv|labeled_inv` in EmitCodeCorr/LowerCodeCorr.

## PRIORITY 1: callIndirect (L10838) — exfalso?

Check if `.callIndirect` is excluded by `supported`. If `ANF.Expr.supported` or `Flat.Expr.supported` excludes callIndirect, close with `exfalso`.

## PRIORITY 2: Expand step_sim_stutter for 1:N cases

For compound cases (let, seq, if, while, throw, tryCatch) that need N IR steps:
1. Add them as explicit matches in `step_sim_stutter` (like return-some at L7380)
2. Write per-case lemmas (like `step_sim_return_litNull`) showing IR takes N steps with matching observable events

Start with `throw` — it's likely the simplest (1 event, simple IR sequence).

## File: `VerifiedJS/Wasm/Semantics.lean`
## Log to agents/wasmspec/log.md
