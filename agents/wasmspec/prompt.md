# wasmspec — CLOSE WASM SORRY CASES

## STATUS: 14 actual sorries in Wasm/Semantics.lean. Runs taking 2+ hours or crashing. FOCUS ON ONE CASE AT A TIME.

## CURRENT SORRIES:
- L6738-6759: compound cases (let, seq, if, while_, throw, tryCatch) — 6 sorries, 1:N stepping
- L6801: return-some — 1 sorry, 1:N stepping
- L6804: yield — 1 sorry
- L6807: await — 1 sorry
- L6810: labeled — 1 sorry
- L6813: break — 1 sorry
- L6816: continue — 1 sorry
- L10776: call — 1 sorry (trap alignment)
- L10831: call stack underflow — 1 sorry
- L10835: call successful — 1 sorry (multi-frame)
- L10838: callIndirect — 1 sorry

## STOP: yield/await/break/continue may NOT be in supported subset
Check `Expr.supported` in `VerifiedJS/Core/Syntax.lean` L138-165:
- `.yield _ _` → **false** (unsupported!)
- `.await _` → **false** (unsupported!)
- `.break _` → **true** (supported, via `| _ => true`)
- `.continue _` → **true** (supported)

So yield (L6804) and await (L6807) can be closed with **exfalso** if the step_sim theorem has a supported hypothesis. CHECK: does `step_sim` at L6700+ have `h_supported` or similar? If yes:
```lean
| .yield arg delegate => exfalso; simp [ANF.Expr.supported] at h_supported
| .await arg => exfalso; simp [ANF.Expr.supported] at h_supported
```

## PRIORITY 0: Close yield and await with exfalso (-2 sorries)

1. Read the theorem signature around L6700 to find the supported hypothesis
2. If it exists: close yield and await with `exfalso; simp [supported] at h_supported`
3. If NOT: check if supported flows through from `compiler_correct` and add it

## PRIORITY 1: Close callIndirect with exfalso (-1 sorry)

L10838: `callIndirect` is likely not in the supported subset. Check if `ANF.Expr.supported` excludes it or if there's an IR-level supported predicate. If unsupported:
```lean
| .callIndirect typeIdx => exfalso; simp [supported] at h_supported
```

## PRIORITY 2: break/continue (L6813, L6816) — check IR emission

Break and continue ARE supported. Check what `lowerExpr` produces for break/continue:
```
grep -n "break\|continue" VerifiedJS/Wasm/Lower.lean | head -20
```

If break maps to a single IR instruction (e.g., `br label`), follow the return-none pattern at L6764-6800:
1. Invert LowerCodeCorr to get the IR instruction
2. Show ANF step? produces the event
3. Show irStep? on the instruction produces a matching step
4. Construct the new LowerSimRel

## PRIORITY 3: labeled (L6810)

`.labeled label body` maps to IR `block` instruction. Check if there's already a `block` case proved elsewhere (L10839+ looks like it handles `block`). If so, the labeled case may just delegate to the block handling.

## DO NOT ATTEMPT
- Compound cases (L6738-6759): these are 1:N and complex
- return-some (L6801): 1:N stuttering, template exists but not trivial
- call cases (L10776, 10831, 10835): needs multi-frame rework

## FILE: `VerifiedJS/Wasm/Semantics.lean`
## LOG to agents/wasmspec/log.md

## CRITICAL: Keep runs SHORT. Target ONE case, close it, build, log. Don't try to solve everything.
