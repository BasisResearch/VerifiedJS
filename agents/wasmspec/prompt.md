# wasmspec — Prove compound if infrastructure lemmas in ANF

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** edit Flat/Semantics.lean — it's DONE (0 sorries), leave it alone
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~2GB available.
- You CAN edit ANFConvertCorrect.lean ONLY
- Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`

## MEMORY WARNING
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## CONCURRENCY: proof agent also edits ANFConvertCorrect.lean
- proof agent works on L9536 (tryCatch step sim) and L9079-9084 (let compound)
- **YOU** own L9273-9322 (infrastructure lemmas) and L9326+ (normalizeExpr_if_step_sim)
- DO NOT touch lines 9060-9090 or 9508-9540

## STATUS: GREAT PROGRESS — 4 inline sorries → 2 infrastructure lemmas (net -2)

You successfully consolidated the 4 if compound inline sorries into 2 well-typed infrastructure lemmas:
- `normalizeExpr_if_compound_true_sim` (L9273-9298) — sorry
- `normalizeExpr_if_compound_false_sim` (L9300-9322) — sorry

## YOUR TASK: Prove these 2 infrastructure lemmas

Both lemmas have the same structure. The goal is:
Given `normalizeExpr sf_expr k` produces `.if cond then_ else_`, and `evalTrivial env cond = .ok v`,
show that Flat can step from `⟨sf_expr, env, heap, trace, funcs, cs⟩` to a state matching `then_` (or `else_`).

### Proof strategy: case analysis on sf_expr

1. **Use `lean_goal` at L9298 to see exact proof state**

2. **Key insight**: Only `.if` in sf_expr can produce `.if` through normalizeExpr.
   - `normalizeExpr (.if c t e) k` normalizes c, then wraps in .if
   - No other constructor produces .if (seq→.let, let→.let, etc.)

3. **Case split on sf_expr**:
   - Most constructors: derive contradiction (normalizeExpr doesn't produce .if)
   - `.if c_flat then_flat else_flat`: the actual case to prove
     - normalizeExpr normalizes c_flat → trivial cond
     - Flat steps: `.if c_flat ...` → evaluate c_flat to value → branch
     - If c_flat is already a value (lit/var/this): single Flat step
     - If c_flat is compound: need multi-step sim (this is the hard part — can sorry initially)

4. **Start with the easy path**: prove the case where c_flat is already a trivial expression (lit/var/this). Sorry the compound sub-case. Even proving the trivial case narrows what's left.

### Template:
```lean
  cases sf_expr with
  | lit | var | this | break | continue | while_ | labeled | tryCatch | return | throw | yield | await =>
    -- These don't produce .if through normalizeExpr
    simp [ANF.normalizeExpr] at hnorm
    -- (may need more work for some constructors)
    sorry  -- placeholder for contradiction derivation
  | «if» c_flat then_flat else_flat =>
    -- The real case: normalizeExpr (.if c t e) k normalizes c then wraps
    sorry -- main proof here
  | _ => sorry -- remaining constructors: derive contradiction
```

## PRIORITY ORDER
1. L9298 (true branch infrastructure) — prove or narrow
2. L9322 (false branch) — structurally identical to true

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
