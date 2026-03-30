# proof — Close ANF throw case (L4413)

## RULES
- Edit: ANFConvertCorrect.lean (primary)
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ONLY: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -x lake` first — do NOT start if one runs.
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches the shell string)

## MEMORY: 7.7GB total, NO swap. Kill stale lean procs.

## CURRENT STATE (18:05 Mar 30)
- ANF: 19 sorries
  - 7 depth-induction (L3825-3923) — skip for now
  - 2 consolidated context (L4116, L4327) — skip for now
  - 10 expression-case (3 throw sub-sorries + 7 others): **YOUR TARGET**

## YOUR TARGET: Close the throw case (L4413, L4417, L4420)

You already decomposed the throw case into 3 sub-sorries. Good. Now close them.

### L4413: Two Flat steps for `.throw (.var name)` → `.throw (.lit v)` → `.lit .undefined`

The proof state has:
- `env : Flat.Env` (from sf)
- `name : String` (the variable name)
- `v : Core.Value` such that `env.lookup name = some v` (from `hwf_var` and `hv`)
- `hv : ANF.Env.lookup env name = some v`

You need to construct 2 Flat steps:
1. Step `.throw (.var name)` with env lookup succeeding:
   - `exprValue? (.var name) = none` (var is not a value)
   - `step? { sf | .var name } = some (.silent, { sf | .lit v })` (var resolves)
   - So `step? { sf | .throw (.var name) } = some (.silent, { sf | .throw (.lit v) })`

2. Step `.throw (.lit v)`:
   - `exprValue? (.lit v) = some v` (lit is a value)
   - `step? { sf | .throw (.lit v) } = some (.error (valueToString v), { sf | .lit .undefined })`

Use `Flat.Steps` constructor to combine these 2 steps.

Try `lean_goal` at L4413 first to see the exact goal. Then construct the proof:

```lean
-- Approach:
-- Step 1: .throw (.var name) →[.silent]→ .throw (.lit v)
have hstep1 : Flat.step? { sf with expr := .throw (.var name) } =
    some (.silent, pushTrace { sf with expr := .throw (.lit v) } .silent) := by
  simp [Flat.step?, Flat.exprValue?, Flat.Env.lookup, hv]
-- Step 2: .throw (.lit v) →[.error ...]→ .lit .undefined
have hstep2 : Flat.step? (pushTrace { sf with expr := .throw (.lit v) } .silent) =
    some (.error (Flat.valueToString v), pushTrace { ... } (.error ...)) := by
  simp [Flat.step?, Flat.exprValue?]
-- Combine:
exact ⟨[.silent, .error (Flat.valueToString v)], final_state, Flat.Steps.cons hstep1 (Flat.Steps.cons hstep2 Flat.Steps.nil), ...⟩
```

The exact details depend on the goal. Use `lean_goal` and `lean_multi_attempt` to refine.

### L4417: Non-var trivial case

If `arg ≠ .var name` (the trivial is a literal), the throw case should be even simpler:
- `exprValue? (.lit v) = some v` → one step: `.throw (.lit v)` → `.error ...`

### L4420: Non-throw outer expression case

This is the fallthrough for when `normalizeExpr` produces `.throw arg` but the original
expression wasn't directly `.throw`. Use `normalizeExpr_throw_or_k` to determine how the
throw was introduced. If it came from `k`, then the outer expression was already handled
by the continuation. If it came from HasThrowInHead, use the has-throw-in-head stepping lemmas.

## PRIORITY ORDER:
1. L4413 (throw .var name — 2 Flat steps)
2. L4417 (throw literal — 1 Flat step)
3. L4420 (indirect throw)
4. L4451 (return case — same pattern as throw)

## DO NOT TOUCH:
- Depth-induction cases (L3825-3923)
- Consolidated context cases (L4116, L4327)
- ClosureConvertCorrect.lean — jsspec and wasmspec own this

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ANFConvertCorrect.lean`
3. Log to agents/proof/log.md with sorry count before/after
