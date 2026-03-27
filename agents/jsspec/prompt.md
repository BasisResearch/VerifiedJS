# jsspec — INTEGRATE STAGED HELPERS + ANF SUPPORT

## STATUS: Sorry count dropped 99→58. Your staged helpers contributed to this. Now integrate them.

## PRIORITY 0: Install cc_st_lemma.lean @[simp] lemmas into main codebase

The lemmas in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_st_lemma.lean` are verified sorry-free.
They need to go into `VerifiedJS/Proofs/ClosureConvertCorrect.lean` BEFORE the main theorem.

Add these ABOVE the `theorem closureConvert_sim_step` line:
```lean
@[simp] theorem convertExpr_lit_snd (v : Core.Value) (scope : List String)
    (envVar : String) (envMap : Std.HashMap String Nat) (st : Nat) :
    (Flat.convertExpr (.lit v) scope envVar envMap st).snd = st := by
  simp [Flat.convertExpr]

@[simp] theorem convertExpr_this_snd (scope : List String)
    (envVar : String) (envMap : Std.HashMap String Nat) (st : Nat) :
    (Flat.convertExpr .this scope envVar envMap st).snd = st := by
  simp [Flat.convertExpr]

@[simp] theorem convertExpr_var_snd (name : String) (scope : List String)
    (envVar : String) (envMap : Std.HashMap String Nat) (st : Nat) :
    (Flat.convertExpr (.var name) scope envVar envMap st).snd = st := by
  simp [Flat.convertExpr]
```

## PRIORITY 1: Write ANF helper lemmas

The proof agent is pivoting to ANF. It needs helper lemmas for `anfConvert_step_star`.

Write and verify in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_helpers.lean`:

1. **ANF.step?_break**: `ANF.step? (.break label) env heap = some (.error (.breakSignal label), ...)`
2. **ANF.step?_continue**: Similar for continue
3. **ANF.step?_throw**: `ANF.step? (.throw arg) env heap = some (.error (.throwSignal (evalTrivial arg env)), ...)`
4. **ANF.step?_return**: `ANF.step? (.return arg) env heap = some (.return (evalTrivial arg env), ...)`
5. **normalizeExpr inversion lemmas**: What does `normalizeExpr (.break label) k` produce?

Use `lean_hover_info` on `ANF.step?` to understand the definition, then write the simp lemmas.

## PRIORITY 2: Document remaining CC design issues

Update `.lake/_tmp_fix/VerifiedJS/Proofs/design_issues.md` with:
- newObj: Core evaluates atomically, Flat multi-step → stuttering simulation needed
- functionDef: same issue
- Proposed fix: which is less disruptive?

## What NOT to do:
- Do NOT run full `lake build` — use `lake env lean` for individual files
- Do NOT edit Wasm/Semantics.lean
- Be careful editing ClosureConvertCorrect.lean — coordinate with proof agent

## Log progress to agents/jsspec/log.md.
