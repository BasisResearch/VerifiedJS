# proof — Build HasTryCatchInHead infrastructure, THEN close L9536

## RULES
- Edit: ANFConvertCorrect.lean, Flat/Semantics.lean, AND EndToEnd.lean
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~2GB available.
Check with: `ps aux | grep "lake build" | grep -v grep | wc -l` — only build if count ≤ 1.

## BUILD COORDINATION — CRITICAL
wasmspec is ALSO building ANFConvertCorrect. **Check before building:**
```bash
ps aux | grep "lake build" | grep -v grep | wc -l
```
If count > 0, WAIT. Do not start a build. Use `lean_goal` / `lean_multi_attempt` via LSP instead of full builds while waiting.

## STATUS: You crashed at 06:40 without adding HasTryCatchInHead. Start fresh.

## TASK 1: Define HasTryCatchInHead — INSERT AT L7100 (after HasIfInHead_not_value)

Model EXACTLY on HasIfInHead (L7054-7098). Create:

```lean
/-! ## HasTryCatchInHead: tracks .tryCatch in CPS-head position -/

section TryCatchInHead

set_option autoImplicit true in
mutual
inductive HasTryCatchInHead : Flat.Expr → Prop where
  | tryCatch_direct : HasTryCatchInHead (.tryCatch body cp cb fin)
  | seq_left : HasTryCatchInHead a → HasTryCatchInHead (.seq a b)
  | seq_right : HasTryCatchInHead b → HasTryCatchInHead (.seq a b)
  | let_init : HasTryCatchInHead init → HasTryCatchInHead (.let name init body)
  | getProp_obj : HasTryCatchInHead obj → HasTryCatchInHead (.getProp obj prop)
  | setProp_obj : HasTryCatchInHead obj → HasTryCatchInHead (.setProp obj prop val)
  | setProp_val : HasTryCatchInHead val → HasTryCatchInHead (.setProp obj prop val)
  | binary_lhs : HasTryCatchInHead lhs → HasTryCatchInHead (.binary op lhs rhs)
  | binary_rhs : HasTryCatchInHead rhs → HasTryCatchInHead (.binary op lhs rhs)
  | unary_arg : HasTryCatchInHead arg → HasTryCatchInHead (.unary op arg)
  | typeof_arg : HasTryCatchInHead arg → HasTryCatchInHead (.typeof arg)
  | deleteProp_obj : HasTryCatchInHead obj → HasTryCatchInHead (.deleteProp obj prop)
  | assign_val : HasTryCatchInHead val → HasTryCatchInHead (.assign name val)
  | call_func : HasTryCatchInHead f → HasTryCatchInHead (.call f env args)
  | call_env : HasTryCatchInHead env → HasTryCatchInHead (.call f env args)
  | call_args : HasTryCatchInHeadList args → HasTryCatchInHead (.call f env args)
  | newObj_func : HasTryCatchInHead f → HasTryCatchInHead (.newObj f env args)
  | newObj_env : HasTryCatchInHead env → HasTryCatchInHead (.newObj f env args)
  | newObj_args : HasTryCatchInHeadList args → HasTryCatchInHead (.newObj f env args)
  | if_cond : HasTryCatchInHead c → HasTryCatchInHead (.if c t e)
  | return_some_arg : HasTryCatchInHead v → HasTryCatchInHead (.return (some v))
  | yield_some_arg : HasTryCatchInHead v → HasTryCatchInHead (.yield (some v) d)
  | throw_arg : HasTryCatchInHead arg → HasTryCatchInHead (.throw arg)
  | await_arg : HasTryCatchInHead arg → HasTryCatchInHead (.await arg)
  | getIndex_obj : HasTryCatchInHead obj → HasTryCatchInHead (.getIndex obj idx)
  | getIndex_idx : HasTryCatchInHead idx → HasTryCatchInHead (.getIndex obj idx)
  | setIndex_obj : HasTryCatchInHead obj → HasTryCatchInHead (.setIndex obj idx val)
  | setIndex_idx : HasTryCatchInHead idx → HasTryCatchInHead (.setIndex obj idx val)
  | setIndex_val : HasTryCatchInHead val → HasTryCatchInHead (.setIndex obj idx val)
  | getEnv_env : HasTryCatchInHead env → HasTryCatchInHead (.getEnv env idx)
  | makeClosure_env : HasTryCatchInHead env → HasTryCatchInHead (.makeClosure funcIdx env)
  | makeEnv_values : HasTryCatchInHeadList values → HasTryCatchInHead (.makeEnv values)
  | objectLit_props : HasTryCatchInHeadProps props → HasTryCatchInHead (.objectLit props)
  | arrayLit_elems : HasTryCatchInHeadList elems → HasTryCatchInHead (.arrayLit elems)

inductive HasTryCatchInHeadList : List Flat.Expr → Prop where
  | head : HasTryCatchInHead e → HasTryCatchInHeadList (e :: rest)
  | tail : HasTryCatchInHeadList rest → HasTryCatchInHeadList (e :: rest)

inductive HasTryCatchInHeadProps : List (Flat.PropName × Flat.Expr) → Prop where
  | head : HasTryCatchInHead e → HasTryCatchInHeadProps ((name, e) :: rest)
  | tail : HasTryCatchInHeadProps rest → HasTryCatchInHeadProps (p :: rest)
end

private theorem HasTryCatchInHead_not_value (e : Flat.Expr)
    (h : HasTryCatchInHead e) : Flat.exprValue? e = none := by
  cases h <;> simp [Flat.exprValue?]

end TryCatchInHead
```

**STOP after inserting this. Verify with `lean_diagnostic_messages` at line 7100. Do NOT build yet.**

## TASK 2: Prove normalizeExpr_tryCatch_or_k — INSERT after HasTryCatchInHead

Model on `normalizeExpr_if_or_k` (search for it with grep). This lemma says:
"If normalizeExpr e k produces .tryCatch, then either HasTryCatchInHead e, or k produced the .tryCatch."

**Find normalizeExpr_if_or_k first**: `grep -n "normalizeExpr_if_or_k" VerifiedJS/Proofs/ANFConvertCorrect.lean`

Copy its ENTIRE structure, replacing `.if` → `.tryCatch`, `HasIfInHead` → `HasTryCatchInHead`.

## TASK 3: Prove normalizeExpr_tryCatch_implies_hasTryCatchInHead

Trivial once Task 2 is done — use normalizeExpr_tryCatch_or_k, then derive contradiction from hk.

## TASK 4: Use in normalizeExpr_tryCatch_step_sim (L9536)

Replace the sorry at L9536 with:
```lean
  have htc_head := normalizeExpr_tryCatch_implies_hasTryCatchInHead sf.expr k hk body catchParam catchBody finally_ n m hnorm
  cases htc_head with
  | tryCatch_direct => sorry -- MAIN CASE: direct tryCatch simulation
  | _ => sorry -- compound cases: deferred
```

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L9273-9322 (if compound infrastructure) ONLY
- You insert at L7100 and work on L9536. DON'T touch L9273-9322.

## PRIORITY ORDER
1. HasTryCatchInHead definition (Task 1) — INSERT at L7100, verify with LSP
2. normalizeExpr_tryCatch_or_k (Task 2)
3. normalizeExpr_tryCatch_implies_hasTryCatchInHead (Task 3)
4. Wire into L9536 (Task 4)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
