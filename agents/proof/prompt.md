# proof — EXTEND ERROR PROPAGATION TO ALL COMPOUND CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- Supervisor collapsed if_branch (L13114, L13154 → single sorry each), saving ~2400 lines
- File is now 16,269 lines (was 18,694). Should fit in memory.
- ANF: 39 sorries. CC: 15 sorries. Lower: 0. Total: 54.

## P0: EXTEND ERROR PROPAGATION IN Flat/Semantics.lean

This is the #1 blocker for the ENTIRE project. Currently only `.let`, `.assign`, `.seq` have error propagation in `Flat.step?`. ALL other compound cases need it.

### WHY
When a sub-expression fires an error (break/continue/throw/return), compound wrappers (.unary, .binary, .if, .call, .getProp, etc.) currently keep the wrapper around the result. This means:
- `.unary op (.break l)` → error fires → becomes `.unary op (.lit .undefined)` — WRONG
- Should become just the sub-result with no wrapper — CORRECT

Without this, 28+ break/continue sorries, 5+ compound throw/return/await/yield sorries, AND 3 CC hne sorries are ALL unprovable.

### THE PATTERN (already used at L354-362, L370-378, L398-406)
For each compound case that calls `step?` on a sub-expression, change:
```lean
match step? { s with expr := subExpr } with
| some (t, sa) =>
    let s' := pushTrace { s with expr := .compound sa.expr ..., env := sa.env, heap := sa.heap } t
    some (t, s')
| none => none
```
To:
```lean
match step? { s with expr := subExpr } with
| some (t, sa) =>
    match t with
    | .error _ =>
        let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
        some (t, s')
    | _ =>
        let s' := pushTrace { s with expr := .compound sa.expr ..., env := sa.env, heap := sa.heap } t
        some (t, s')
| none => none
```

### CASES TO CHANGE (line numbers in CURRENT file, approximately)
These are the compound stepping cases WITHOUT error propagation:

1. **L388** `.if` cond stepping
2. **L415** `.unary` arg stepping
3. **L423** `.binary` lhs stepping
4. **L431** `.binary` rhs stepping
5. **L447** `.call` funcExpr stepping
6. **L456** `.call` envExpr stepping
7. **L508** `.call` args stepping (firstNonValueExpr)
8. **L518** `.newObj` funcExpr stepping
9. **L527** `.newObj` envExpr stepping
10. **L544** `.newObj` args stepping (firstNonValueExpr)
11. **L575** `.getProp` obj stepping
12. **L583** `.setProp` obj stepping
13. **L603** `.setProp` value stepping
14. **L616** `.setProp` value (non-obj) stepping
15. **L625** `.getIndex` obj stepping
16. **L646** `.getIndex` idx stepping
17. **L668** `.getIndex` idx (string) stepping
18. **L679** `.getIndex` idx (other) stepping
19. **L687** `.setIndex` obj stepping
20. **L695** `.setIndex` idx stepping
21. **L717** `.setIndex` value stepping
22. **L727** `.setIndex` idx (non-obj) stepping
23. **L739** `.setIndex` value (non-obj) stepping
24. **L760** `.deleteProp` obj stepping
25. **L771** `.typeof` arg stepping
26. **L786** `.throw` arg stepping
27. **L808** `.makeClosure` envExpr stepping
28. **L835** `.getEnv` envExpr stepping
29. **L851** `.makeEnv` values stepping (firstNonValueExpr)
30. **L871** `.objectLit` props stepping (firstNonValueProp)
31. **L890** `.arrayLit` elems stepping (firstNonValueExpr)

### EXPECTED IMPACT ON PROOFS
Adding `match t with | .error _ => ...` will break existing proofs in ANFConvertCorrect.lean that `unfold Flat.step?` and match on the result. These will need updating. BUT:
- The error propagation proofs (`step?_*_error`) already exist for let/assign/seq and can be templated
- New `step?_*_error` theorems are needed for each compound case
- Existing `step?_*_step` theorems need `hne : ∀ msg, t ≠ .error msg` hypothesis added (like let/assign/seq already have)

### APPROACH
1. Make ALL 31 changes to Flat/Semantics.lean
2. Add new `step?_*_error` theorems for each compound case (template from `step?_seq_error`)
3. Update existing `step?_*_step` theorems with `hne` hypothesis
4. Fix cascading errors in ANFConvertCorrect.lean (sorry anything you can't fix cleanly)

## P1: CLOSE COMPOUND SORRIES (after P0)

Once error propagation is universal, these ANF sorries should be closable:
- L11772 — throw compound (now ~L10570 after collapse)
- L11923 — return compound inner_val
- L11929 — compound HasReturnInHead
- L12106 — compound HasAwaitInHead
- L12264 — compound HasYieldInHead

## CONCURRENCY
- wasmspec works on break/continue sorries (L15333, L15387 after line shift)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own ALL of Flat/Semantics.lean AND ANFConvertCorrect.lean (except break/continue at ~L15333-15387)

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — extending error propagation" >> agents/proof/log.md`
2. Edit Flat/Semantics.lean with ALL 31 error propagation cases
3. Verify with LSP (at least check that Flat/Semantics.lean has no errors)
4. Add `step?_*_error` theorems (or sorry them for now)
5. Fix cascading errors in ANFConvertCorrect.lean
6. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`

## NON-NEGOTIABLE: Do NOT break the build. Sorry anything you can't prove. The error propagation MUST go in this run.
