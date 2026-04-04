# proof — CLOSE SORRIES. UNBLOCK NoNestedAbrupt.

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

## ‼️ SORRY COUNT WENT UP: 23 → 26. UNACCEPTABLE. ‼️
You added 3 sorries at L4472/4478/4484 (mutual inductive bridge theorems) and 2 from decomposition, closed only 1. NET +3. Fix this NOW.

## STATE: ANF has 26 sorry lines. 8 runs without net sorry reduction.

## PRIORITY 1 (BLOCKING EVERYTHING): Close L4472/4478/4484 mutual induction sorries

These 3 sorries (`hasThrowInHead_implies_hasAbruptCompletion` and list/props variants) are BLOCKING the entire NoNestedAbrupt framework. wasmspec wrote 12 absurd lemmas that ALL depend on L4472. Until you close these 3, the NoNestedAbrupt approach is useless.

### The problem
`HasThrowInHead`, `HasThrowInHeadList`, `HasThrowInHeadProps` are mutually inductive. Lean 4 no longer supports `induction h with` on them directly.

### The fix: Use the generated mutual recursor

```lean
private theorem hasThrowInHead_implies_hasAbruptCompletion :
    HasThrowInHead e → hasAbruptCompletion e = true := by
  intro h
  -- Use the mutual recursor directly:
  induction h with
  | throw_direct => simp [hasAbruptCompletion]
  | seq_left _ ih => simp [hasAbruptCompletion, ih]
  | seq_right _ ih => simp [hasAbruptCompletion, ih]
  -- ... etc for all constructors
```

If `induction h with` doesn't work, try these alternatives IN ORDER:
1. `cases h` + recursive `apply` (if non-recursive cases suffice — they DON'T here)
2. Use `@HasThrowInHead.rec` explicitly as a term-mode proof:
```lean
private theorem hasThrowInHead_implies_hasAbruptCompletion :
    HasThrowInHead e → hasAbruptCompletion e = true :=
  @HasThrowInHead.rec
    (fun e _ => hasAbruptCompletion e = true)
    (fun es _ => hasAbruptCompletionList es = true)
    (fun ps _ => hasAbruptCompletionProps ps = true)
    (by simp [hasAbruptCompletion])  -- throw_direct
    (fun _ ih => by simp [hasAbruptCompletion, ih])  -- seq_left
    (fun _ ih => by simp [hasAbruptCompletion, ih])  -- seq_right
    -- ... one case per constructor
```
3. Try `lean_multi_attempt` with both approaches to see which Lean accepts
4. If `.rec` doesn't exist, check `lean_hover_info` on `HasThrowInHead` to find the actual recursor name

### For the List/Props variants:
The `.rec` recursor handles all 3 mutuals simultaneously. The `(fun es _ => ...)` and `(fun ps _ => ...)` motives cover the list/props variants. You get all 3 theorems from one `.rec` application — just project out the components.

### DO THIS FIRST. Use lean_goal at each sorry, then lean_multi_attempt to test approaches.

## PRIORITY 2: After P1, close TRIVIAL_CHAIN_IN_THROW (L7450)

Same approach as before: case split on `e`, use `isTrivialChain e = true` to eliminate most cases, then handle lit/var/this.

## PRIORITY 3: After P2, use NoNestedAbrupt to close NESTED_THROW (L7444)

Add `hna : NoNestedAbrupt sf.expr` hypothesis to `normalizeExpr_throw_compound_case`. Then the HasThrowInHead branch becomes:
```lean
exact absurd (hasThrowInHead_implies_hasAbruptCompletion hth)
  (by have := NoNestedAbrupt.throw_arg_abruptFree hna; simp [this])
```
This pattern works for ALL Group D HasXInHead sorries — it's the ENTIRE point of NoNestedAbrupt.

## DO NOT:
- Add new inductive types or infrastructure > 20 lines
- Work on Group A, F, or G sorries
- Analyze without writing proof code

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
