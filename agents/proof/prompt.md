# proof — Fix Flat.step? abrupt completion propagation

## RULES
- Edit: ANFConvertCorrect.lean AND Flat/Semantics.lean
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~3.5GB free. USE LSP ONLY — no `lake build`.

## CONCURRENCY
- wasmspec works on L12268-12372 (while cases) and L13976-15525 (if_branch)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own everything else in ANFConvertCorrect.lean + Flat/Semantics.lean

## STATUS: 67 sorries total. ZERO progress in 4 days.

## ===== ROOT CAUSE ANALYSIS (from supervisor) =====

The compound sorries (L11713, L11870, L12047, L12205, L17701, L17754) are **unprovable as stated** because:

1. `normalizeExpr_throw_step_sim` requires `sf'.env = sf.env ∧ sf'.heap = sf.heap`
2. For compound cases like `seq_left` (expr = `.seq a b` with throw in `a`):
   - Flat.step? steps `a` through the seq context
   - `a` eventually throws → error event, `a` becomes `.lit .undefined`
   - Then `.seq (.lit .undefined) b` steps to `b`
   - `b` EXECUTES (dead code!) and can modify env/heap
3. So `sf'.env = sf.env` is FALSE for compound cases

**The fix**: Modify `Flat.step?` in Flat/Semantics.lean to propagate abrupt completions.

## ===== P0: FIX Flat.step? (Flat/Semantics.lean) =====

Current behavior at L382 in Flat/Semantics.lean:
```lean
| .seq a b =>
    match exprValue? a with
    | some _ => -- a is value → step to b
    | none => match step? { s with expr := a } with
              | some (t, sa) => -- step a, stay in .seq sa.expr b
```

**What needs to change**: When `a` is an abrupt completion literal (the result of throw/return/break/continue having already executed), propagate it instead of continuing to `b`.

Specifically, add a check: if `a` is `.lit .undefined` AND the last trace event was an error/abrupt event, then the seq should propagate the terminal state rather than stepping to `b`.

BUT WAIT — this approach is fragile. A better approach:

**Add explicit abrupt value forms to Flat.Expr** or **check if `a` stepped to an error event and stop**.

Actually, the SIMPLEST fix that doesn't change the Expr type:

In the `.seq a b` case of step?, after stepping `a`:
```lean
| some (t, sa) =>
    -- If the step produced an error event AND sa.expr is terminal (.lit .undefined),
    -- then propagate the terminal state instead of wrapping in .seq
    if sa.expr matches .lit .undefined then
      -- Abrupt completion: don't execute b
      some (t, sa)  -- propagate directly
    else
      some (t, { s with expr := .seq sa.expr b, ... })
```

NO — this is WRONG. `a` can legitimately become `.lit .undefined` through normal execution (e.g., `a = .assign x (.lit .undefined)`), and we still want to execute `b` in that case.

**Better approach**: Only propagate when the trace event is `.error msg`. Error events come from throw/break/continue/return:

```lean
| some (t, sa) =>
    match t with
    | .error _ =>
        -- Abrupt completion produced error event: propagate without executing b
        let s' := pushTrace { s with expr := sa.expr, env := sa.env, heap := sa.heap } t
        some (t, s')
    | _ =>
        -- Normal step: continue in seq context
        let s' := pushTrace { s with expr := .seq sa.expr b, env := sa.env, heap := sa.heap } t
        some (t, s')
```

This makes `.seq` propagate error events from `a` without executing `b`.

### CONCRETE STEPS:

1. **Read** Flat/Semantics.lean around L382 to see exact current code
2. **Read** `step?_seq_ctx` and `Flat_step?_seq_step` in ANFConvertCorrect.lean to understand what depends on seq stepping behavior
3. **Search** for all uses of `.seq` stepping patterns: `lean_local_search "step?_seq"`
4. **Check** how many existing proofs reference seq step behavior — these will break
5. **Make the change** to Flat.step? ONLY for the `.seq a b` case
6. **Also apply** the same fix to `.let name init body`, `.call funcExpr envExpr args`, and other compound expression cases where inner stepping wraps in an outer context
7. **Run lean_diagnostic_messages** on Flat/Semantics.lean to check for immediate breakage
8. **Fix** broken proofs in ANFConvertCorrect.lean

### IMPORTANT: Start small
- First, change ONLY `.seq a b` error propagation
- Check what breaks
- If manageable, proceed to other compound forms
- If catastrophic, REVERT and document what went wrong

### WHAT THIS UNBLOCKS:
If Flat.step? propagates errors through seq, then for `seq_left h` case:
- Flat.Steps from `⟨.seq a b, env, heap, trace, funcs, cs⟩` now end at `⟨.lit .undefined, env, heap, ...⟩`
- env/heap ARE preserved because b never executes
- The theorem becomes provable via depth induction

This unblocks: L11713 (throw), L11870 (return), L12047 (await), L12205 (yield), L17701 (break), L17754 (continue) = **6+ sorries** directly, plus enables depth induction for many more.

## ===== FALLBACK: If Flat.step? change is too risky =====

If too many proofs break, instead:
1. Case-split L11713 from `| _ => sorry` into individual HasThrowInHead constructors
2. For each constructor, write a sorry with a detailed comment
3. This doesn't close sorries but makes the problem decomposed

## WORKFLOW
1. Start with reading Flat/Semantics.lean .seq case
2. Search for all proofs that depend on seq stepping behavior
3. Make the minimal change
4. Check breakage
5. Fix broken proofs
6. Verify with lean_diagnostic_messages

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
