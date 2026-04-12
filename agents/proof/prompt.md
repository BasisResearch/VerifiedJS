# proof — CLOSE 18 INFRASTRUCTURE SORRIES (HasThrowInHead_step_nonError)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T02:05
- ANF: 48 real sorries (30 original + 18 you added). CC: 15. Total: **63**.
- You added 18 infrastructure sorries at L14919-14936 for HasThrowInHead_step_nonError.
- K' refactor is DEAD — confirmed it cannot work. Do NOT revisit.
- **Sorry count went UP by 21. This is a CRISIS. Close your infrastructure sorries NOW.**

## P0: CLOSE 18 HasThrowInHead_step_nonError CASES (L14919-14936) — HIGHEST PRIORITY

These 18 cases all follow the SAME pattern as the 16 proved cases above them.

### The Pattern (from your proved cases):
Each case has form:
```lean
| constructor h =>
  cases hthrow
  case head_case => -- HasThrowInHead in the sub-expression being stepped
    -- Use IH (ih) with h and the head HasThrowInHead
    exact HasThrowInHead.constructor (ih h head_throw)
  case other_cases => -- HasThrowInHead in a different sub-expression
    -- The step only affects the sub-expression matching the constructor
    -- Other sub-expressions are unchanged, so HasThrowInHead is preserved
    exact HasThrowInHead.other_constructor unchanged_throw
```

### The 18 sorry cases (multi-context — 2+ sub-expressions):
```
setProp_obj, setProp_val, binary_lhs, binary_rhs,
getIndex_obj, getIndex_idx, setIndex_obj, setIndex_idx, setIndex_val,
call_func, call_env, call_args,
newObj_func, newObj_env, newObj_args,
makeEnv_values, objectLit_props, arrayLit_elems
```

### For each:
1. `lean_goal` at the sorry line
2. The HasThrowInHead can be in the stepped sub-expression OR another sub-expression
3. For the stepped sub-expression: apply IH
4. For other sub-expressions: they didn't change, reconstruct HasThrowInHead
5. For list/props cases (call_args, newObj_args, makeEnv_values, objectLit_props, arrayLit_elems): use your proved HasThrowInHeadList/Props helpers (append_right, firstNonValue, reconstruct)

### DO THEM IN ORDER: setProp_obj first, then setProp_val, etc.
### VERIFY EACH with lean_diagnostic_messages BEFORE moving to next.

**Expected: -18 sorries (infrastructure cleanup)**

## P1: USE INFRASTRUCTURE TO CLOSE L14196 (compound throw) — AFTER P0

Once HasThrowInHead_step_nonError is sorry-free:
1. Write `HasThrowInHead_Steps_steppable` (~50 lines, multi-step version)
2. In `hasThrowInHead_compound_throw_step_sim` at L14196, use Steps_steppable + error propagation

**Expected: -1 sorry**

## P2: If-branch K-mismatch (L23525, L23565) — only if P0+P1 done
These might be closeable now. Check if the existing normalizeExpr infrastructure suffices.

## DO NOT WORK ON:
- K' refactor (DEAD)
- L17182 (wasmspec)
- ClosureConvertCorrect.lean
- Any deep compound cases (L22464+)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — closing 18 HasThrowInHead infrastructure sorries" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
