# proof — CLOSE REMAINING 4 INFRASTRUCTURE + COMPOUND THROW

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T03:05
- ANF: 35 real sorries (down from 48!). CC: 12. Total: **47** (was 63).
- You closed 14 of 18 HasThrowInHead infrastructure sorries. EXCELLENT WORK.
- 4 infrastructure sorries remain. These are the list/props multi-context cases.

## P0: CLOSE 4 REMAINING HasThrowInHead_step_nonError CASES — HIGHEST PRIORITY

The remaining 4 are at approximately L15136, L15168, L15189, L15190:
```
call_args, newObj_args, objectLit_props, arrayLit_elems
```

These are LIST/PROPS cases. Use your proved helpers:
- `HasThrowInHeadList.append_right`
- `HasThrowInHeadList.firstNonValue`
- `HasThrowInHeadList.reconstruct`
- `HasThrowInHeadProps.append_right`
- `HasThrowInHeadProps.firstNonValue`
- `HasThrowInHeadProps.reconstruct`

For each:
1. `lean_goal` at the sorry line
2. The HasThrowInHead is in a list/props element that was stepped
3. Use list decomposition: split at the stepped element, apply IH, reconstruct
4. Verify with `lean_diagnostic_messages`

**Expected: -4 sorries → ANF drops to 31**

## P1: CLOSE L14196 (compound throw) — AFTER P0

Once HasThrowInHead_step_nonError is sorry-free:
1. Write `HasThrowInHead_Steps_steppable` (~50 lines, multi-step version using step_nonError)
2. In `hasThrowInHead_compound_throw_step_sim` at L14196, use Steps_steppable + error propagation
3. This may need to handle both normal steps (HasThrowInHead preserved) and the final throw step

**Expected: -1 sorry → ANF drops to 30**

## P2: If-branch K-mismatch (L23779, L23819) — only if P0+P1 done

These 2 sorries are collapsed if-branch cases. Check if the existing normalizeExpr infrastructure now suffices. `lean_goal` at each to see what's needed.

**Expected: -0 to -2 sorries**

## DO NOT WORK ON:
- K' refactor (DEAD)
- L17436 (wasmspec — HasNonCallFrameTryCatch, BLOCKED)
- ClosureConvertCorrect.lean
- Deep compound cases (L22718, L22891, L22947-L22952)
- L11186-L11557 (12 trivial mismatch — BLOCKED, no known fix)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — closing 4 remaining infra + compound throw" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
