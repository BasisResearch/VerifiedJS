# proof — COMPOUND THROW + ERROR PROPAGATION INFRASTRUCTURE

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T04:05
- ANF: 30 real sorries. CC: 12. Total: **42**.
- ALL 18 HasThrowInHead_step_nonError infrastructure sorries are CLOSED. EXCELLENT.
- The 12 trivial-mismatch sorries (L11186-L11557) are BLOCKED — do NOT work on them.

## P0: CLOSE L14196 (compound throw) — HIGHEST PRIORITY

HasThrowInHead_step_nonError is now sorry-free. Next steps:

1. **Write HasThrowInHead_Steps_steppable** (~50 lines):
```lean
theorem HasThrowInHead_Steps_steppable
    (hth : HasThrowInHead e)
    (hsteps : Flat.Steps ⟨e, env, heap, trace, funcs, cs⟩ evs sf') :
    HasThrowInHead sf'.expr ∨ sf'.expr.isValue
```
Use induction on Steps. Base case: refl → left hth. Step case: use HasThrowInHead_step_nonError.
If step produces error (isValue), go right. Otherwise, IH with preserved HasThrowInHead.

2. **Close L14196**: The `| _ =>` catch-all handles compound cases where HasThrowInHead is in a sub-expression. Pattern:
   - Get HasThrowInHead from normalizeExpr structure
   - Use HasThrowInHead_Steps_steppable to show Flat reaches either a value (contradiction) or still has throw
   - Then use existing throw simulation infrastructure

**Expected: -1 sorry**

## P1: COMPOUND ERROR PROPAGATION — HIGH LEVERAGE

14 ANF sorries share the blocker "compound error propagation in Flat.step?":
- L22850, L23023, L23079, L23083, L23084 (await/yield/return/compound)
- L23174, L23186 (while condition)
- L24792, L24810, L24813 (tryCatch)
- L26360, L26431 (break/continue compound)

These all need a general lemma: when a compound expression has HasXInHead (for X = break/continue/await/yield), the Flat machine can step through the non-head sub-expressions to reach the abrupt completion.

If you finish P0 and have time, the break/continue cases (L26360, L26431) use the EXACT same pattern as throw but with HasBreakInHead/HasContinueInHead. Check if analogous infrastructure exists.

## P2: If-branch (L23911, L23951) — only if P0 done

These are collapsed for OOM. `lean_goal` to check if they're actually blocked or just need expanding.

## DO NOT WORK ON:
- L11186-L11557 (12 trivial mismatch — BLOCKED, no known fix)
- L17568 (wasmspec — HasNonCallFrameTryCatch, BLOCKED)
- ClosureConvertCorrect.lean
- K' refactor (DEAD)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — compound throw P0" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
