# wasmspec — FIX step_error_isLit tryCatch (L14759) + Case B sorries

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T15:00
- Total: 61 real sorries (ANF 46, CC 15).
- **step_error_isLit (L14289)**: NEARLY PROVED. Only 1 sorry remaining at L14759 (tryCatch case).
- **hasReturnInHead_return_steps**: First-position cases ALL PROVED. Second-position being worked on by proof agent.
- **You wrote most of the current infrastructure. Excellent work.**

## P0: step_error_isLit tryCatch (L14759) — CASCADE BLOCKER

The sorry at L14759 is in the tryCatch case of `HasReturnInHead_step_error_isLit`:

```
14755:    | tryCatch body catchParam catchBody fin =>
14756:      -- BLOCKED: tryCatch non-call-frame catch (Flat/Semantics.lean L1104-1111) emits
14757:      -- (.error msg, {expr := handler}) where handler is not .lit.
14758:      -- Fix: change Flat/Semantics.lean to emit (.silent, ...) for caught errors.
14759:      sorry
```

### THE PROBLEM
When Flat.step? on tryCatch body catches an error (body evaluates to `.error msg`), it steps to `{expr := catchBody}` — which is NOT `.lit v`. So the theorem `∃ v, sf'.expr = .lit v` is FALSE for this case.

### BUT: HasReturnInHead has NO tryCatch constructor!

Wait — check if `HasReturnInHead` has a `tryCatch_body` constructor. If it does NOT, then the match `| tryCatch body catchParam catchBody fin =>` is matching on the EXPRESSION, not the HasReturnInHead constructor. The `hret : HasReturnInHead (.tryCatch body catchParam catchBody fin)` needs to be case-split:

```lean
    | tryCatch body catchParam catchBody fin =>
      cases hret with
      | seq_left h => -- HasReturnInHead in body via seq_left? No — tryCatch is not seq
      ...
```

### APPROACH 1: Check what HasReturnInHead constructors apply to tryCatch
Use `lean_goal` at L14759 to see hret. Then `cases hret` — if HasReturnInHead has no constructor that produces `.tryCatch`, this case is impossible and `cases hret` should close it.

### APPROACH 2: If HasReturnInHead DOES have tryCatch_body
Then the theorem statement needs strengthening — add a precondition excluding tryCatch with non-call-frame catchParam, OR change Flat/Semantics.lean so caught errors also produce `.lit v`.

### VERIFICATION
After fixing, check that `HasReturnInHead_step_error_isLit` has NO remaining sorries:
```
lean_diagnostic_messages ANFConvertCorrect.lean declaration_name=HasReturnInHead_step_error_isLit
```

This is the #1 priority because closing step_error_isLit cascades to close/unblock multiple downstream sorries.

## P1: Case B continuation sorries (L16091, L16147)

These are in hasReturnInHead_return_steps, inside the newObj_func case. They say:
```
-- Case B: return from continuation (normalizeExpr b K produces return (some arg_t))
sorry
```

Read 30 lines around L16091 and L16147 to understand. Case B happens when the return doesn't come from HasReturnInHead on the sub-expression `a`, but from the continuation `K` applied to `a`'s result. This needs a different proof strategy:
- After sub-expression `a` evaluates to value, the continuation produces `.return arg`
- Need to show Flat steps: first evaluate `a` to value, then the wrapper (seq/newObj) steps once, THEN the continuation body produces return

This is structurally different from Case A (return from sub-expr). Assess feasibility before writing code.

## P2: compound HasAwaitInHead (L16515) + compound HasYieldInHead (L16688)

Same pattern as HasReturnInHead compound cases. Check if these follow the same infrastructure.

## DO NOT WORK ON:
- L16148-16159 (second-position — proof agent is on this)
- ClosureConvertCorrect.lean (jsspec)
- L10566-L10937 (trivialChain zone)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — step_error_isLit tryCatch fix" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
