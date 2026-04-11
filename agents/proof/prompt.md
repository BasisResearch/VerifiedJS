# proof — CLOSE HasReturnInHead_step_error_isLit (L14152) + trivialChain list sorries

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE lemma, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T11:06
- ANF: 33 sorries. CC: 17 (jsspec). Total: 50.
- **HasReturnInHead_step_nonError WRITTEN** (wasmspec, ~600 lines) but depends on HasReturnInHead_step_error_isLit (L14152) which is sorry.
- **HasReturnInHead_Steps_steppable (L14161) is PROVED** — depends on step_error_isLit.
- Your break/continue step? helpers at L4575/L5713 are good (+2 sorries for non-head cases).
- **trivialChain (L10429-L10800)** — 12 sorries. Still BLOCKED by LSP timeout past L10000.

## ⚠️ DO NOT WORK ON:
- L10429-L10800 (trivialChain — LSP TIMEOUT zone)
- L12969-L14148 (wasmspec-owned)
- L15033-L15045 (while — BLOCKED)
- L15770-L15810 (if — BLOCKED)
- L16651-L16672 (tryCatch — BLOCKED)
- L17999, L18010 (noCallFrameReturn/body_sim — BLOCKED)

## P0: HasReturnInHead_step_error_isLit (L14152) — HIGHEST VALUE

This sorry blocks the entire HasReturnInHead cascade. wasmspec proved step_nonError and Steps_steppable, but they depend on step_error_isLit. Closing this one sorry cascades: step_nonError becomes sorry-free → Steps_steppable fully verified → callStack condition sorries at L14298-L14321 auto-verify → potential -4 to -8 sorries.

### What it says
```lean
private theorem HasReturnInHead_step_error_isLit
    {sf sf' : Flat.State} {msg : String}
    (hret : HasReturnInHead sf.expr)
    (hstep : Flat.step? sf = some (.error msg, sf')) :
    ∃ v, sf'.expr = .lit v
```

If an expression has HasReturnInHead, and it takes an error step, then the result is a literal.

### Why this should be provable

Error steps in Flat.step? come from:
1. `.return none` → error "return:undefined" → `.lit .undefined` ✓
2. `.return (some v)` where v is value → error "return:value" → `.lit v` ✓
3. `.throw v` where v is value → error "throw:..." → `.lit v` ✓
4. `.break label` → error "break:..." → `.lit .undefined` ✓
5. `.continue label` → error "continue:..." → `.lit .undefined` ✓
6. `.yield (some v)` where v is value → error "yield:..." → `.lit v` ✓
7. `.await v` where v is value → error "await:..." → `.lit v` ✓

ALL error-producing steps result in `.lit v`. So the theorem is true regardless of HasReturnInHead.

### Proof strategy

You might not even need the `hret` hypothesis. Try:

```lean
  -- Error steps in Flat.step? always produce .lit values
  cases sf with | mk e env heap trace funcs cs =>
  simp [Flat.State.expr] at hret
  -- Case split on e to find which expressions produce errors
  cases e <;> simp [Flat.step?] at hstep
  -- For each error-producing case, extract the .lit result
  all_goals (try (obtain ⟨v, hv⟩ := ...; exact ⟨v, hv⟩))
```

Or use `lean_multi_attempt` at L14157:
```
["cases sf with | mk e env heap trace funcs cs => cases e <;> simp [Flat.step?] at hstep <;> sorry",
 "simp [Flat.step?] at hstep; sorry"]
```

### Step-by-step
1. `lean_goal` at L14157 to see the goal state
2. `lean_multi_attempt` with the tactics above
3. For remaining sub-goals: each error-producing step? branch produces `.lit v` in sf'. Extract it from hstep.

## P1: Complete break/continue non-head cases

Your HasBreakInHead_step?_produces_error (L4575) and HasContinueInHead_step?_produces_error (L5713) have sorries for non-head cases. These mirror Pattern B from HasReturnInHead_step_nonError (L13623). Study that theorem's approach for "right" compound cases.

## P2: L18229 and L18300

These are at the end of the file. Check what theorems they're in and whether they're closable with existing infrastructure.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — HasReturnInHead_step_error_isLit" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
