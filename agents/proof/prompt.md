# proof — WRITE HELPER LEMMAS FOR break/continue COMPOUND CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE lemma, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T10:00
- ANF: 32 sorries. CC: 15 (jsspec). Total: 47.
- **trivialChain (L10183-L10554) is CONFIRMED BLOCKED** — you confirmed this in 3 consecutive runs. DO NOT ATTEMPT.
- **LSP times out past ~L10000** in the 18K-line ANFConvertCorrect.lean.
- ALL your previous targets are blocked or past LSP range.
- **NEW ASSIGNMENT**: Write helper lemmas EARLY in file (L4000-L7000, within LSP range) that will enable closing L17340/L17411 later.

## ⚠️ DO NOT WORK ON:
- L10183-L10554 (trivialChain — BLOCKED, confirmed 3x)
- L12969-L14054 (wasmspec-owned HasReturnInHead sorries)
- L14144-L14921 (while/if — BLOCKED)
- L15762-L15783 (tryCatch — BLOCKED)
- L17110, L17121 (noCallFrameReturn/body_sim — BLOCKED)

## P0: HELPER LEMMAS FOR break/continue COMPOUND CASES

The sorries at L17340 and L17411 are in `anfConvert_step_star` for break/continue. The pattern: `HasBreakInHead e label` (or HasContinueInHead) through compound constructors (seq_left, binary_lhs, call_func, etc.). Each needs a proof that Flat.step? of the compound expression delegates to stepping the sub-expression.

### STEP 1: Check what exists

Use `lean_local_search` for:
- "HasBreakInHead_not_value" or "HasBreak.*value"
- "step?_seq_left" or "step?_binary_lhs" (step delegation lemmas)
- "compound_step_delegates"
- "HasAbruptCompletion_not_value"

### STEP 2: Write `HasBreakInHead_not_value`

Place near L5400 (after existing break lemmas). If `HasBreakInHead e label`, then `e` is not a flat value.

```lean
private theorem HasBreakInHead_not_value (h : HasBreakInHead e label) :
    Flat.exprValue? e = none := by
  cases h <;> rfl
```

Verify with `lean_diagnostic_messages`.

### STEP 3: Write step? delegation lemmas

These show that compound expressions delegate step? to the head sub-expression. Place near L4500 or wherever step? lemmas live.

For each compound constructor where step? delegates to a non-value head:

```lean
/-- seq delegates step to non-value head -/
private theorem step?_seq_delegates_head
    (hnv : Flat.exprValue? a = none)
    (hstep_a : Flat.step? ⟨a, env, heap, trace, funcs, cs⟩ = some (ev, sa')) :
    Flat.step? ⟨.seq a b, env, heap, trace, funcs, cs⟩ =
      some (ev, ⟨.seq sa'.expr b, sa'.env, sa'.heap, sa'.trace, sa'.funcs, sa'.callStack⟩) := by
  simp [Flat.step?, hnv, hstep_a]
```

Write similar for: binary_lhs (when lhs not value), call_func (when func not value), getProp_obj, setProp_obj, unary_arg, etc.

**IMPORTANT**: First check what step? actually does for each compound. Use `lean_hover_info` on `Flat.step?` to understand the definition, or `lean_goal` on a test position.

### STEP 4: Write the compound step-through lemma

Once delegation lemmas exist, write:

```lean
/-- For compound expressions with HasBreakInHead in head position,
    Flat.step? delegates to stepping the head sub-expression. -/
private theorem HasBreakInHead_compound_step_exists
    (hbreak : HasBreakInHead e label)
    (hna : NoNestedAbrupt e)
    (he_compound : ∀ l, e ≠ .break l)  -- e is compound, not direct break
    (hwf : ExprWellFormed e env) :
    ∃ ev (sf' : Flat.State), Flat.step? ⟨e, env, heap, trace, funcs, cs⟩ = some (ev, sf') ∧
      HasBreakInHead sf'.expr label := by
  sorry -- fill in using the delegation lemmas + cases on hbreak
```

Even if this is sorry'd, it structures the proof. The sorry can be filled later.

### STEP 5: Verify everything with lean_diagnostic_messages

Make sure no new errors introduced. All new lemmas should either compile fully or have intentional sorry markers.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — break/continue helper lemmas" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
