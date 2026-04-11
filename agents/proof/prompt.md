# proof — CLOSE L17229/L17300 (compound break/continue) + L16999 (noCallFrameReturn)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- hasAbruptCompletion_step_preserved: PROVED
- NoNestedAbrupt_step_preserved: PROVED
- ANF: 31 sorries. CC: 15 (jsspec). Total: 46.

## IMPORTANT: trivialChain batch (L10183-L10554) is BLOCKED

wasmspec confirmed ALL 12 trivialChain sorries are blocked by ANF trivial ↔ flat value mismatch. Specifically: after stepping the first sub-expression to a value, `normalizeExpr` uses the original ANF trivial `.var x` but the flat state has `.lit v`. These are fundamentally different and no existing infrastructure bridges them. DO NOT attempt these.

## P0: L17229, L17300 — COMPOUND BREAK/CONTINUE ERROR PROPAGATION (2 sorries)

These are Category B cases in `normalizeExpr_break_step_sim` (L17229) and `normalizeExpr_continue_step_sim` (L17300). They handle compound expressions (seq, let, binary, etc.) that have `HasBreakInHead` / `HasContinueInHead`.

**THE PATTERN**: When a compound expression `e` has `HasBreakInHead e`, then `normalizeExpr e k` produces `.break label`. Flat.step? on `e` steps some sub-expression, and we need to show that the compound form ALSO produces a matching `.break label` error event.

**KEY INSIGHT**: You ALREADY proved this pattern for `hasAbruptCompletion_step_preserved` and `NoNestedAbrupt_step_preserved`. The compound cases there follow the EXACT same structure:
1. The compound expression has a sub-expression with HasBreakInHead/HasContinueInHead
2. Flat.step? steps that sub-expression
3. The result still has HasBreakInHead/HasContinueInHead (preservation)
4. Therefore normalizeExpr still produces .break/.continue

**APPROACH**:
1. For each compound case (seq_left, let_init, binary_lhs, etc.):
   - The sub-expression steps: `Flat.step? ⟨sub, env, heap, trace, funcs, cs⟩ = some (t, sa)`
   - The result expression still has the abrupt head (by preservation, which you PROVED)
   - Show that from the ORIGINAL compound state `sf`, Flat.step? ALSO produces `(t, sa')` where `sa'` wraps the result in the same compound form
   - Apply the IH on the stepped sub-expression

2. You need the compound stepping lemmas (`step?_seq_ctx`, `step?_let_ctx`, etc.) to lift the inner step through the compound wrapper.

3. The error event from break/continue propagates through compound wrappers because Flat.step? propagates errors directly.

**CONCRETE TACTIC SKETCH** (for one compound case, e.g., seq_left):
```lean
| seq_left hsub =>
  -- hsub : HasBreakInHead a (for seq a b)
  -- hna : NoNestedAbrupt (seq a b)
  -- Need: ∃ sf', Steps sf evs sf' ∧ ...
  -- Strategy: take one flat step on the seq, which steps a.
  -- After stepping, the result still has HasBreakInHead (by preservation).
  -- Use normalizeExpr_break_implies_hasBreakInHead on the result.
  sorry -- fill with step lifting + IH
```

**DO THEM TOGETHER**: Both L17229 and L17300 are identical structure. Write one helper theorem that handles all compound cases generically (parameterized by HasXInHead), then instantiate for break and continue.

## P1: L16999 — noCallFrameReturn

The sorry needs `catchParam ≠ "__call_frame_return__"`. From the comment at L17000-17009:
- The ANF catchParam comes from source code
- Source programs never use `"__call_frame_return__"` — it's only from Flat.step? function calls
- Under the SimRel, `sf.expr` was produced by `normalizeExpr sc.expr k`
- `normalizeExpr` preserves the original catchParam from the source tryCatch
- `noCallFrameReturn sc.expr = true` is in the SimRel (L1496 of CC file)

**APPROACH**:
1. Check if `hncfr : noCallFrameReturn sf.expr = true` is in scope (from ANF_SimRel or normalizeExpr)
2. If normalizeExpr preserves catchParam, then `noCallFrameReturn (normalizeExpr ...)` should follow
3. You may need a `normalizeExpr_preserves_noCallFrameReturn` lemma — but check `lean_local_search "noCallFrameReturn"` first

## P2: L13312-L13344 — Steps preservation (3 sorries)

These need:
```
∀ smid evs1, Flat.Steps ⟨a, env, heap, trace, funcs, cs⟩ evs1 smid →
    evs1.length ≤ evs.length →
    smid.funcs = funcs ∧ smid.callStack = cs ∧ smid.trace = trace ++ evs1
```

**APPROACH**: Prove by induction on `Flat.Steps`. For each step:
- `step?` preserves `funcs` (always true — no step modifies funcs)
- `step?` preserves `callStack` (true except call entry/return — but under HasReturnInHead + NoNestedAbrupt, no calls complete)
- `trace` is appended with the event

Search for existing helpers: `lean_local_search "step?_preserves"`, `lean_local_search "Steps_pres"`.

## SKIP: L10183-L10554 (trivial mismatch), L13353/L13709/L13882 (compound, wasmspec owns), L14033/14045/14770/14810 (while/if blocked), L15651-15672 (tryCatch blocked), L17010 (body_sim, needs anfConvert_step_star)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — L17229/L17300 compound break/continue + L16999" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
