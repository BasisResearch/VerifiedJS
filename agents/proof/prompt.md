# proof — CLOSE TRIVIALCHAIN SORRIES (12 remaining at L10183-L10554)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-11T09:00
- ANF: 31 sorries. CC: 15 (jsspec). Total: 46.
- wasmspec just closed 6 callStack sorries (-5 net). GOOD PROGRESS.
- Your 12 trivialChain sorries are the LARGEST remaining block.
- LSP may time out past ~L8500 in this 18K-line file.

## ⚠️ DO NOT WORK ON (owned by wasmspec or BLOCKED):
- L12969, L13264, L13415, L13771, L13944, L14000-L14005 (wasmspec)
- L14095-L14872 (while/if — BLOCKED)
- L15713-L15734 (tryCatch — BLOCKED)
- L17061, L17072, L17291, L17362 (BLOCKED)

## P0: TRIVIALCHAIN SORRIES — SYSTEMATIC APPROACH

All 12 sorries are in `normalizeExpr_labeled_branch_step` (L9688+). They follow one pattern:

**The pattern**: `HasLabeledInHead` is in a secondary operand (e.g., rhs of binary). The primary operand does NOT have labeled. The proof needs:
1. Step the primary operand to a value (it's a trivialChain)
2. After stepping, the binary/setProp/etc becomes `op (.lit v) rhs`
3. Show normalizeExpr of this stepped expression still produces `labeled label body`
4. Apply IH on the secondary operand (which has HasLabeledInHead)

**The blocker (per comments)**: "ANF trivial ≠ flat value" — after the primary operand steps to `.lit v`, `normalizeExpr (.lit v) k` should immediately apply `k` to produce a trivial, but the proof can't connect this.

### STEP-BY-STEP APPROACH

**Step 1**: Use `lean_hover_info` on `normalizeExpr` to understand how it handles `.lit v` — does it immediately apply the continuation?

**Step 2**: Use `lean_goal` at L10183 to see the EXACT proof state. We need:
- What is `lhs` / what does `hnorm` say about `normalizeExpr`?
- Is there a hypothesis showing `lhs` is a trivialChain or NOT HasLabeledInHead?

**Step 3**: Check if `isTrivialChain lhs = true` can be derived from `¬HasLabeledInHead lhs`. This might require a case analysis or a helper lemma.

**Step 4**: If `isTrivialChain lhs`, then `trivialChain_eval_value` (L9526) gives `∃ v evs, Flat.Steps ⟨lhs, ...⟩ evs ⟨.lit v, ...⟩`. Use these steps.

**Step 5**: After stepping, need `normalizeExpr (.binary op (.lit v) rhs) K` to match `normalizeExpr (.binary op lhs rhs) K`. Check if there's a `normalizeExpr_value_trivial` lemma, or if `normalizeExpr (.lit v) k = k (.lit v)` follows from the definition.

**Step 6**: Use `lean_multi_attempt` at L10183 with:
```
["trivialChain_eval_value", "sorry", "simp [ANF.normalizeExpr]", "simp_all [ANF.normalizeExpr]"]
```

### ALTERNATIVE: If trivialChain blocked, try the OTHER approach

Look for helper lemmas:
- `normalizeExpr_lit` or `normalizeExpr_value`
- `HasLabeledInHead_not_trivialChain` or `isTrivialChain_not_hasLabeledInHead`
- `normalizeExpr_continuation_compose`

Use `lean_local_search` with keywords: "trivialChain", "normalizeExpr_lit", "normalizeExpr_value", "HasLabeledInHead_not"

### LAST RESORT: If all 12 are truly blocked

Use `lean_multi_attempt` on EVERY non-owned sorry in the file to find any that automated tactics can close:
```
["simp_all", "aesop", "omega", "tauto", "contradiction"]
```

Even closing 1 sorry is progress worth logging.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — trivialChain systematic approach" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
