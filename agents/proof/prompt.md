# proof — INFRASTRUCTURE: trivialChain sorries + lean_multi_attempt exploration

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE sorry, verify, log, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS
- ANF: 36 sorries. CC: 15 (jsspec). Total: 51.
- Previous 3 runs: declared ALL ANF sorries blocked. 0 closed in 6 hours.
- Key insight from previous runs: LSP times out past ~L8500 in ANFConvertCorrect.lean (18K lines).

## ⚠️ DO NOT WORK ON:
- L13351-L13407 (callStack — wasmspec owns)
- L13763/L13936/L13992-L13997 (HasAwait/HasYield — wasmspec owns)
- L12969 (compound cases — wasmspec)
- L14033-L14864 (while/if — BLOCKED)
- L15705-L15726 (tryCatch — BLOCKED)
- L17053 (noCallFrameReturn — BLOCKED, needs predicate)
- L17064 (body_sim — BLOCKED, needs anfConvert_step_star)
- L17283/L17354 (compound break/continue — BLOCKED by error propagation)

## P0: USE lean_multi_attempt ON TRIVIALCHAIN SORRIES (L10183-L10554)

These 12 sorries share a common structure. `trivialChain_eval_value` already exists at L9526. The question is whether it can be applied.

**DO THIS**:
1. Run `lean_goal` at L10183 to see the exact proof state
2. Run `lean_multi_attempt` at L10183 with these tactics:
   ```
   ["simp_all", "aesop", "omega", "exact trivialChain_eval_value _ _ _ _ _ _ _ ‹_› ‹_›", "apply trivialChain_eval_value", "tauto", "contradiction"]
   ```
3. If any tactic works, apply it. Then try the same on L10231, L10279, etc.
4. If `lean_goal` reveals a specific structure, adapt tactics accordingly.

**KEY CONTEXT**: These sorries are inside `normalizeExpr_step_sim`. They involve proving that a trivialChain expression evaluates to a value via Flat.Steps. The theorem `trivialChain_eval_value` (L9526) should provide exactly this.

Read the context around L10183 (±30 lines) to understand the pattern, then systematically try each sorry.

## P1: IF P0 BLOCKED — TRY lean_multi_attempt ON ALL REMAINING SORRIES

If trivialChain is truly blocked, use `lean_multi_attempt` to scan remaining ANF sorries for any that might be closable by automated tactics. Try each sorry position with:
```
["simp_all", "aesop", "omega", "tauto", "contradiction", "exact?", "apply?"]
```

Even closing 1 sorry is progress. Focus on sorries in the first 8000 lines where LSP can verify.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — trivialChain lean_multi_attempt" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
