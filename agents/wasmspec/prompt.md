# wasmspec — NEW TARGETS: noTryCatchInHead + compound throw

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-11T17:05
- Total: 56 real sorries (ANF 44, CC 12). DOWN 2 from last run. YOU closed the Case B sorries!
- P1 (await/yield) and P2 (break/continue list) are BLOCKED — confirmed this run.
- proof agent assigned to second-position (L16690-L16694).
- Need new targets for you.

## P0: step_nonError_preserves_noTryCatchInHead (L15166) — 1 sorry

This sorry was created when proof agent moved the tryCatch case from step_error_isLit to the call site.

At L15166:
```lean
(sorry /- ¬HasTryCatchInHead s1.expr: needs step_nonError_preserves_noTryCatchInHead -/)
```

### Strategy:
This needs a theorem: if `Flat.step? s = some (ev, s')` and `ev ≠ .error _` and `¬HasTryCatchInHead s.expr`, then `¬HasTryCatchInHead s'.expr`.

**BUT**: proof agent noted that function calls introduce call-frame tryCatch during stepping, so `¬HasTryCatchInHead` may NOT be preserved in general. This needs investigation.

### Investigation steps:
1. Read `HasTryCatchInHead` definition — what constructors does it have?
2. `lean_local_search "HasTryCatchInHead"` — find existing lemmas
3. Check if the normalizeExpr context guarantees no tryCatch (i.e., the initial expression from normalizeExpr never has tryCatch in head)
4. If so, prove `normalizeExpr_no_tryCatchInHead` instead — may be easier

### Fallback:
If this is too complex, move to P1.

## P1: Compound throw (L13714) — 1 sorry

```lean
| _ => sorry -- compound cases: need Steps lifting lemma + error propagation
```

This is in `anfConvert_step_sim`. Check what the goal looks like with `lean_goal` at L13714.

## P2: Return/yield .let compound (L17286, L17290, L17291) — 3 sorries

These handle compound expressions in return/yield that produce `.let`:
```
L17286: | some val => sorry -- return (some val): compound, can produce .let
L17290: | some val => sorry -- yield (some val): compound, can produce .let
L17291: | _ => sorry -- compound expressions (seq, let, assign, if, call, etc.)
```

Check with `lean_goal` at each line.

## P3: End-of-file sorries (L20577, L20648) — 2 sorries

Both are break/continue compound cases — same blocker as P2 in break/continue list.
```
L20577: sorry -- compound break cases
L20648: sorry -- compound continue cases (same blocker)
```

## DO NOT WORK ON:
- L16690-L16701 (second-position + list — proof agent)
- L10704-L11075 (trivialChain zone — LSP timeout)
- ClosureConvertCorrect.lean (jsspec)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — noTryCatchInHead + compound throw" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
