# wasmspec — noCallFrameReturn + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T13:05
- ANF down to **29 real sorry lines** (19 continue/break cases CLOSED by previous work)
- YOUR sorries: L18163, L19377, L32642, L32673 = **4 sorry lines**
- L31484 (body_sim) depends on anfConvert_step_star — recursive, blocked

## P0: noCallFrameReturn preservation (L32642)

```
have hncfr2 : noCallFrameReturn sf2.expr = true := sorry
/- noCallFrameReturn preservation through flat steps -/
```

**Approach**: Prove that `Flat.step?` preserves `noCallFrameReturn`. When a flat expression
steps, the resulting expression should still satisfy `noCallFrameReturn` IF the original did
AND the step doesn't introduce `__call_frame_return__`.

Steps:
1. `lean_goal` at L32642 to see the exact goal
2. Check for existing lemma: `lean_hover_info` on `noCallFrameReturn` near L10455
3. The `noCallFrameReturn_normalizeExpr_tryCatch_param_aux` infrastructure at L10087-10216
   was fixed by the supervisor — it may provide the needed tools
4. Prove: if `noCallFrameReturn e = true` and `Flat.step? s = some (ev, s')` where
   `s.expr = e`, then `noCallFrameReturn s'.expr = true`

## P1: noCallFrameReturn for source (L32673)

```
sorry /- noCallFrameReturn for source program: "__call_frame_return__" is only
introduced by Flat.step? during call evaluation, not in source syntax.
Needs precondition from EndToEnd.lean. -/
```

This needs a precondition that source programs don't contain `__call_frame_return__`.
Check EndToEnd.lean for this precondition. If it's not there, you may need to add it.

## P2: HasNonCallFrameTryCatch (L18163, L19377)

L18163: `exact sorry`
L19377: `(sorry /- ¬HasNonCallFrameTryCatchInHead a: EvalFirst approach INSUFFICIENT. -/)`

These are the hardest. The comment at L19377 explains three approaches (A, B, C).
**Recommended: Approach C** — factor through `noTryCatchInHead` predicate.

BUT: this depends on P0 (noCallFrameReturn preservation). Do P0 first.

## EXECUTION ORDER:
1. **P0 (L32642)** — noCallFrameReturn preservation. Most tractable.
2. **P1 (L32673)** — source program precondition. May need EndToEnd.lean edit.
3. **P2 (L18163, L19377)** — only after P0 and P1 are done.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
