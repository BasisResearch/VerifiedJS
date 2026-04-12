# wasmspec — noCallFrameReturn PRESERVATION + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T17:05
- L18163: DONE ✓ (you closed it at 16:35, great work!)
- **YOUR sorries: L19377, L32634 = 2 sorry lines**
- L19377: HasNonCallFrameTryCatchInHead — needs approach A/B/C from comment
- L32634: noCallFrameReturn preservation in anfConvert_step_star_ncfr

## P0: noCallFrameReturn preservation (L32634) — START HERE

```lean
sorry -- in anfConvert_step_star_ncfr, needs case analysis mirroring anfConvert_step_star
```

**Approach:** Prove that the flat steps produced by the ANF simulation preserve noCallFrameReturn.

General flat-step ncfr preservation is FALSE (call introduces tryCatch "__call_frame_return__" transiently). But `anfConvert_step_star_ncfr` applies only to ANF-simulation step BATCHES that resolve the call frame.

**Strategy A (recommended):** Case split on `hstep : ANF.Step sa ev sa'`, mirror anfConvert_step_star structure. For each case, the batch of flat steps starts and ends with ncfr expressions:
1. `lean_goal` at L32634 to get exact context
2. `cases hstep` to split on ANF step constructor
3. For each case, show the resulting sf'.expr from the Flat.Steps batch is ncfr
4. The key insight: each case in anfConvert_step_star produces a SPECIFIC flat expression (e.g., .seq, .let, .if, etc.) and you can directly check ncfr on it

**Strategy B (simpler but needs lemma):** Factor through hrel' (the output SimRel):
- `hrel' : ANF_SimRel s t sa' sf'` gives structural info about sf'.expr
- If ANF_SimRel implies ncfr (which it should since ANF expressions don't have call-frame returns), prove that as a lemma

Try Strategy B first — check if `ANF_SimRel` implies `noCallFrameReturn sf'.expr`:
```lean
lean_hover_info file="VerifiedJS/Proofs/ANFConvertCorrect.lean" line=<ANF_SimRel_def> column=0
```

## P2: HasNonCallFrameTryCatch (L19377) — AFTER P0

This sorry passes `¬HasNonCallFrameTryCatchInHead a` to `HasReturnInHead_Steps_steppable_core`.

**Key connection:** Now that L18163 is PROVED, the infrastructure around it is solid. The question is whether `noCallFrameReturn` implies `¬HasNonCallFrameTryCatchInHead`.

Check definitions:
- `noCallFrameReturn e = true` means no tryCatch with catchVar = "__call_frame_return__"
- `HasNonCallFrameTryCatchInHead e` means there IS a tryCatch whose catchVar ≠ "__call_frame_return__" in head position

These are NOT contradictory! A program can have NO call-frame-return tryCatch AND ALSO no non-call-frame tryCatch (no tryCatch at all). Or it could have non-call-frame tryCatch.

**The real question:** Does the simulation context guarantee ¬HasNonCallFrameTryCatchInHead?
- Check what hypotheses are available at L19377 (`lean_goal`)
- If `normalizeExpr` of `.return` produces expressions without user-level tryCatch in head position, prove it
- May need to thread `noCallFrameReturn` + additional info from normalizeExpr

## EXECUTION ORDER:
1. **P0 (L32634)** — noCallFrameReturn preservation, try Strategy B first
2. **P2 (L19377)** — HasNonCallFrameTryCatchInHead

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
