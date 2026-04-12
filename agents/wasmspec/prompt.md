# wasmspec — noCallFrameReturn PRESERVATION + HasNonCallFrameTryCatch

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, pgrep, sleep loops
- You CAN edit ANFConvertCorrect.lean AND Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY — no builds.

## STATUS — 2026-04-12T18:05
- L18163: DONE ✓
- **YOUR sorries: L19389, L32645, L32667, L32741 = 3-4 sorry lines**
- Build is CLEAN (proof agent fixed all compilation errors)

## P0: noCallFrameReturn preservation (L32645 area) — CONTINUE

You're working on `anfConvert_step_star_ncfr`. The theorem says ncfr is preserved through ANF-simulation flat step batches.

**Strategy B (check first):** Does `ANF_SimRel` imply `noCallFrameReturn sf'.expr`?
- If so, prove `ANF_SimRel_implies_ncfr` as a lemma → close L32645 immediately
- `lean_goal` at L32645 to check what's available

**Strategy A (fallback):** Case split on ANF step constructor, mirror `anfConvert_step_star` structure (~300 lines).

**Key reminder:** General flat-step ncfr preservation is FALSE (call introduces tryCatch "__call_frame_return__" transiently). Must prove for simulation-specific step batches only.

## P2: HasNonCallFrameTryCatch (L19389) — AFTER P0

Check what hypotheses are available. The question: does `normalizeExpr` of `.return` produce expressions without user-level tryCatch in head position?

If ¬HasNonCallFrameTryCatchInHead can't be derived from existing hypotheses, may need to thread an additional precondition (invasive change — check with supervisor before proceeding).

## EXECUTION ORDER:
1. **P0 (L32645)** — try Strategy B first, then Strategy A
2. **P2 (L19389)** — HasNonCallFrameTryCatchInHead

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
