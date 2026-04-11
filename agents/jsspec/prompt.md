# jsspec — TRIAGE: lean_multi_attempt ON ALL CC SORRIES, THEN DESIGN FIX

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T09:00
- CC: 15 sorries. Total: 46 (down from 51 — wasmspec closed callStack).
- Previous analysis (March 31) concluded CCStateAgree sorries are ARCHITECTURALLY UNPROVABLE.
- The March 31 analysis identified 3 viable paths. We're now pursuing a TRIAGE approach.

## SORRY CLASSIFICATION (15 total)
- CCStateAgree: 5 (L5491, L5517, L8407, L8484, L8600) — ARCHITECTURALLY BLOCKED
- TryCatch-init edge: 3 (L5265, L5409, L5696) — blocked by L8484
- Multi-step: 3 (L5044, L6347, L6358) — BLOCKED
- Non-consoleLog call: 1 (L6139) — BLOCKED
- Unprovable: 1 (L6998) — CANNOT BE PROVED
- functionDef: 1 (L8250) — BLOCKED
- tryCatch finally: 1 (L8410) — BLOCKED

## P0: lean_multi_attempt SCAN OF ALL 15 SORRIES

Before investing in design changes, systematically scan every sorry with automated tactics. Some may be closer to provable than the March analysis suggested, especially if new helper lemmas have been added since then.

**DO THIS FOR EACH SORRY** (L5044, L5265, L5409, L5491, L5517, L5696, L6139, L6347, L6358, L6998, L8250, L8407, L8410, L8484, L8600):

1. Run `lean_goal` at the sorry line to see the exact proof state
2. Run `lean_multi_attempt` with:
   ```
   ["simp_all", "aesop", "omega", "tauto", "contradiction", "rfl", "exact?", "decide"]
   ```
3. Log the result (what the goal looks like, what tactics were tried)
4. If ANY tactic works → apply it immediately

**PRIORITY ORDER**: Start with L8407 (most likely closable — it's `by rw [hst'_eq]; sorry` which may become trivial after rewrite). Then L5265, L5409, L5696 (these are `Or.inr sorry` — check what the Or.inr branch needs).

## P1: L8407 DEEP DIVE

L8407 is: `exact ⟨st, st, by simp [sc', Flat.convertExpr], ⟨rfl, rfl⟩, by rw [hst'_eq]; sorry⟩`

After `rw [hst'_eq]`, the goal should be CCStateAgree of some specific states. Run `lean_goal` after the rewrite to see if it's just `⟨rfl, rfl⟩` or if it needs more.

If the rewrite makes the goal `CCStateAgree st st` (identity), then `exact ⟨rfl, rfl⟩` closes it.

## P2: IF ALL SORRIES CONFIRMED BLOCKED — START DESIGN FIX

If the scan confirms all 15 are blocked, begin implementing **Path A from March 31 analysis**:

### Path A: CCStateAgreeWeak (monotone invariant)

The comments at L5491 and L5517 both say:
```
-- FIX: Change invariant to CCStateAgreeWeak; then use convertExpr_state_mono
```

This suggests the code AUTHORS intended CCStateAgreeWeak as the fix. Check:

1. Does `CCStateAgreeWeak` already exist? (It's defined at L565 as `≤` instead of `=`)
2. Does `convertExpr_state_mono` exist? Search for it.
3. The March 31 analysis said "≤ breaks chaining cases". But check: do the chaining cases actually NEED `=`, or can they work with `≤` + `convertExpr_state_determined`?

If `convertExpr_state_determined` can be weakened to accept `≤` inputs (using monotonicity), then CCStateAgreeWeak works everywhere.

**Key question**: Does `convertExpr_state_determined` actually NEED `=`? If the output expression only depends on `nextId` (for fresh names), and names are used as opaque identifiers (never compared for equality in the semantics), then even with different names, the semantics could be equivalent.

### Path B: Skip-branch state threading (surgical fix)

For the specific sorry sites:
- L5491 (if-true): `st_a' = (convertExpr then_ ... st).snd`. Need `CCStateAgree st_a' st'` where `st' = (convertExpr else_ ... (convertExpr then_ ... st).snd).snd`. This needs `convertExpr else_` to not change state → only when `else_` has no `functionDef`.
- Could add a `supported_no_functionDef` lemma if the `supported` predicate excludes nested function definitions. CHECK: does `supported = true` imply no `functionDef` sub-expressions?

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — lean_multi_attempt CC triage" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
