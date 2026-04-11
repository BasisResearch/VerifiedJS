# jsspec — CONTINUE TRIAGE + BEGIN CCStateAgreeWeak IF BLOCKED

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T10:00
- CC: 15 sorries. Total: 47.
- **Your last run confirmed ALL CCStateAgree targets architecturally blocked.**
- You started lean_multi_attempt triage at 10:00. CONTINUE if not done.
- Root cause confirmed: convertExpr converts ALL branches, simulation tracks only TAKEN branch, creating irreconcilable state gap.

## SORRY CLASSIFICATION (15 total)
- CCStateAgree: 5 (L5491, L5517, L8407, L8484, L8600) — ARCHITECTURALLY BLOCKED
- TryCatch-init edge: 3 (L5265, L5409, L5696) — blocked by L8484
- Multi-step: 3 (L5044, L6347, L6358) — BLOCKED
- Non-consoleLog call: 1 (L6139) — BLOCKED
- Unprovable: 1 (L6998) — CANNOT BE PROVED
- functionDef: 1 (L8250) — BLOCKED
- tryCatch finally: 1 (L8410) — BLOCKED

## P0: FINISH lean_multi_attempt TRIAGE (if not done)

If you already started the triage scan at 10:00, continue it. Test each sorry with:
```
["simp_all", "aesop", "omega", "tauto", "contradiction", "rfl", "exact?", "decide"]
```

Priority: L8407, L5265, L5409, L5696, then remaining.

## P1: IF ALL BLOCKED → supported_no_functionDef CHECK

Before the heavy CCStateAgreeWeak refactor, check a simpler hypothesis:

**Does `supported = true` imply no `.functionDef` sub-expressions?**

If yes, then `convertExpr` on any supported sub-expression would NOT allocate new function slots, meaning `convertExpr_state_determined` would give state equality even across unconverted branches.

Steps:
1. Find the `supported` definition: `lean_local_search "supported"` or grep for `def supported`
2. Check if it excludes `.functionDef`
3. If yes: write `supported_no_functionDef : e.supported = true → ∀ sub ∈ subExprs e, ¬sub.isFunctionDef`
4. Then check if `convertExpr` with no functionDef is state-preserving: `convertExpr e K st = (result, st)` when no functionDef

This would close L5491, L5517, L8407, L8484, L8600 WITHOUT the heavy CCStateAgreeWeak refactor.

## P2: IF supported_no_functionDef FAILS → CCStateAgreeWeak

Begin the heavy refactor:

1. CCStateAgreeWeak is defined at L565 as `≤` (monotone) instead of `=`
2. Change the simulation invariant CC_SimRel to use CCStateAgreeWeak
3. For each existing proved case that uses `convertExpr_state_determined`:
   - Check if it still works with `≤` input (using convertExpr_state_mono)
   - Fix any breakage

**WARNING**: Your last analysis said "CCStateAgreeWeak breaks all proved compound cases." Before committing to this path, verify by trying ONE compound case (e.g., .seq) with CCStateAgreeWeak to see if it actually breaks or if the breakage is fixable.

## P3: L6998 (UNPROVABLE)

This is marked unprovable (semantic mismatch). Check if it can be:
1. Guarded by `supported = true` (excluding the problematic case)
2. Rewritten as `sorry /- AXIOM: getIndex string both-values -/` to mark it as a known axiom

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CC triage + supported_no_functionDef" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
