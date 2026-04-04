# proof — CLOSE SORRIES. STOP ADDING INFRASTRUCTURE.

## RULES
- Edit: ANFConvertCorrect.lean ONLY
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build ANF: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
- **DO NOT** edit ClosureConvertCorrect.lean or LowerCorrect.lean

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## ⚠️ CRASH PREVENTION ⚠️
- **Start small**: build only the specific lemma you're editing
- If build OOMs: add `set_option maxHeartbeats 200000` above the theorem
- Do NOT attempt to build the entire file if it's failing

## ‼️ YOU HAVE BEEN STUCK FOR 7+ RUNS ‼️
You keep adding infrastructure (650+ lines) and analyzing but NOT CLOSING SORRIES.
STOP ADDING CODE. START CLOSING SORRIES. Every run must close at least 1 sorry.

## STATE: ANF has 23 sorry lines. 0 closed in 7 runs.

## YOUR ONE TASK THIS RUN: Close the TRIVIAL_CHAIN_CONNECT sorry

Find the sorry with comment `TRIVIAL_CHAIN_CONNECT` (search for it with grep). It's in `normalizeExpr_throw_compound_case`, in the `¬HasThrowInHead e` branch.

### What you have in context:
- `htc : isTrivialChain e = true` (from no_throw_head_implies_trivial_chain)
- `hnorm' : (ANF.normalizeExpr e (fun t => pure (.throw t))).run n = .ok (.throw arg, m)`
- `v, evs, sf', hsteps, hexpr, henv, hheap, htrace, hobs` from trivialChain_throw_steps
- `hewf' : ∀ x, VarFreeIn x e → Flat.Env.lookup env x ≠ none`

### What you need to prove:
The two conjuncts: (1) evalTrivial ok case → Flat.Steps exist, (2) evalTrivial error case → Flat.Steps exist.

### CONCRETE APPROACH:
1. `lean_goal` at the TRIVIAL_CHAIN_CONNECT sorry to see exact proof state
2. Case split on `e` using `cases e` — since `isTrivialChain e = true`, only `lit`, `var`, `this`, `seq` survive
3. For each surviving case, `simp [ANF.normalizeExpr]` at `hnorm'` to determine what `arg` is
4. Then show `evalTrivial env arg` matches the flat value `v`

### For lit case:
- `normalizeExpr (.lit val) (fun t => pure (.throw t))` = `pure (.throw (.lit val))` or similar
- `arg` = the trivial of val
- `evalTrivial env arg = .ok val`
- Already have flat steps from trivialChain_throw_steps producing val

### For var case:
- `normalizeExpr (.var x) (fun t => pure (.throw t))` = `pure (.throw (.var x))`
- `arg = .var x`
- `evalTrivial env (.var x)` = lookup x in env
- Well-formedness gives lookup succeeds

### DO NOT:
- Add new inductive types
- Add infrastructure lemmas > 30 lines
- Work on any other sorry until this one is closed
- Spend more than 5 minutes analyzing before writing proof code

### AFTER closing TRIVIAL_CHAIN_CONNECT, IF time remains:
- Look at the HasThrowInHead sorry just above it (~10 lines earlier)
- Try: `cases e <;> simp [HasThrowInHead, isTrivialChain] at *`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
