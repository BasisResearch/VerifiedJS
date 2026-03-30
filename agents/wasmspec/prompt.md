# wasmspec — Apply hnoerr guards to CC + close easy CC sorries

## CRITICAL: CHECK FILE PERMISSIONS FIRST
Before editing CC, verify you can write to it:
```bash
test -w VerifiedJS/Proofs/ClosureConvertCorrect.lean && echo "WRITABLE" || echo "BLOCKED - wait for proof agent to chmod"
```
If BLOCKED: wait 5 min, then check again. Proof agent has been instructed to chmod g+w.

## MEMORY: 7.7GB total, NO swap
- **NEVER run `lake build VerifiedJS`** (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- Check `pgrep -af "lake build"` first — do NOT start if one runs.

## CONTEXT: YOU WERE BLOCKED FOR 3 HOURS
CC file was owned by proof with no group write. Proof agent is now instructed to fix this.
Once writable, you have a LOT of catching up to do.

## PRIORITY 1: Apply hnoerr guards (UNBLOCKS Fix D)

jsspec has staged ALL the diffs in `.lake/_tmp_fix/cc_hnoerr_guards.lean`. Read it.

The pattern for each of ~23 `Flat_step?_*_step` theorems (L1620-2081):
1. Add `(hnoerr : ∀ msg, t ≠ .error msg)` as LAST hypothesis
2. Change proof to:
```lean
    simp only [Flat.step?, hnv, hss]
    cases t with
    | error msg => exact absurd rfl (hnoerr msg)
    | log _ => rfl
    | silent => rfl
```
3. At each CALL SITE, supply `hnoerr`. Usually derivable from context as `fun msg h => by simp [h] at hev` or similar.

**NOTE**: `Flat_step?_seq_step` (L1895) and `Flat_step?_let_step` (L1918) ALREADY have hnoerr. Skip these.

Build after EVERY 3-4 theorem changes. Do NOT batch all 23 and hope it works.

## PRIORITY 2: Close easy CC sorries (after P1 builds clean)

### Tier A — Mechanical (attempt these):
- **L2707**: Read context with `lean_goal`, likely simple case analysis
- **L3036**: CCState threading in if-then — use `lean_multi_attempt` with `[simp, rfl, omega, exact rfl]`
- **L3058**: Two sorries on same line, CCState threading

### Tier B — Need helper lemmas:
- **L2852, L3175**: `hev_noerr : ∀ msg, ev ≠ .error msg` — prove from context that the trace event from stepping a well-formed non-error expression is not an error
- **L2513, L2623**: needs `convertExpr_not_lit` lemma

### DO NOT TOUCH Tier C (hard) this run:
- L1369/1370 (forIn/forOf stubs — unprovable)
- L3562/3563, L4131, L4303, L4625, L4723, L4897, L4987 (complex)

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw — once permissions fixed)
- `.lake/_tmp_fix/cc_hnoerr_guards.lean` (read — jsspec staging)
- DO NOT edit: ANFConvertCorrect.lean, Flat/Semantics.lean
- LOG every 15 min to agents/wasmspec/log.md
