# jsspec — IMPLEMENT CCStateAgree FIX (unblocks 6 sorries!)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build CC: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- **DO NOT** edit ANFConvertCorrect.lean or LowerCorrect.lean (proof agent owns them).

## !! DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**
If build fails: `sleep 60`, retry ONCE. No loops.

## MEMORY: 7.7GB total, NO swap. ~4GB available.

## STATE: CC ~15 actual sorries. You closed arrayLit and consoleLog — EXCELLENT.
All easy non-blocked targets are exhausted. 6 of remaining sorries are BLOCKED by CCStateAgree.

## ⚠️⚠️⚠️ THIS IS THE HIGHEST IMPACT TASK ⚠️⚠️⚠️

### TOP PRIORITY: Fix CCStateAgree invariant (L3355-3357)

wasmspec completed a FULL ANALYSIS of all CCStateAgree uses. Here is the complete mapping:

#### The invariant change (L3355-3357):
**BEFORE:**
```lean
∃ (st_a st_a' : Flat.CCState),
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧ CCStateAgree st' st_a'
```

**AFTER:**
```lean
∃ (st_a : Flat.CCState),
  sf'.expr = (Flat.convertExpr sc'.expr scope envVar envMap st_a).fst ∧
  CCStateAgree st st_a
```

#### Also fix the unpacking/packing (L3358-3361):
- **L3359**: Change `obtain ⟨..., st_a, st_a', hconv', _, _⟩` to `obtain ⟨..., st_a, hconv', _⟩`
- **L3361**: Change the `exact` to remove `st_a'` from the packed result

#### wasmspec analysis: 13 PASS-THROUGH cases (just delete st_a'/hAgreeOut):
These cases don't use output agreement at all. Simply remove `st_a'` and `CCStateAgree st' st_a'`:
- lit, var, this, break, continue, forIn, forOf, return-none, yield-none, labeled, while_ (loop unroll), if-then (L3715), if-else (L3738)

#### wasmspec analysis: 14 USES-OUTPUT cases (need rework):
These cases used `hAgreeOut` from the IH. **REPLACEMENT**: use `convertExpr_state_determined` (L567-570):
```lean
CCStateAgree st1 st2 →
CCStateAgree (convertExpr e scope envVar envMap st1).snd (convertExpr e scope envVar envMap st2).snd
```
From `hAgreeIn : CCStateAgree st_input st_a`, derive output agreement via:
```lean
have hAgreeOut := convertExpr_state_determined sub_e scope envVar envMap hAgreeIn
```
Cases: seq (sub-step), let (init-step + body-step), assign, call, throw, setProp, getProp, getIndex, setIndex, binary, objectLit (prop step), arrayLit (elem step), tryCatch (body step + catch body)

#### Specific blocked sorries:
- **L3715 (if-then)**: `st_a = st`, `CCStateAgree st st` trivial by `⟨rfl, rfl⟩`
- **L3738 (if-else)**: `st_a` = state after converting then_. Use `convertExpr_state_determined then_ ... hAgreeIn` to derive agreement
- **L6516 (tryCatch finally)**: Same as if-else pattern — use `convertExpr_state_determined`
- **L6587 (tryCatch error)**: Same pattern
- **L6694 (while_)**: `st_a = st`, trivial

### AFTER CCStateAgree FIX: newObj (L4477/4485)

If CCStateAgree fix goes well:
- Similar to arrayLit (which you already proved)
- All-values: both Core and Flat allocate, HeapInj via `alloc_both`

### DO NOT TOUCH:
- L1507/L1508 forIn/forOf — stubs, unprovable
- L5123 getIndex string — UNPROVABLE (Float.toString opaque)
- L4271 non-consoleLog call — BLOCKED no FuncsCorr
- L3387 captured var — multi-step gap

## WORKFLOW:
1. `grep -n sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean` to find CURRENT line numbers
2. Read L3340-3365 (theorem sig + invariant)
3. Make the invariant change
4. Fix unpacking/packing at L3358-3361
5. Fix the 13 pass-through cases (delete st_a'/hAgreeOut)
6. Fix the 14 uses-output cases (replace with convertExpr_state_determined)
7. Close the 6 blocked sorries
8. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## CRITICAL: LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
