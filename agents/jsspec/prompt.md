# jsspec — Close remaining CC sorries (CCState threading + captured var)

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`

## !! DO NOT USE WHILE/UNTIL LOOPS !!
Previous agents got PERMANENTLY STUCK. **NEVER use `while`, `until`, or `sleep` in a loop.**
`lake serve` processes are PERMANENT. Just run your build command directly.

## MEMORY: 7.7GB total, NO swap.

## STATE (04:05): CC has 17 sorries (you proved 2 two runs ago! 19→17 ✓)
**Your last 3 runs (03:00, 02:00, 01:43) logged NOTHING — check if you're making progress.**

### Remaining sorry breakdown:
- **2 unprovable stubs** (L1520-1521 forIn/forOf): DO NOT TOUCH
- **1 captured variable** (L2933): YOUR TARGET — BLOCKED (multi-step mismatch)
- **3 CCStateAgree** (L3252, L3274, L5313): YOUR TARGET — BLOCKED (invariant too strong)
- **7 value/heap sub-cases**: wasmspec owns (L3768, L3769, L4337, L4509, L4831, L5014, L5192, L5282)

### YOUR FINDINGS FROM LAST RUN:
You correctly identified that the CCStateAgree sorries are fundamentally blocked:
- L3252 (if-true): `st'` includes else_ conversion but `st_a'` is then_-only
- L3274 (if-false): input `st` doesn't agree with `(convertExpr then_ ... st).snd`
- L5313 (while_): duplicated sub-expression conversion advances state differently
- L2933 (captured var): Flat needs 2 steps, Core needs 1 — 1-to-1 sim can't match

## NEW STRATEGY: WEAKEN CCStateAgree TO MONOTONICITY

The root cause is that `CCStateAgree` requires EQUALITY of `nextId` and `funcs.size`,
but branching/resolution steps naturally produce states where one is "ahead" of the other.

### APPROACH: Change CCStateAgree from equality to monotone bounds

```lean
-- CURRENT (broken for branches):
private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId = st2.nextId ∧ st1.funcs.size = st2.funcs.size

-- PROPOSED (works for branches):
private abbrev CCStateAgree (st1 st2 : Flat.CCState) : Prop :=
  st1.nextId ≤ st2.nextId ∧ st1.funcs.size ≤ st2.funcs.size
```

### BUT FIRST: Check what breaks!

1. `grep -n "CCStateAgree" VerifiedJS/Proofs/ClosureConvertCorrect.lean | head -40`
2. Key user: `convertExpr_state_determined` (L566) uses `hid : st1.nextId = st2.nextId`
   - If we weaken to `≤`, this theorem BREAKS — it needs equality to show expressions match
   - **BUT**: do we actually USE the expression-equality from state_determined in the main proof?
   - Check each call site of `convertExpr_state_determined` to see if we need `=` or just `≤`

3. Alternative: Keep CCStateAgree as equality for the INPUT `st st_a` (needed for
   `convertExpr_state_determined`), but weaken the OUTPUT to `st_a'.nextId ≤ st'.nextId`:
```lean
∃ st_a st_a',
  (sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a ∧
  CCStateAgree st st_a ∧    -- INPUT: equality (needed for state_determined)
  st_a'.nextId ≤ st'.nextId ∧ st_a'.funcs.size ≤ st'.funcs.size  -- OUTPUT: monotone
```

4. Then for if-true: `st_a = st` (input agrees), `st_a' = (convertExpr then_ st).snd`
   (output is ≤ st' because converting else_ only increases counters). ✓

5. For if-false: `st_a = st` (input agrees by rfl), `st_a' = (convertExpr else_ ... (convertExpr then_ ... st).snd).snd = st'` (output equals st'). ✓
   Wait — for if-false, sf'.expr should be `(convertExpr else_ ... st_then).fst`, but with
   `st_a = st`, `convertExpr else_ ... st_a_then` where `st_a_then = (convertExpr then_ st).snd`.
   Actually the conversion IS from st → convert cond → convert then_ → convert else_. Since cond=.lit cv,
   converting cond doesn't change state. So `st_a_then = (convertExpr then_ st).snd` and
   `st_a' = (convertExpr else_ ... st_a_then).snd = st'`. So output agrees exactly. ✓

### IMPLEMENTATION PLAN:
1. **First**: Try the asymmetric approach (input=equality, output=monotone)
2. Change the existential in the main theorem (L2901-2903) from `CCStateAgree st' st_a'` to
   `st_a'.nextId ≤ st'.nextId ∧ st_a'.funcs.size ≤ st'.funcs.size`
3. Fix all callers — most just need `≤` weakened from `=`
4. Check that `convertExpr_state_determined` still works (it uses input agreement, not output)
5. Re-prove the if-true/false/while_ cases with the weakened output invariant

**IMPORTANT**: This changes the theorem signature. It WILL break other cases temporarily.
Make the change, then fix ALL build errors before logging. If too many things break,
REVERT and try a different approach.

## ALTERNATIVE: If monotone approach is too disruptive

For the if-true case (L3252), try this specific fix without changing CCStateAgree:
- Pick `st_a = st` (input agrees)
- Pick `st_a' = (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st).snd).snd` = `st'`
- Then `CCStateAgree st' st_a'` is `CCStateAgree st' st'` = `⟨rfl, rfl⟩` ✓
- BUT need `(sf'.expr, st_a') = Flat.convertExpr sc'.expr scope envVar envMap st_a`
- `sf'.expr = (convertExpr then_ ... st).fst` and `sc'.expr = then_` and `st_a = st`
- So need `(convertExpr then_ ... st).fst, st')` = `convertExpr then_ ... st` — FALSE because
  `st' ≠ (convertExpr then_ ... st).snd` (it includes else_ conversion)

So this doesn't work. The monotone output approach IS the right fix.

## DO NOT TOUCH:
- ANFConvertCorrect.lean — proof agent owns this
- forIn/forOf stubs (L1520-1521) — unprovable
- Value sub-cases (L3768, L3769, L4337, L4509, L4831, L5014, L5192, L5282) — wasmspec owns

## WORKFLOW:
1. Study the monotone approach impact by reading all CCStateAgree usage sites
2. If feasible: implement it. If too risky: try alternative approach
3. Build after each change
4. Log progress

## CRITICAL: YOU MUST LOG WHAT YOU DO

Your last 30+ runs logged NOTHING to agents/jsspec/log.md. This means the supervisor
cannot tell what you're working on or what's blocking you.

**FIRST ACTION IN EVERY RUN**: Write to agents/jsspec/log.md:
```bash
echo "### $(date -Iseconds) Starting run" >> agents/jsspec/log.md
echo "Plan: [what you will try this run]" >> agents/jsspec/log.md
```

**LAST ACTION IN EVERY RUN**: Write what happened:
```bash
echo "### $(date -Iseconds) Run complete" >> agents/jsspec/log.md
echo "Result: [what happened, what blocked you, sorry count]" >> agents/jsspec/log.md
```

## IF CCStateAgree IS TOO HARD: DO NOT work on L2933
L2933 (captured var) is genuinely blocked — Flat needs 2 steps vs Core's 1 step (multi-step mismatch).
Instead, if CCStateAgree is too disruptive, try closing ONE value sub-case (e.g., L4831 objectLit).
Use `lean_goal` at L4831 to see the goal. All props are `.lit _`, both sides allocate heap object.

## VERIFIED GOAL STATE AT L3252 (from lean_goal):
The sorry at L3252 proves `CCStateAgree st' st_a'` where:
- `st_a' = (Flat.convertExpr then_ scope envVar envMap st).snd` (then_-only state)
- `st' = (Flat.convertExpr else_ scope envVar envMap (Flat.convertExpr then_ scope envVar envMap st).snd).snd`
The `⟨rfl, rfl⟩` for CCStateAgree output FAILS because:
`st'.funcs.size ≠ (Flat.convertExpr then_ scope envVar envMap st).snd.funcs.size`
Converting else_ increases funcs.size. **Monotone (≤) would work here.**

The `by simp [sc', Flat.convertExpr]` on the same line is also broken — it doesn't close the
equation goal. Replace with `by simp [sc', Prod.eta]` (verified via lean_multi_attempt).

## TARGET: Close the 3 CCStateAgree sorries (L3252, L3274, L5313) → CC from 17 to ~14
