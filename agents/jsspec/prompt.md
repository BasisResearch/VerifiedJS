# jsspec — Close the SIMPLEST CC sorries first. You closed ZERO last run.

## RULES
- **DO NOT** run `lake build VerifiedJS` (full build). OOMs.
- Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
- Before building: `pkill -f "lean.*\.lean" 2>/dev/null; sleep 5`
- **NEVER** use `pgrep -f "lake build"` inside a while loop (self-matches)
- Check builds with: `pgrep -x lake` (not `-f`)

## MEMORY: 7.7GB total, NO swap.

## DO NOT TOUCH THESE SORRIES:
- 47 "Fix D reverted" sorries (lines 1627-2157, 2289-2606) — BLOCKED
- 2 forIn/forOf sorries (L1369-1370) — unprovable stubs
- ANFConvertCorrect.lean — proof agent owns this

## YOUR LAST RUN CLOSED ZERO SORRIES IN 2 HOURS. CHANGE APPROACH.

Stop trying complex proofs. Start with the ABSOLUTE simplest sorry you can close.

## TARGET 1: ExprAddrWF propagation (L4890, L4988) — SIMPLEST

L4890: `ExprAddrWF (.objectLit _)` doesn't propagate to elements.
L4988: `ExprAddrWF (.arrayLit _)` doesn't propagate to elements.

APPROACH:
1. `lean_goal` at L4890 to see exact goal
2. `lean_hover_info` on `ExprAddrWF` to see its definition
3. Try `lean_multi_attempt` at L4890 with:
   ```
   ["simp [ExprAddrWF]",
    "unfold ExprAddrWF; simp",
    "simp_all [ExprAddrWF]",
    "intro h; exact absurd h (by decide)",
    "exact ExprAddrWF.of_objectLit ‹_› ‹_›",
    "cases hexprwf; assumption"]
   ```
4. If none work, read the ExprAddrWF definition and write the exact unfolding proof.

## TARGET 2: CCState threading (L3267, L4937) — MEDIUM

L3267: `sorry⟩ -- CCState threading: st' includes else_ conversion but st_a' only then_`
L4937: `sorry -- CCState threading: convertPropList over concatenated lists`

APPROACH:
1. `lean_goal` at L3267 to see what CCState property is needed
2. Search for CCState monotonicity lemmas: `lean_local_search "CCState"`
3. Try `omega`, `simp`, or explicit transitivity

## TARGET 3: value sub-cases (L3783, L4524, L4846, L4944)

L3783: callee is value, arg stepping or call execution
L4524: value sub-case (heap reasoning)
L4846: all props are values: heap allocation
L4944: all elements are values: heap allocation

## WORKFLOW FOR EACH SORRY:
1. `lean_goal` at the sorry line — read the FULL goal
2. `lean_multi_attempt` with 6-8 simple tactics
3. If nothing closes it in 5 minutes, MOVE TO THE NEXT ONE
4. Do NOT spend more than 15 minutes on any single sorry

## VERIFICATION
After any sorry closure:
1. Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
2. Count: `grep -c sorry VerifiedJS/Proofs/ClosureConvertCorrect.lean`
3. Log to agents/jsspec/log.md

## TARGET: Close at least 2 sorries. Prioritize QUANTITY over difficulty.
