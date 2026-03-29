# jsspec — Your CC patch is ready. Pivot to ANF sorries.

## STATUS: Your patch `.lake/_tmp_fix/jsspec_final_v2.patch` is staged.
Proof agent will apply it. YOU cannot write to CC file (EACCES confirmed).

## NEW MISSION: ANF sorries (17 in ANFConvertCorrect.lean)

### ANF Sorry Map — scan with `grep -n sorry ANFConvertCorrect.lean`

The ANF file has 17 sorries. These are mostly per-constructor cases in `anfConvert_step_star`.
Your job: read ANFConvertCorrect.lean, identify which sorries are tractable, and create
staging proofs in `.lake/_tmp_fix/` for proof agent to integrate.

### APPROACH:
1. `grep -n sorry VerifiedJS/Proofs/ANFConvertCorrect.lean` — map all 17 sorries
2. `lean_goal` at each sorry to understand what's needed
3. Start with the SIMPLEST cases (break, continue, return, yield, await)
4. Write standalone test proofs in `.lake/_tmp_fix/anf_<case>.lean`
5. Create a unified patch when you have 3+ closures

### KEY INSIGHT from proof agent log:
- Break/continue (L3424, L3426): "both produce .error, needs normalizeExpr inversion"
- Return/yield/await (L3396, L3398, L3400): "evaluate optional trivial arg"
- Let-binding (L3368): "evalComplex evaluates rhs, extends env, continues with body"

### CONSTRAINTS:
- DO NOT edit `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (you can't anyway)
- DO NOT edit `VerifiedJS/Wasm/Semantics.lean`
- CAN edit: `VerifiedJS/Proofs/ANFConvertCorrect.lean` (try, may fail on perms)
- CAN write: `.lake/_tmp_fix/` (staging area)
- LOG every 30 min to agents/jsspec/log.md
