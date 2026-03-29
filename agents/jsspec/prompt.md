# jsspec — EXCELLENT CC WORK. Now: ANF sorries (17 remaining).

## STATUS: Your CC v3 patch is staged. Proof agent will integrate. YOU are done with CC.

## NEW MISSION: Close ANF sorries in ANFConvertCorrect.lean

### ANF Sorry Map (17 sorries) — VERIFIED locations:

#### EASIEST (do these first):
1. **L3424** — break: "both produce .error, needs normalizeExpr inversion"
2. **L3426** — continue: same pattern as break
3. **L3396** — return: "evaluate optional trivial arg"
4. **L3398** — yield: same pattern as return
5. **L3400** — await: same pattern as return

#### MEDIUM:
6. **L3368** — let-binding: evalComplex evaluates rhs, extends env, continues with body
7. **L3370** — sequence: either a is value (skip to b) or step inner a
8. **L3372** — conditional: evaluate cond, branch
9. **L3394** — try-catch: step body, catch errors, handle finally

#### RECURSIVE/HARD:
10-17. **L3190, L3194, L3205, L3256, L3260, L3271, L3288, L3392** — nested cases needing induction on depth

### APPROACH:
1. `lean_goal` at each sorry to get exact goal state
2. Start with L3424 (break) and L3426 (continue) — should be identical pattern
3. For each, try `lean_multi_attempt` with:
   - `["simp [normalizeExpr]", "cases on normalizeExpr structure", "omega"]`
4. Write proofs directly into ANFConvertCorrect.lean if you have write access
5. If no write access: stage in `.lake/_tmp_fix/anf_<case>.lean` with patch

### KEY INSIGHT from proof agent:
- Break/continue both produce `.error` on both sides. The `normalizeExpr` wrapper shouldn't change this.
- Return/yield/await evaluate an optional arg that should be trivial (value or absent).
- The recursive cases (L3190, L3194, etc.) need proper depth induction — skip these for now.

### CONSTRAINTS:
- DO NOT edit `VerifiedJS/Proofs/ClosureConvertCorrect.lean`
- DO NOT edit `VerifiedJS/Wasm/Semantics.lean`
- CAN try to edit: `VerifiedJS/Proofs/ANFConvertCorrect.lean`
- CAN write: `.lake/_tmp_fix/` (staging area)
- LOG every 30 min to agents/jsspec/log.md
