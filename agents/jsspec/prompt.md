# jsspec — ANF CASE HELPERS (LABELED, YIELD, AWAIT)

## STATUS: proof agent is installing your simp lemmas from staging. You now need to write CASE-SPECIFIC helpers.

## CRITICAL DISCOVERY: MORE BLOCKED CASES

observableTrace only filters `.silent`. These ANF cases produce DIFFERENT events from their Flat counterparts:
- **return none**: ANF → `.silent`, Flat → `.error "return:undefined"`. BLOCKED.
- **return some**: ANF → `.silent`, Flat → `.error "return:..."`. BLOCKED.
- **throw**: ANF → `.error "throw"`, Flat → `.error (valueToString v)`. BLOCKED (different strings).
- **break/continue**: Already known BLOCKED.

PROVABLE CASES (both sides produce matching events):
- **labeled** (L1158): both `.silent` → body
- **yield none** (L1154): both `.silent` → `.lit .undefined`/`.trivial .litUndefined`
- **yield some** (L1154): both `.silent` on success
- **await** (L1156): both `.silent` on success
- **if** (L1144): both `.silent` on branch
- **let** (L1140): complex (evalComplex)
- **seq** (L1142): complex (inner stepping)
- **while** (L1146): complex
- **tryCatch** (L1150): complex

## PRIORITY 0: Flat.step? simp lemmas for labeled/yield/await

Write these in `.lake/_tmp_fix/VerifiedJS/Proofs/anf_helpers.lean` (or new file):

```lean
-- Flat.step? on labeled: steps to body with .silent
@[simp] theorem Flat.step?_labeled (s : Flat.State) (label : Flat.LabelName) (body : Flat.Expr) :
    Flat.step? { s with expr := .labeled label body } =
      some (.silent, Flat.pushTrace { s with expr := body } .silent) := by
  simp [Flat.step?]

-- Flat.step? on yield none: steps to .lit .undefined with .silent
@[simp] theorem Flat.step?_yield_none (s : Flat.State) (delegate : Bool) :
    Flat.step? { s with expr := .yield none delegate } =
      some (.silent, Flat.pushTrace { s with expr := .lit .undefined } .silent) := by
  simp [Flat.step?]

-- Flat.step? on await with value: steps to .lit v with .silent
@[simp] theorem Flat.step?_await_value (s : Flat.State) (v : Flat.Value) :
    Flat.step? { s with expr := .await (.lit v) } =
      some (.silent, Flat.pushTrace { s with expr := .lit v } .silent) := by
  simp [Flat.step?, Flat.exprValue?]
```

Verify each with `lean_verify`. These are needed by proof agent for the easy cases.

## PRIORITY 1: normalizeExpr inversion for labeled case

The proof agent needs: if `(normalizeExpr sf.expr k).run n = .ok (.labeled label body_anf, m)`, then sf.expr = `.labeled label body_flat` for some `body_flat` and `(normalizeExpr body_flat k).run n = .ok (body_anf, m)`.

This is hard to prove for ALL Flat.Expr constructors (need StateT monad reasoning for compound cases). Try the approach:
1. Case split on `sf.expr`
2. For simple cases (var, lit, this, break, continue, etc.), `simp [normalizeExpr]` should give contradiction
3. For compound cases, may need `unfold normalizeExpr; simp` or monad reasoning

If full inversion is too hard, prove it for just the cases where `hk_triv` (k only produces .trivial) is available — this eliminates many compound cases.

## PRIORITY 2: Document which cases are provable vs blocked

Update `.lake/_tmp_fix/VerifiedJS/Proofs/design_issues.md` with the full blocked-case analysis above.

## DO NOT edit main proof files. Log to agents/jsspec/log.md.
