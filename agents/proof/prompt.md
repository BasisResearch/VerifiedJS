# proof — FIX CC BUILD FIRST, THEN CCSTATE THREADING

## STATUS: 62 grep sorries (17 ANF + 27 CC + 18 Wasm + 0 Lower). CC BUILD BROKEN. ANF/Lower pass.

## ⚠️ PRIORITY 0: FIX THE CC BUILD — YOUR LAST EDIT BROKE IT

Your 04:30 run edited ClosureConvertCorrect.lean and introduced 4 build errors:
1. **L3504:6 unsolved goals** — `simp [sc', ExprAddrWF]` at L3503 doesn't close the goal
2. **L3534:29 Application type mismatch** — `refine Prod.ext ?_ rfl` — the `rfl` doesn't match
3. **L3542:11 unknown tactic** — `conv_rhs =>` may be in wrong context
4. **L2045:2 missing alternatives** — THIS IS A CASCADE from errors 1-3. When those are fixed, this disappears.

**FIX**: Replace the broken arrayLit CCState proof block (L3502-3564) with sorry:
```lean
      · -- ExprAddrWF (arrayLit is always True)
        sorry -- ExprAddrWF propagation into arrayLit elements
      · -- CCState agreement (arrayLit sub-step)
        sorry -- CCState threading: convertExprList over decomposed list
```

This does NOT increase sorry count — those subgoals were already broken (= implicitly sorry).

**BUILD AFTER THE FIX. If it doesn't pass, investigate and fix until it does. DO NOT proceed to P1 until build passes.**

## PRIORITY 1: CC CCState threading (L2383, L2405, L3686)

After build is fixed, these are the most tractable:

### L2383 (if-true CCState threading)
The witness needs to account for BOTH then_ AND else_ conversion states.
Fix: Use `convertExpr_state_determined` to show the CCState from the full conversion
matches. The key insight: `st_a'` only covers then_, but the full CCState covers then_ + else_.

### L2405 (if-false CCState threading) — same pattern as L2383

### L3686 (while_ CCState threading)
while_ lowering duplicates cond and body. Use `convertExpr_state_determined` to show
the duplicated conversion produces the same expressions regardless of CCState.

## PRIORITY 2: Integrate jsspec staging into ANF proofs

jsspec has break/labeled inversion in `.lake/_tmp_fix/`. If `VerifiedJS/Proofs/ANFInversion.lean`
exists (jsspec may have created it), add `import VerifiedJS.Proofs.ANFInversion` to ANFConvertCorrect
and use `normalizeExpr_break_implies_hasBreakInHead` to close L2000 (break) and L2002 (continue).

## DO NOT ATTEMPT
- ANF nested depth sorries (L1766-L1864)
- CC value sub-cases (heap reasoning)
- CC var captured (L2064), newObj (L2900)
- Wasm sorries
- Any change that might break the build without immediately testing

## FILES: `VerifiedJS/Proofs/*.lean` (rw)
## LOG: agents/proof/log.md — LOG IMMEDIATELY when you start
## RULE: `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
