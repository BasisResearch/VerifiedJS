# proof — CC SORRY REDUCTION (newObj → objectLit → arrayLit)

## STATUS: 0 Lower, 17 ANF, 20 CC, 18 Wasm. Total grep: 55. ZERO CHANGE in 4 hours.

## YOUR LAST RUN (17:30) GOT OOM KILLED (code 137). Your 20:30 run has NO logged output.

If you are reading this, you need to LOG IMMEDIATELY, then work on P0.

## PRIORITY 0: CC newObj case (-1 CC sorry) — SIMPLEST TARGET

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean` line 2699.

You ALREADY proved the call non-value sub-case (L2686-2697). The newObj case at L2699 is structurally IDENTICAL:
- Both have `ExprAddrWF f n ∧ (∀ e, e ∈ args → ExprAddrWF e n)` (you fixed this)
- Both step the first non-value argument
- Both use `Flat_step?_call_func_step` pattern (or the newObj analog)

Copy the call non-value pattern:
1. Case split on `exprValue? f`:
   - `none` → step the callee, use IH. This is the call non-value proof at L2686-2697.
   - `some cv` → sorry (value sub-case, heap reasoning, skip)
2. For the `none` case, you need `Flat.step?` on `.newObj f args` when `exprValue? f = none`. Check if it steps the callee like `.call` does. If so, the proof is copy-paste from call.

**Build command**: `lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean 2>&1 | grep error | head -20`

## PRIORITY 1: CC objectLit (-1 CC sorry)

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean` line 3129.

jsspec staging infrastructure exists in `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`:
- `convertPropList_append`
- `propListNoCallFrameReturn_append`
- `listNoCallFrameReturn_append`

Strategy:
1. Case split on first non-value prop in `props`
2. If all values → allocate object, sorry the heap reasoning
3. If first prop non-value → step inner, use IH
4. Empty props → trivial

This is HARDER than newObj. Only attempt after P0.

## PRIORITY 2: CC arrayLit (-1 CC sorry)

Line 3130. Similar to objectLit but simpler (no prop names). Only attempt after P0/P1.

## DO NOT ATTEMPT
- ANF sorries (blocked on inversion infrastructure from jsspec)
- Wasm sorries (structurally blocked, axiom issues)
- CC value sub-cases (L2698, 2705, 2763, 2833, 2902, 2987 — heap reasoning)
- CC forIn/forOf (L1148-1149 — theorem false for stubs)
- CC while_ (L3252), tryCatch (L3221), functionDef (L3131)
- CC CCState threading (L2182, L2204)

## STALE COMMENT TO FIX (while you're in the file)

ANFConvertCorrect.lean L1948: "break: ANF produces .silent but Flat produces .error" — this is WRONG. wasmspec fixed ANF break to produce `.error` matching Flat. Update the comment to: "break: both produce .error, needs normalizeExpr inversion"

Same at L1950 for continue.

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/LowerCorrect.lean` (rw)

## WORKFLOW
1. LOG what you're doing immediately
2. Try newObj first — highest probability of success
3. Build after each edit
4. If stuck on newObj after 20 min, try objectLit
5. Log to agents/proof/log.md with EXACT sorry counts and build status
