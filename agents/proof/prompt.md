# proof — CC SORRY REDUCTION (objectLit/arrayLit/call)

## CRITICAL: Your last run (13:30) produced NO OUTPUT. You must produce results this cycle.

## CURRENT STATE: 17 ANF, 20 CC grep / 18 actual, 1 Lower = 56 grep total. ZERO change from last run.

## ANF hk GENERALIZATION IS BLOCKED — DO NOT ATTEMPT

The hk generalization requires redesigning `ANF_SimRel` (L59-66). The trivial-preserving property flows through:
- `ANF_SimRel` stores it (L65-66)
- `normalizeExpr_labeled_step_sim` conclusion returns it (L1467)
- The labeled case passes `hk` through (L1528): `exact ⟨k, n, m', hres, hk⟩`
- Helper theorems (`normalizeExpr_var_step_sim`, `normalizeExpr_var_implies_free`) require it
- ALL proved cases in `anfConvert_step_star` extract and use `hk_triv`

Weakening the hypothesis cascades everywhere. This is a planned multi-step refactor. Skip it for now.

## PRIORITY 0: Integrate objectLit/arrayLit from staging (-2 sorries → target 54 grep)

Staging proofs at:
- `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_proof.lean`
- `.lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_helpers.lean`

Read these staging files FIRST. Then integrate at ClosureConvertCorrect.lean L3018-3019.

Pattern: same as your setProp/setIndex integration (expand into value/non-value sub-cases, close non-value, sorry value sub-case). Expected: -2 sorries or 0 net if each expands to 1 sorry.

Steps:
1. `cat .lake/_tmp_fix/VerifiedJS/Proofs/cc_objectLit_arrayLit_proof.lean` — read the proof structure
2. Replace `| objectLit props => sorry` (L3018) with the expanded proof
3. Replace `| arrayLit elems => sorry` (L3019) with the expanded proof
4. Build: `lake env lean VerifiedJS/Proofs/ClosureConvertCorrect.lean`
5. Fix any build errors

## PRIORITY 1: Close CC call case (L2588, -1 sorry)

Read staging: `.lake/_tmp_fix/VerifiedJS/Proofs/cc_call_patches.lean`

The `call` case in `closureConvert_forward` (L2588). Check if the staging file has a proof.

## PRIORITY 2: CC captured variable (L1828)

The `| some idx =>` case of var lookup. convertExpr gives `.getEnv (.var envVar) idx`. The Flat step evaluates the var to the env pointer, then indexes. Thread `EnvCorrInj` to relate Core env lookup to Flat getEnv.

## PRIORITY 3: CC functionDef (L3020)

Read the functionDef case of convertExpr to understand the Flat output structure. This may be similar to call.

## WORKFLOW
1. Read staging files for objectLit/arrayLit
2. Integrate proofs at L3018-3019
3. Build and verify
4. If successful: attempt call (L2588) or captured var (L1828)
5. Log everything to agents/proof/log.md with exact sorry counts

## FILES YOU OWN
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)

## IMPORTANT
- The forIn/forOf sorries (L1132-1133) are in `convertExpr_not_value` which appears unused. SKIP.
- The 5 value sub-cases (getProp L2595, getIndex L2653, assign L2723, delete L2792, L2876) all need heap reasoning. Skip for now.
- while_ (L3141) and if CCState (L2147, L2169) are CCState threading issues. Skip.
