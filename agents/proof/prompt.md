# proof — THROW LIST + COMPOUND CASES

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep
- **CRASH PREVENTION**: Keep tasks SMALL. Do ONE case, verify, move to next.

## MEMORY: 7.7GB total, NO swap. USE LSP ONLY.

## STATUS — 2026-04-12T10:05
- ANF: **8 sorry-using declarations** (35 sorry instances). CC: 12 instances. Total: **47 real**.
- FLAT since 09:05. No agent has committed anything in the last hour.
- Previous methodology was undercounting inline sorries. Real count is higher than 30.

## P0: THROW/LIST AREA (6 sorries — L16180, L16275, L16286, L16288, L16290, L16292)

**LINE NUMBERS SHIFTED** from last prompt. Verify with `lean_goal` before editing.

- **L16180**: third-operand — obj and idx evaluate, then val steps
- **L16275**: list — f and env evaluate, then args list steps
- **L16286**: list — f and env evaluate, then args list steps
- **L16288**: list case — first non-value element in values has throw
- **L16290**: list case — first non-value prop in props has throw
- **L16292**: list case — first non-value element in elems has throw

For L16288-16292, the pattern is:
- HasThrowInHeadList/Props gives the first non-value element with throw
- Split the list at that element: `values = prefix ++ [elem] ++ suffix` where prefix is all values
- Flat.step? steps `elem` through the compound context
- Use ctx lemmas (check with `lean_local_search "step?.*ctx"`)
- Apply IH on the inner element

### EXECUTION:
1. `lean_goal` at L16288 to see what's needed
2. `lean_local_search "throwInHead.*list"` to find existing infrastructure
3. Prove L16288 first (simplest), replicate for L16290, L16292
4. Then L16180 (third-operand), L16275, L16286

## P1: COMPOUND AWAIT/YIELD/RETURN (5 sorries — L23959, L24132, L24188, L24192, L24193)

- **L23959**: compound HasAwaitInHead — blocked by Flat.step? error propagation
- **L24132**: compound HasYieldInHead — same blocker
- **L24188**: return (some val) — compound, can produce .let
- **L24192**: yield (some val) — compound, can produce .let
- **L24193**: compound expressions (seq, let, assign, if, call, etc.) — needs structural induction

These use the SAME error-propagation pattern as compound throw. Check for `compound_lift` or `abruptHead_compound_lift` infrastructure.

## P2: WHILE CONDITION (2 sorries — L24283, L24295)
- L24283: While condition value case — transient state breaks single-step SimRel
- L24295: Condition-steps case — needs flat while-condition simulation

## P3: IF-BRANCH K-MISMATCH (2 sorries — L25020, L25060)
- L25020: if_branch true — collapsed for OOM fix, 24 sub-cases blocked by K-mismatch
- L25060: if_branch false — same
- These are inside `normalizeExpr_if_branch_step` (L24982) and its false variant

## P4: TRYCATCH (3 sorries — L25901, L25919, L25922)
- L25901: tryCatch body-error
- L25919: tryCatch body-step — blocked by callStack propagation + counter alignment
- L25922: compound cases — deferred

## BLOCKED (12): L11366-L11737 — labeled-in-compound area. DO NOT TOUCH until error propagation infrastructure exists.

## FULL SORRY MAP (35 instances across 8 declarations):
- **BLOCKED (12)**: L11366, L11414, L11462, L11512, L11539, L11589, L11591, L11641, L11643, L11674, L11706, L11737
- **P0 (6)**: L16180, L16275, L16286, L16288, L16290, L16292 ← START HERE
- **P1 (5)**: L23959, L24132, L24188, L24192, L24193
- **P2 (2)**: L24283, L24295
- **P3 (2)**: L25020, L25060
- **P4 (3)**: L25901, L25919, L25922
- **WASMSPEC (3)**: L18673, L27249, L27250 (wasmspec owns these)
- **END (2)**: L27469, L27540

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — [task]" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
