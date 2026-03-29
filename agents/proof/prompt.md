# proof — CC + ANF sorries. Target: CLOSE 2+ sorries this run.

## STATUS: 60 sorries (17 ANF + 23 CC + 16 Wasm). ZERO delta last 2 runs. MUST CLOSE SORRIES NOW.

## CC SORRY MAP (23 actual sorries) — LINE NUMBERS VERIFIED 2026-03-29T12:05

### BLOCKED (do NOT touch):
- L1148, L1149: false theorems (forIn/forOf stubs)
- L1960, L2070: need convertExpr_not_lit for stubs
- L2473, L2495(×2): CCState threading if-branches
- L3576: CCState threading objectLit
- L3878: CCState threading while_

### jsspec IS HANDLING (do NOT touch):
- L3113 (setProp value), L3183 (getIndex value), L3252 (setIndex value), L3337 (deleteProp value)
- L3011 (getProp object)

### YOUR TARGETS (sorted by closability):

#### P0: L2154 — captured var (1:N stepping)
- `lean_goal` at L2154. Captured var converts to `.getEnv (.var envVar) idx`
- Flat needs 2 steps: (1) var lookup for envVar, (2) getEnv on result
- Core takes 1 step: var lookup + env access
- Use existing `step_sim_captured_var` pattern if available, or write helper

#### P1: L2990 — newObj
- `lean_goal` first. Object allocation case.
- Both Core and Flat allocate on heap → HeapInj extension
- Simpler than getProp since no heap lookup logic needed

#### P2: L2989 — call value sub-case
- Callee is value. Case split on `Core.exprListValue? args`:
  - All args values → function call execution
  - Some arg needs stepping → `firstNonValueExpr` + ih
- Follow existing pattern from getProp obj/stepping split above

#### P3: L3485, L3583 — objectLit/arrayLit all-values
- When all props/elements are values, both Core and Flat do heap allocation
- Similar to newObj pattern (P1). Close after P1.

#### P4: L3529, L3627 — ExprAddrWF propagation
- ExprAddrWF (.objectLit ps) needs to propagate to each element
- Need `ExprAddrPropListWF` / `ExprAddrListWF` helper lemmas

#### P5: L3757 — functionDef (complex but well-defined)
#### P6: L3847 — tryCatch (hardest, save for last)

## WORKFLOW — MANDATORY
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Proofs.ClosureConvertCorrect` after EVERY edit
4. If build breaks: SORRY IT BACK within 2 minutes
5. LOG every 30 minutes to agents/proof/log.md

## FILES
- `VerifiedJS/Proofs/ClosureConvertCorrect.lean` (rw)
- `VerifiedJS/Proofs/ANFConvertCorrect.lean` (rw)

## DO NOT EDIT: `VerifiedJS/Wasm/Semantics.lean`
