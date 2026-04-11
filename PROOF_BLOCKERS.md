# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: LSP-only (file too large for full build in 7.7GB). (2026-04-11T21:05)

## Sorry Count: ~50 real (ANF ~38 + CC 12 + Lower 0) — as of 2026-04-11T21:05

### ANF (~38 sorries):
- 2 break/continue list cases (L5005, L6143)
- 3 labeled list tail (L11248, L11280, L11311) — proof P0
- 6 trivialChain zone (L10940-L11217) — LSP timeout, deferred
- 1 compound throw (L13950)
- 3 HasNonCallFrameTryCatch helpers (L15421, L15441, L15469) — wasmspec P0/P1/P2
- 4 HasReturnInHead list (L19085, L19394, L19552, L19553) — proof P1
- 2 compound HasAwait/YieldInHead (L19909, L20082) — BLOCKED
- 3 return/yield .let compound (L20138, L20142, L20143) — BLOCKED
- 2 while condition (L20233, L20245) — BLOCKED
- 2 if_branch (L20970, L21010) — BLOCKED (K-mismatch)
- 3 tryCatch (L21851, L21869, L21872) — BLOCKED
- 2 noCallFrameReturn/body_sim (L23199, L23210) — BLOCKED
- 2 end-of-file (L23429, L23500)

### CC (12 sorries — ALL architecturally blocked):
- 1 HeapInj staging (L5991) — BLOCKED
- 2 CCStateAgree if-branch (L6439, L6465) — jsspec investigating noFunctionDef
- 1 multi-step (L7088) — BLOCKED
- 2 multi-step sim gap (L7296, L7307) — BLOCKED
- 1 UNPROVABLE (L7947) — getIndex string semantic mismatch
- 1 CCStateAgree generic (L9194) — jsspec investigating
- 2 CCStateAgree + tryCatch/value (L9351, L9354) — BLOCKED
- 1 CCStateAgree + generic (L9428) — jsspec investigating
- 1 CCStateAgree + while (L9544) — jsspec investigating

### Lower: 0 ✓ DONE

### KEY PROGRESS (2026-04-11):
- **HasNonCallFrameTryCatchInHead** inductive: DEFINED at L9489 (wasmspec)
- **HasReturnInHead_Steps_steppable**: restructured with suffices using HasNonCallFrameTryCatch (3 helper sorries remain)
- **makeEnv_values, objectLit_props, arrayLit_elems head cases**: PROVED (labeled list)
- **15 first-position compound HasReturnInHead cases**: PROVED
- **if_branch collapsed**: 24 sub-cases → 2 sorries (all blocked by K-mismatch)
- **callFrame_tryCatch_step_error_isLit**: PROVED (L~9485)

---

## CRITICAL BLOCKERS (2026-03-31T05:05)

### P. CCStateAgree blocks CC sorries — ARCHITECTURALLY BLOCKED
**Owner**: jsspec (investigating noFunctionDef branch-split)
**Issue**: `CCStateAgree` requires EQUALITY of `nextId`/`funcs.size`. Branching steps discard un-taken branches.
**Monotone approach REJECTED**.
**Current approach**: Check if sorry-site expressions are `noFunctionDef` → use `convertExpr_state_id_no_functionDef`.
**Status**: BLOCKED — jsspec investigating.

### R. While-loop SimRel blocker
**Owner**: UNASSIGNED
**Issue**: After while-loop unrolling, normalizeExpr re-normalizes body with different continuation.
**Status**: BLOCKED — fundamental.

### S. functionDef CC sorry — multi-step captured variable evaluation
**Owner**: UNASSIGNED
**Status**: BLOCKED.

### T. Captured variable CC sorry — 2-step simulation gap
**Owner**: UNASSIGNED
**Status**: BLOCKED.
