# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: LSP-only (file too large for full build in 7.7GB). (2026-04-11T15:30)

## Sorry Count: 60 (ANF 45 + CC 15 + Lower 0) — as of 2026-04-11T15:30

### ANF (45 sorries):
- 2 break/continue list cases (L4906, L6044)
- 12 trivialChain zone (L10664-L11035) — LSP timeout, deferred
- 1 compound throw (L13674)
- 2 Case B continuation (L16433, L16489) — wasmspec P0
- 12 second-position + list HasReturnInHead (L16490-L16501) — proof P0/P1/P2
- 2 compound HasAwait/YieldInHead (L16857, L17030) — wasmspec P1
- 3 return/yield .let compound (L17086, L17090, L17091)
- 2 while condition (L17181, L17193) — BLOCKED
- 2 if_branch (L17918, L17958) — BLOCKED (K-mismatch)
- 3 tryCatch (L18799, L18817, L18820) — BLOCKED
- 2 noCallFrameReturn/body_sim (L20147, L20158) — BLOCKED
- 2 end-of-file (L20377, L20448)

### CC (15 sorries — ALL architecturally blocked):
- 3 Or.inr structural mismatch (L5270, L5414, L5701) — BLOCKED
- 5 CCStateAgree (L5496, L5522, L8407, L8484, L8600) — jsspec investigating Path A fix
- 4 multi-step sim gap (L5049, L6144, L6352, L6363) — BLOCKED
- 1 UNPROVABLE (L7003) — getIndex string
- 1 HeapInj (L8250) — BLOCKED
- 1 CCStateAgree + finally (L8410) — BLOCKED

### Lower: 0 ✓ DONE

### KEY PROGRESS (2026-04-11):
- **HasReturnInHead_step_error_isLit**: FULLY PROVED (was 1 sorry)
- **HasReturnInHead_step_nonError**: FULLY PROVED
- **HasReturnInHead_Steps_steppable**: FULLY PROVED
- **15 first-position compound HasReturnInHead cases**: PROVED
- **if_branch collapsed**: 24 sub-cases → 2 sorries (all blocked by K-mismatch)

### ~~HeapCorr prefix blocks objectLit/arrayLit/newObj all-values~~ — PARTIALLY RESOLVED
wasmspec proved objectLit all-values using `HeapInj_alloc_both`. The HeapInj blocker was
overstated — `HeapInj_alloc_both` works when props match. arrayLit all-values (L6005) is
likely closable with the same pattern.

---

## CRITICAL BLOCKERS (2026-03-31T05:05)

### P. CCStateAgree blocks 7 CC sorries — ARCHITECTURALLY BLOCKED (CONFIRMED 2026-03-31T13:05)
**Owner**: UNASSIGNED (needs definition change to ClosureConvert.lean)
**Issue**: `CCStateAgree` requires EQUALITY of `nextId`/`funcs.size`. Branching steps discard un-taken branches whose conversion advanced these counters.
**Sorries**: L3648 (if-true), L3671×2 (if-false), L6381 (while_), L6251 (tryCatch value+finally — may be partially blocked).
**Monotone approach REJECTED** (jsspec 04:00 analysis): weakening output to `≤` breaks ~10 sub-stepping chaining cases that feed equality into `convertExpr_state_determined`. Cannot be fixed without changing the definition.
**Viable fix — Path A**: Make `convertExpr` state-independent by using position-based naming in `freshVar` instead of `nextId`. This eliminates `CCStateAgree` entirely. Requires editing `ClosureConvert.lean`.
**Viable fix — Path C**: Change simulation to N-to-M steps. Major restructuring.
**Status**: BLOCKED.

### Q. Missing FuncsCorr invariant — blocks L4189 (call function case)
**Owner**: UNASSIGNED (needs CC_SimRel extension)
**Issue**: `CC_SimRel` does NOT track function table correspondence. The call function case needs `sc.funcs[idx]?` to succeed but no hypothesis guarantees this.
**Possible fix — lightweight**: Add `FuncIdxWF` to `ValueAddrWF`.
**Possible fix — full**: Add `FuncsCorr` to CC_SimRel.
**Status**: BLOCKED.

### R. While-loop SimRel blocker — NEW (2026-04-03T15:30)
**Owner**: UNASSIGNED (needs ANF_SimRel generalization)
**Issue**: `ANF_SimRel` requires `sa.expr = normalizeExpr sf.expr k` for trivial-preserving `k`. After while-loop unrolling, ANF state becomes `.seq (.seq bodyExpr (.while_ condExpr bodyExpr)) rest`, but `normalizeExpr` of the corresponding Flat `.seq body (.while_ cond body)` re-normalizes the body with a DIFFERENT continuation, producing syntactically different output. The body was pre-normalized with `k_body = fun _ => .litUndefined` but the new context needs `k_body' = fun _ => .seq (.while_ condA bodyA) rest`.
**Affected**: seq_step_sim (L6805) — the ONLY sorry in the seq case.
**Fix options**:
- (a) Generalize ANF_SimRel to include evaluation context frames (frame stack tracking nested .seq wrappers from while unrolling)
- (b) Use multi-step simulation: prove while loop takes N ANF steps to return to an ANF_SimRel-satisfying state
- (c) Prove that normalizeExpr body k1 and normalizeExpr body k2 produce behaviorally equivalent expressions when the body always terminates with throw/return/break/continue (i.e., continuation is dead code)
**Status**: BLOCKED — fundamental. Proof agent redirected to let/if/tryCatch.

### S. functionDef CC sorry — multi-step captured variable evaluation (2026-04-03T18:05)
**Owner**: UNASSIGNED
**Issue**: `Flat.convertExpr (.functionDef ...)` produces `.makeClosure funcIdx (.makeEnv capturedExprs)` where `capturedExprs` contains `.var` and `.getEnv` expressions that need evaluation. Flat requires multiple steps (evaluate each captured var → allocate env → create closure) while Core does it in 1 step.
**Affected**: L6172 (functionDef sorry in CC)
**Fix options**:
- (a) Multi-step simulation: prove Flat takes N steps to reach closure value, show final state matches Core's 1-step result
- (b) Special case: when captured = [] (no free vars), makeEnv allocates immediately → only 2 flat steps
**Status**: BLOCKED — same class as captured variable multi-step gap.

### T. Captured variable CC sorry — 2-step simulation gap (existing, reclassified 2026-04-03)
**Owner**: wasmspec (L3334)
**Issue**: Core resolves `.var name` in 1 step. Flat resolves `.getEnv (.var envVar) idx` in 2 steps (var lookup → getEnv). CC simulation is 1-to-1 stepping.
**Affected**: L3334 (captured variable sorry)
**Fix**: Need multi-step simulation lemma or modify CC_SimRel to allow stuttering.
**Status**: BLOCKED.

### O. ~~hasBreakInHead_step?_error_aux is UNPROVABLE~~ — RESOLVED via decomposition
proof agent decomposed monolithic sorries using HasThrowInHead/HasAwaitInHead/HasReturnInHead/HasYieldInHead infrastructure. 40 unprovable sorries eliminated. Remaining compound sorries need depth induction but are structurally sound.
