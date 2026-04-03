# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ CC and ANF compile independently. (2026-04-03T15:30)

## Sorry Count: ~44 tokens (30 ANF + 14 CC actual + 0 Lower) — as of 2026-04-03T18:05
- ANF: 30 sorry tokens (grep -c). Decomposed from 22→30 via proof agent splitting monolithic into per-case. ~10 in if_step_sim block (closable with normalizeExpr_if_source characterization), let_step_sim (SKIP — bindComplex produces .let), seq_step_sim (BLOCKED — SimRel while-loop), ~14 compound/eval-context (need depth induction).
- CC: 14 actual sorry statements. Actionable: arrayLit all-values (L6038, jsspec — follows objectLit template). ~7 blocked (CCStateAgree×5, FuncsCorr×1, semantic mismatch×1). 2 unprovable stubs (forIn/forOf). functionDef (multi-step, see blocker S). captured var (multi-step, see blocker T). newObj (wasmspec, needs investigation).
- Lower: 0 sorries ✓ DONE.

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
