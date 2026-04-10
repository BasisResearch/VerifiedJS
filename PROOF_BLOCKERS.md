# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ❌ ANF OOM-KILLED (exit 137). CC build status unknown. (2026-04-10T19:05)

ANFConvertCorrect.lean (18,698 lines) exceeds available memory (7.7GB total, ~500MB free, no swap).
FIX: Collapse if_branch `| succ d ih =>` to single sorry (saves ~1200 lines, all blocked by K-mismatch anyway).

## Sorry Count: 75 (ANF 60 + CC 15 + Lower 0) — as of 2026-04-10T19:05

### ANF (54 sorries):
- 1 trivialChain passthrough (L10203) — BLOCKED (K-mismatch)
- 5 second-position trivial mismatch (L10253-10399) — BLOCKED (K-mismatch)
- 6 list/func decomposition (L10375-10518) — needs list iteration infra
- 7 compound throw/return/await/yield (L11765, L11916, L11922, L12093, L12099, L12251, L12257) — BLOCKED by Flat.step? not propagating errors. **FIX IN PROGRESS** (proof agent)
- 3 return/yield structural (L12288, L12292, L12318) — wasmspec assigned
- 2 while (L12408, L12420) — transient state / flat simulation
- 24 if_branch (L14028-14343, L15262-15577) — BLOCKED (K-mismatch, needs theorem redesign)
- 3 tryCatch (L16418, L16436, L16439) — wasmspec assigned
- 2 callframe sorries (L17522, L17533) — wasmspec assigned
- 2 remaining (L17753, L17806) — unassigned

### CC (12 sorries):
- 1 HeapInj staging (L4905) — RESTORABLE from git
- 2 CCStateAgree if-branch (L5234, L5257) — BLOCKED (blocker P)
- 1 funcs correspondence (L5821) — potentially provable
- 2 multi-step simulation gap (L6029, L6037) — BLOCKED
- 1 UNPROVABLE (L6675) — getIndex string
- 1 functionDef (L7917) — large, needs infrastructure (blocker S)
- 3 tryCatch (L8074, L8075, L8147) — CCStateAgree blocked
- 1 while CCState threading (L8255) — BLOCKED

### Lower: 0 ✓ DONE

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
