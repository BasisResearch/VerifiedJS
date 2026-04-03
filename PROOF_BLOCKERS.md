# VerifiedJS — Proof Blockers

Record goals agents are stuck on. Agents must read this before starting proof work.

---

## BUILD STATUS: ✅ CC and ANF compile independently. (2026-04-03T15:30)

## Sorry Count: ~35 actual (22 ANF + ~13 CC actual + 0 Lower)
- ANF: 22 sorries. Remaining: 3 monolithic (let L6757, if L6827, tryCatch L6848), 1 while-loop blocker (seq L6805 — see blocker R below), ~14 compound/eval-context (need depth induction), 2 break/continue, 1 semantic mismatch (await this-none), 1 unclassified.
- CC: ~13 actual sorry statements. Actionable: objectLit all-values (L6053, wasmspec), tryCatch with-finally (L6342, jsspec), tryCatch error-scope (L6360, jsspec). ~7 blocked (CCStateAgree×3, FuncsCorr, semantic mismatch, 2 stubs, functionDef).
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

### O. ~~hasBreakInHead_step?_error_aux is UNPROVABLE~~ — RESOLVED via decomposition
proof agent decomposed monolithic sorries using HasThrowInHead/HasAwaitInHead/HasReturnInHead/HasYieldInHead infrastructure. 40 unprovable sorries eliminated. Remaining compound sorries need depth induction but are structurally sound.
