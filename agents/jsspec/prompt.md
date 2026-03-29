# jsspec — WASM SORRIES. wasmspec is ZOMBIE (17h+). You are the only one.

## STATUS
- ANF: 17 sorries, ALL blocked by continuation mismatch. DO NOT WORK ON ANF.
- CC: 25 sorries, proof agent handling. DO NOT WORK ON CC.
- Wasm: 16 actual sorries in Wasm/Semantics.lean. YOUR MISSION.

## YOUR TARGETS — 12 sorries (the 4 call/callIndirect are too hard)

### Pattern to follow: return-none (L6822-6863) is FULLY PROVED

The proof pattern for every `step_sim` case is:
1. `have hc := hrel.hcode; rw [hexpr] at hc` — get IR code structure from LowerCodeCorr
2. Invert `hc` to get the specific code shape (e.g., `hc.return_none_inv`, `hc.var_inv`)
3. Get ANF step lemma (e.g., `ANF.step?_return_none s1`)
4. Rewrite `heq` with the step result to extract `⟨rfl, rfl⟩`
5. Get IR step result (e.g., `irStep?_eq_return_toplevel`)
6. Match traces using `traceFromCore`
7. Construct new `LowerSimRel` for successor state with all fields

### EASIEST 5 (start here):

**L6876 — break**: Both sides produce error signal.
```lean
have hc := hrel.hcode; rw [hexpr] at hc
-- Look for: LowerCodeCorr.break_inv, ANF.step?_break
-- lean_local_search "step?_break" and "break_inv"
```

**L6879 — continue**: Identical to break.

**L6864 — return (some t)**: Follow return-none (L6822-6863).
- Need `hc.return_some_inv` to get `⟨argCode, hcode_eq, htcc⟩`
- See `step_sim_return_litNull` at L6884 for a specialized example
- Evaluate trivial arg, then return

**L6867 — yield**: Evaluate optional arg, produce yield event.

**L6870 — await**: Evaluate trivial arg, produce await event.

### MEDIUM 7:

**L6816 — throw**: Evaluate arg, produce error. Similar to return.
**L6806 — sequence**: Comments say needs 1:N stepping framework. Try anyway.
**L6798 — let**: Comments say needs IR multi-step. Try anyway.
**L6810 — if**: Evaluate cond, branch.
**L6813 — while**: Loop stepping.
**L6819 — tryCatch**: Error handling.
**L6873 — labeled**: Enter labeled block.

### WORKFLOW:
1. Read L6708-6863 (proven cases) as your template — especially var (L6708), return-none (L6822)
2. `lean_goal` at each sorry to see exact goal
3. `lean_local_search` for `step?_break`, `break_inv`, etc. to find available lemmas
4. `lean_hover_info` on `hc` after `rw [hexpr] at hc` to see what inversions exist
5. `lean_multi_attempt` to test tactic combinations
6. Edit file, then `lake build VerifiedJS.Wasm.Semantics`
7. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
8. Max 20 min per sorry. If stuck, move to next.
9. LOG every 30 min to agents/jsspec/log.md

### KEY LEMMAS TO SEARCH FOR:
- `ANF.step?_break`, `ANF.step?_continue`, `ANF.step?_yield`, `ANF.step?_await`, `ANF.step?_throw`
- `LowerCodeCorr.break_inv`, `.continue_inv`, `.yield_inv`, `.await_inv`, `.throw_inv`
- `irStep?_eq_*` for each IR instruction pattern
- `traceFromCore` for trace conversion

### CONSTRAINTS:
- CAN edit: `VerifiedJS/Wasm/Semantics.lean`
- DO NOT edit: `VerifiedJS/Proofs/*.lean`
- Stage helpers in `.lake/_tmp_fix/` if needed
- LOG every 30 min to agents/jsspec/log.md
