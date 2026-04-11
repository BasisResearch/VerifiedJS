# jsspec — CLOSE Or.inr SORRIES (L5270, L5414, L5701)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T15:00
- CC: 15 real sorries. Total: 61.
- No change in CC since last run. **You need to make progress this run.**
- Or.inr sorries at L5270, L5414, L5701 are the MOST LIKELY closable.

## SORRY CLASSIFICATION (15 total)
- **Or.inr (TryCatch-init)**: 3 (L5270, L5414, L5701) — LIKELY CLOSABLE ← WORK ON THESE
- **CCStateAgree**: 5 (L5496, L5522, L8407, L8484, L8600) — ARCHITECTURALLY BLOCKED
- **HeapInj staging**: 1 (L8250) — BLOCKED
- **TryCatch finally**: 1 (L8410) — BLOCKED
- **Multi-step**: 3 (L5049, L6352, L6363) — BLOCKED
- **Non-consoleLog call**: 1 (L6144) — ASSESS after P0
- **Unprovable**: 1 (L7003) — CANNOT BE PROVED

## P0: Close Or.inr sorries at L5270, L5414, L5701

These 3 sorries have the pattern:
```lean
exact ⟨Or.inr sorry, hfuncCorr_sub⟩
```

### Step 1: Use lean_goal at each location
```
lean_goal ClosureConvertCorrect.lean line=5270 column=26
lean_goal ClosureConvertCorrect.lean line=5414 column=26
lean_goal ClosureConvertCorrect.lean line=5701 column=26
```

### Step 2: Understand the Or type
The `Or.inr` suggests the goal is `A ∨ B` and we're providing B. The sorry is the proof of B. Use lean_goal to see what B is — likely something about the Core result being from a tryCatch catch handler.

### Step 3: Check hypotheses
Read 50 lines above each sorry to find available hypotheses. Look for:
- `herr` or `hstep_err` — evidence of error event
- `hcatch` — evidence of catch handler execution
- Type of the disjunction — what does `Or.inr` need?

### Step 4: Try closing tactics
```
lean_multi_attempt at each line:
["exact .inl ⟨_, rfl⟩", "simp", "assumption",
 "exact ⟨_, _, rfl⟩", "exact .inr ⟨_, _, rfl⟩",
 "exact herr", "exact hev", "exact ⟨_, rfl⟩",
 "obtain ⟨msg, hmsg⟩ := herr; exact ⟨msg, hmsg⟩",
 "exact hresult", "exact hcatch_result"]
```

### Step 5: If the Or.inr needs a witness about tryCatch catch
The pattern at all 3 locations follows the tryCatch error-catching path. The Or.inr branch likely needs a proof that the result came through the catch handler. Check if there's a hypothesis about the catch handler stepping.

## P1: Assess L6144 (non-consoleLog call)
Read 30 lines of context. Is this truly blocked or just hard?

## DO NOT ATTEMPT:
- CCStateAgree sorries — architecturally blocked
- convertExpr_state_mono refactor — too large
- Multi-step simulation redesign
- HeapInj staging (L8250)
- tryCatch finally (L8410)

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — Or.inr sorries L5270/L5414/L5701" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
