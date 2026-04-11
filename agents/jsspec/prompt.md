# jsspec — CLOSE Or.inr SORRIES (L5270, L5414, L5701)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean AND Flat/ClosureConvert.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS — 2026-04-11T12:00
- CC: 15 sorries. Total: 48.
- Triage confirmed CCStateAgree targets architecturally blocked (5 total).
- Or.inr sorries at L5270, L5414, L5701 are the MOST LIKELY closable ones.
- **YOU JUST STARTED A RUN. FOCUS ON THESE 3 SORRIES AND NOTHING ELSE.**

## SORRY CLASSIFICATION (15 total)
- **Or.inr (TryCatch-init)**: 3 (L5270, L5414, L5701) — LIKELY CLOSABLE ← WORK ON THESE
- **CCStateAgree**: 5 (L5496, L5522, L8412, L8489, L8605) — ARCHITECTURALLY BLOCKED
- **TryCatch catch path**: 2 (L5413, L5700) — blocked by L8489
- **Multi-step**: 3 (L5049, L6352, L6363) — BLOCKED
- **Non-consoleLog call**: 1 (L6144) — ASSESS after P0
- **Unprovable**: 1 (L7003) — CANNOT BE PROVED

## P0: Close Or.inr sorries at L5270, L5414, L5701

These 3 sorries have the pattern:
```lean
exact ⟨Or.inr sorry, hfuncCorr_sub⟩
```

### Step 1: Read context
Read 30 lines around each sorry to see what the `Or.inr` needs to produce. The disjunction is likely about the result being either a lit value or something from tryCatch catch.

### Step 2: Use lean_goal
`lean_goal` at L5270, L5414, L5701. If LSP times out, read the surrounding context manually to infer the goal type.

### Step 3: Try tactics
```
lean_multi_attempt at each line:
["exact .inl ⟨_, rfl⟩", "simp", "exact trivial", "omega",
 "exact ⟨_, _, rfl⟩", "exact .inr ⟨_, _, rfl⟩",
 "assumption", "exact hev", "exact herr"]
```

### Step 4: If the goal needs a witness
Look at the hypotheses in context. The Or.inr branch likely needs something like "the result came from an error path (tryCatch catch handler)" — check if there's an `herr` or `hstep_err` hypothesis that provides this.

## P1: Assess L6144 (non-consoleLog call)
Read 30 lines of context. Is this truly blocked or just hard?

## DO NOT ATTEMPT:
- CCStateAgree sorries (L5496, L5522, L8412, L8489, L8605) — architecturally blocked
- convertExpr_state_mono refactor — too large
- Multi-step simulation redesign
- functionDef sorry (L8255) — blocked
- tryCatch finally (L8415) — blocked

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — Or.inr sorries L5270/L5414/L5701" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
