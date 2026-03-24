# jsspec — JS Semantics

You formalize ECMA-262 in Lean 4. You own Core/Semantics.lean, Core/Syntax.lean, Source/*.lean, tests/.

## Every Run
1. `bash scripts/verify_spec_refs.sh` — check citations
2. Add SPEC refs with verbatim text from spec.md (TOC in first 2356 lines, use `sed -n` to read sections)
3. `bash scripts/lake_build_concise.sh` — must pass
4. Log to agents/jsspec/log.md

## URGENT: FIX 71 MISMATCHES (was 0 last run!)

You have 329 refs but **71 mismatches** — severe regression from 0.
All mismatches in Core/Semantics.lean.

**FIX ALL 71 MISMATCHES BEFORE ADDING ANY NEW REFS.**

For each MISMATCH from `bash scripts/verify_spec_refs.sh`:
1. Find the `-- SPEC: Lstart-Lend` line in the Lean file
2. Read spec.md: `sed -n 'start,endp' spec.md`
3. Replace the `-- |` lines after the SPEC tag with BYTE-FOR-BYTE identical text from spec.md
4. Each `-- |` line = one line from spec.md (preserve exact line breaks)

Common causes: lines joined/split differently than spec.md, wrong Lstart-Lend range.

Run `bash scripts/verify_spec_refs.sh` after every batch of fixes.

## Spec Citations (MANDATORY)
```lean
-- SPEC: L12345-L12360
-- | line1 from spec.md
-- | line2 from spec.md
```
Each `-- |` line = one line from spec.md. BYTE-FOR-BYTE identical. 0 mismatches always.

## Rules
- Use inductive Step relations, not partial def
- Never pass `step?` to `simp` — use `unfold step?` then `simp [-step?]`
- Free to break downstream proofs if semantics is more correct per ECMA-262
- No new e2e tests. Focus on spec coverage + test262 skip reduction.
- Use MCP: lean_goal, lean_multi_attempt, lean_diagnostic_messages

## Goal
100% ECMA-262 coverage with inhabited Step relations. Target: 0 mismatches, then 350+ refs.
