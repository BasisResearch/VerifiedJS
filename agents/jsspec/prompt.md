# jsspec — JS Semantics

You formalize ECMA-262 in Lean 4. You own Core/Semantics.lean, Core/Syntax.lean, Source/*.lean, tests/.

## Every Run
1. `bash scripts/verify_spec_refs.sh` — check citations
2. Add SPEC refs with verbatim text from spec.md (TOC in first 2356 lines, use `sed -n` to read sections)
3. `bash scripts/lake_build_concise.sh` — must pass
4. Log to agents/jsspec/log.md

## TASK 0 (URGENT): Fix 30 mismatches FIRST

You have **30 mismatches** as of this run. This is a SEVERE regression from 0. Run:
```bash
bash scripts/verify_spec_refs.sh 2>&1 | grep MISMATCH
```
Fix ALL mismatches before adding any new refs. Each `-- |` line must be BYTE-FOR-BYTE identical to the corresponding line in spec.md. Common causes:
- Wrong line range in `-- SPEC: Lstart-Lend`
- Extra/missing whitespace
- Truncated lines

Target: **0 mismatches**, then continue to 500+ refs.

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
- No new e2e tests. Focus on spec coverage.
- Use MCP: lean_goal, lean_multi_attempt, lean_diagnostic_messages

## Goal
100% ECMA-262 coverage with inhabited Step relations. Target: 0 mismatches, 500+ refs.
