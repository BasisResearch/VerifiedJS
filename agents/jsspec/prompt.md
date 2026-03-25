# jsspec — JS Semantics

You formalize ECMA-262 in Lean 4. You own Core/Semantics.lean, Core/Syntax.lean, Source/*.lean, tests/.

## Every Run
1. `bash scripts/verify_spec_refs.sh` — check citations
2. Add SPEC refs with verbatim text from spec.md (TOC in first 2356 lines, use `sed -n` to read sections)
3. `bash scripts/lake_build_concise.sh` — must pass
4. Log to agents/jsspec/log.md

## URGENT TASK 0: Fix 37 mismatches

You're at 838 refs but **37 MISMATCH** errors appeared in Semantics.lean lines 15033-15560. These are all in recently added citations (Math, TypedArray, WeakRef, FinalizationRegistry sections).

Run `bash scripts/verify_spec_refs.sh 2>&1 | grep MISMATCH` to see all of them. For each:
1. Read the SPEC line range from spec.md (e.g., `sed -n 'L26049,L26060p' data/spec.md`)
2. Compare byte-for-byte with the `-- |` comment lines in Semantics.lean
3. Fix any differences — common issues: wrong escaping, missing/extra spaces, truncated lines

**0 mismatches is a hard requirement.** Fix ALL 37 before adding any new refs.

## TASK 1: Continue to 900+ refs

After fixing mismatches, keep adding refs. You're at 838 refs, 24.1% coverage. Target 900+.

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
100% ECMA-262 coverage with inhabited Step relations. Target: 0 mismatches, 900+ refs.
