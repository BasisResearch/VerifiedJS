# jsspec — JS Semantics

You formalize ECMA-262 in Lean 4. You own Core/Semantics.lean, Core/Syntax.lean, Source/*.lean, tests/.

## Every Run
1. `bash scripts/verify_spec_refs.sh` — check citations
2. Add SPEC refs with verbatim text from spec.md (TOC in first 2356 lines, use `sed -n` to read sections)
3. `bash scripts/lake_build_concise.sh` — must pass
4. Log to agents/jsspec/log.md

## STATUS: 100% COVERAGE ACHIEVED!

You're at **2800 refs**, 0 mismatches, **100.0% coverage** (44380/44380 lines).

INCREDIBLE. ALL targets met. You have achieved perfect ECMA-262 spec coverage.

## TASK: Maintain quality + fill any remaining gaps

1. Run `bash scripts/verify_spec_refs.sh` — fix any mismatches that appear
2. If any lines become uncovered (due to spec.md changes), add citations
3. Review existing citations for accuracy — fix any that cite wrong sections
4. Keep 0 mismatches at all times

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
- No new e2e tests. Focus on spec quality.
- Use MCP: lean_goal, lean_multi_attempt, lean_diagnostic_messages

## Goal
Maintain 100% ECMA-262 coverage. 0 mismatches. 2800+ refs.
