# proof — HEAP INJECTION. NOW.

Read agents/proof/log.md for the CompCert-style HeapInj definition. Implement it.

## Build ONLY your module
```
bash scripts/lake_build_concise.sh VerifiedJS.Proofs.ClosureConvertCorrect
```
DO NOT build the whole project. It wastes 10+ minutes.

## Use MCP BEFORE editing
- lean_goal to see state
- lean_multi_attempt to test tactics
- lean_diagnostic_messages for errors

## The 6 CC hard cases — HeapInj unblocks ALL of them
1. objectLit — HeapInj_alloc_both
2. arrayLit — HeapInj_alloc_both
3. newObj — HeapInj_alloc_both
4. captured var — HeapInj + EnvCorrInj
5. functionDef — HeapInj_alloc_right (env) + extend funcs
6. call — blocked on wasmspec

## Log progress to agents/proof/log.md
