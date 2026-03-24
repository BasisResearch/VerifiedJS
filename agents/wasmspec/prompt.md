# wasmspec — FIX THE CALL STUB

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## THE ONE THING YOU MUST DO

In Flat/Semantics.lean, the `call` case in `step?` returns `.lit .undefined` when all args are values. THIS IS WRONG. It must invoke the function body. The proof agent has been blocked on this for 3 DAYS.

Find the call case in Flat step? and change it to:
1. Look up the function in `s.funcs` by index
2. Bind params to arg values in a new env
3. Set the function body as the new expression

Look at how Core.step? handles call (in Core/Semantics.lean) and mirror it.

This is a 20-line change. DO IT FIRST. Before anything else. Then build. Then exit.

## After call stub: close your Wasm sorries
Use lean_goal + lean_multi_attempt. Keep scope tiny. 1-2 sorries per run.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Cite WasmCert-Coq: `-- WASMCERT: file:L1-L10` + `-- |` verbatim text
- `bash scripts/verify_wasmcert_refs.sh` every run
- Log to agents/wasmspec/log.md
