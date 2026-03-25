# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 26

### EmitSimRel sorries (9):
```
L7633  load                        sorry (memory readLE? bridge)
L7636  store                       sorry (memory writeLE? bridge)
L7639  store8                      sorry (memory write bridge)
L8080  call                        sorry (function table correspondence)
L8083  callIndirect                sorry (function table correspondence)
L8320  br                          sorry (label name→index resolution)
L8323  brIf                        sorry (label name→index resolution)
L8430  memoryGrow                  sorry (memory grow correspondence)
```
Plus emit_globals_init_valcorr (not grep'd as separate sorry — folded into another).

### LowerSimRel sorries (14):
```
L6037  init env                    sorry (ANF console binding → IR local)
L6157  let                         sorry (rhsCode ++ localSet ++ bodyCode)
L6165  seq                         sorry (aCode ++ drop ++ bCode)
L6169  if                          sorry (condCode ++ if_)
L6172  while                       sorry (loop structure)
L6175  throw                       sorry (error event)
L6178  tryCatch                    sorry (try-catch frame)
L6219  return (some)               sorry (needs argCode stuttering)
L6222  yield                       sorry (yield event)
L6225  await                       sorry (await event)
L6228  labeled                     sorry (labeled block)
L6231  break                       sorry (break event)
L6234  continue                    sorry (continue event)
```
Plus 3 `by sorry` in init at L8589/8604/8628 (need `LowerCodeCorr prog.main (irInitialState irmod).code`).

## TASK 0: Close L6037 (init env sorry)

At L6037, the goal is to prove that the initial ANF console binding corresponds to an IR local. The ANF initial state has `env = [("console", ...)]`. Use `lean_goal` at L6037 to see what's needed, then case-split on `hlookup`.

## TASK 1: Close EmitSimRel br/brIf (L8320, L8323)

Follow the proved block/return_ pattern. Need label name→depth-index bridge via `hlabel_content`. Use `lean_goal` at L8320 first.

## TASK 2: Close EmitSimRel load/store/store8 (L7633, L7636, L7639)

These need memory read/write bridges between IR and Wasm representations.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
