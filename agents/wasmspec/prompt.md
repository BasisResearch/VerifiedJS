# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 27

### EmitSimRel sorries (9):
```
L6931  emit_globals_init_valcorr   sorry (irTypeToValType private in Emit.lean)
L7636  load                        sorry (memory readLE? bridge)
L7639  store                       sorry (memory writeLE? bridge)
L7642  store8                      sorry (memory write bridge)
L8083  call                        sorry (function table correspondence)
L8086  callIndirect                sorry (function table correspondence)
L8323  br                          sorry (label name→index resolution)
L8326  brIf                        sorry (label name→index resolution)
L8433  memoryGrow                  sorry (memory grow correspondence)
```

### LowerSimRel sorries (15):
```
L6025  init env                    sorry (ANF console binding → IR local)
L6145  let                         sorry (rhsCode ++ localSet ++ bodyCode)
L6153  seq                         sorry (aCode ++ drop ++ bCode)
L6157  if                          sorry (condCode ++ if_)
L6160  while                       sorry (loop structure)
L6163  throw                       sorry (error event)
L6166  tryCatch                    sorry (try-catch frame)
L6207  return (some)               sorry (needs argCode stuttering)
L6210  yield                       sorry (yield event)
L6213  await                       sorry (await event)
L6216  labeled                     sorry (labeled block)
L6219  break                       sorry (break event)
L6222  continue                    sorry (continue event)
```
Plus 3 `by sorry` in init at L8592/8607/8631.

## TASK 0: Close easy LowerSimRel event cases

**L6163 (throw)**, **L6210 (yield)**, **L6213 (await)**, **L6219 (break)**, **L6222 (continue)**: These all produce events and have short IR code sequences. Follow the pattern from the proved localGet case and the return none case you just closed.

## TASK 1: Close L6931 (emit_globals_init_valcorr)

Make `irTypeToValType` public in Wasm/Emit.lean (remove `private`), rebuild, then prove by cases on the type.

## TASK 2: Close br/brIf (L8323, L8326)

Follow the proved block/return_ pattern. Need label name→depth-index bridge via `hlabel_content`.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
