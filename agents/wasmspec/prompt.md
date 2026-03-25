# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 28

### EmitSimRel sorries (10):
```
L6887  emit_globals_init_valcorr   sorry (irTypeToValType private in Emit.lean)
L7592  load                        sorry (memory readLE? bridge)
L7595  store                       sorry (memory writeLE? bridge)
L7598  store8                      sorry (memory write bridge)
L8039  call                        sorry (function table correspondence)
L8042  callIndirect                sorry (function table correspondence)
L8279  br                          sorry (label name→index resolution)
L8282  brIf                        sorry (label name→index resolution)
L8389  memoryGrow                  sorry (memory grow correspondence)
```
Plus the empty-code label-pop at ~L7004 was CLOSED last run ✅.

### LowerSimRel sorries (15):
```
L6021  init env                    sorry (ANF console binding → IR local)
L6094  hhalt (localGet)            sorry (labels=[] ∧ frames≤1 invariant)
L6139  let                         sorry (rhsCode ++ localSet ++ bodyCode)
L6147  seq                         sorry (aCode ++ drop ++ bCode)
L6151  if                          sorry (condCode ++ if_)
L6154  while                       sorry (loop structure)
L6157  throw                       sorry (error event)
L6160  tryCatch                    sorry (try-catch frame)
L6163  return                      sorry (return event)
L6166  yield                       sorry (yield event)
L6169  await                       sorry (await event)
L6172  labeled                     sorry (labeled block)
L6175  break                       sorry (break event)
L6178  continue                    sorry (continue event)
```
Plus 3 `by sorry` in init at L8548/8563/8587.

## TASK 0 (EASIEST — DO FIRST): Close br and brIf (L8279, L8282)

These follow the EXACT pattern from `.block` (L8043-8084) and `.return_` (L8283-8385) which are already proved.

For **br** (L8279):
1. `have hc : EmitCodeCorr (IRInstr.br label :: rest) s2.code := hcode_ir ▸ hrel.hcode`
2. `rcases hc.br_inv with ⟨idx, rest_w, hcw, hrest⟩ | hf` (add `br_inv` lemma to EmitCodeCorr if needed)
3. Compute `irStep?` for br — it finds label, pops labels/code, continues with onExit
4. Compute `Wasm.step?` for `Wasm.Instr.br idx` — pops labels to idx
5. Use `hlabel_content` to connect IR label's onExit to Wasm label's continuation
6. Build post-step EmitSimRel

For **brIf** (L8282): Same pattern but with a condition check. Case split on stack top being truthy/falsy.

## TASK 1: Close easy LowerSimRel cases

**L6163 (return)**, **L6166 (yield)**, **L6169 (await)**: These produce events and have short IR code. Follow the pattern from the proved localGet case at L6033-6104.

**L6175 (break)**, **L6178 (continue)**: Similar — produce error events with label info.

## TASK 2: Close L6887 (emit_globals_init_valcorr)

Make `irTypeToValType` public in Wasm/Emit.lean (remove `private`), then rebuild, then `cases t <;> simp [irTypeToValType]`.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
