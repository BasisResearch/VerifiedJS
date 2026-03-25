# wasmspec — Close Wasm/Semantics.lean sorries

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 23

### LowerSimRel sorries (12):
```
L6158  let                         sorry (rhsCode ++ localSet ++ bodyCode)
L6166  seq                         sorry (aCode ++ drop ++ bCode)
L6170  if                          sorry (condCode ++ if_)
L6173  while                       sorry (loop structure)
L6176  throw                       sorry (error event)
L6179  tryCatch                    sorry (try-catch frame)
L6220  return (some)               sorry (needs argCode stuttering)
L6223  yield                       sorry (yield event)
L6226  await                       sorry (await event)
L6229  labeled                     sorry (labeled block)
L6232  break                       sorry (break event)
L6235  continue                    sorry (continue event)
```

### EmitSimRel sorries (8):
```
L7634  load                        sorry (memory readLE? bridge)
L7637  store                       sorry (memory writeLE? bridge)
L7640  store8                      sorry (memory write bridge)
L8081  call                        sorry (function table correspondence)
L8084  callIndirect                sorry (function table correspondence)
L8321  br                          sorry (label name→index resolution)
L8324  brIf                        sorry (label name→index resolution)
L8431  memoryGrow                  sorry (memory grow correspondence)
```

### Init sorries (3):
```
L8590  ir_forward_sim init         by sorry (LowerCodeCorr for initial program)
L8605  ir_stutter_sim init         by sorry (LowerCodeCorr for initial program)
L8629  lower_behavioral_obs init   by sorry (LowerCodeCorr for initial program)
```

## TASK 0: Close LowerSimRel `let` case (L6158)

This is the most common pattern. ANF `let x = rhs in body` lowers to `rhsCode ++ [localSet x] ++ bodyCode`. The LowerSimRel invariant says the IR code is `LowerCodeCorr` of the ANF expression.

Use `lean_goal` at L6158 to see the exact goal. The proof pattern:
1. Unfold `anfStep?` for the `let` case
2. Show IR executes rhsCode (by LowerCodeCorr of rhs), then localSet, then continues with bodyCode
3. Construct new LowerSimRel with updated locals and remaining code

## TASK 1: Close EmitSimRel br/brIf (L8321, L8324)

You already aligned IR br/brIf to keep loop labels (last run). The remaining gap is the label name→depth-index bridge. Need invariant: `hlabel_content` now includes `EmitCodeCorr irLbl.onBranch wLbl.onBranch ∧ irLbl.isLoop = wLbl.isLoop`.

Use `lean_goal` at L8321. The proof needs: `irFindLabel? label labels = some (idx, lbl)` → Wasm `br idx` resolves to same target.

## TASK 2: Close EmitSimRel load/store (L7634, L7637, L7640)

Memory read/write bridges between IR and Wasm representations.

## URGENT TASK -1: Fix build-breaking indentation in Semantics.lean

The build is broken by a systematic indentation error in `VerifiedJS/Wasm/Semantics.lean`. In every `EmitSimRel` named-field block, the `hlabel_content` and `hframes_one` fields are indented 4 spaces too far after the `hhalt` field. This causes Lean to parse them as arguments to `hhalt_of_structural` instead of as separate structure fields.

**Fix**: Apply the pre-built patch at `/tmp/fix_semantics_indent.patch`:
```bash
cd /opt/verifiedjs && patch -p0 < /tmp/fix_semantics_indent.patch
```

If the patch file is gone, run this Python script instead:
```python
python3 -c "
with open('VerifiedJS/Wasm/Semantics.lean', 'r') as f:
    lines = f.readlines()
i = 0
while i < len(lines) - 2:
    line = lines[i]
    if 'hhalt := hhalt_of_structural' in line:
        next_line = lines[i + 1]
        if 'hlabel_content' in next_line:
            hhalt_indent = len(line) - len(line.lstrip())
            hlc_indent = len(next_line) - len(next_line.lstrip())
            if hlc_indent > hhalt_indent:
                spaces = ' ' * hhalt_indent
                lines[i + 1] = spaces + lines[i + 1].lstrip()
                lines[i + 2] = spaces + lines[i + 2].lstrip()
    i += 1
with open('VerifiedJS/Wasm/Semantics.lean', 'w') as f:
    f.writelines(lines)
"
```

This fixes 32 instances. Do this FIRST before any other work.

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
