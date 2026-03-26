# wasmspec — Close EmitSimRel br/brIf (L9797, L9800)

You own Flat/*, ANF/*, Wasm/Syntax,Semantics,Typing,Numerics, Runtime/*.

## Current Wasm sorry count: 20 (in Semantics.lean)
- L6343-6420: 12 LowerSimRel (blocked by 1:N stepping — DO NOT touch)
- L9527, 9531: call underflow + success (blocked by hframes_one)
- L9541: callIndirect (blocked by hframes_one + table)
- L9797: br (this task)
- L9800: brIf (this task)
- L10244, 10259, 10283: init (blocked by LowerCodeCorr)

## TASK: Close br (L9797) and brIf (L9800)

### Architecture needed

For `br label`, the IR does:
1. `irFindLabel? ir.labels label` → returns `(ir_idx, irLbl)`
2. Uses `irLbl.isLoop` to decide: loop → jump to `irLbl.onBranch`, block → jump to `irLbl.onExit`

For Wasm `Instr.br idx`:
1. `resolveBranch? w.labels idx` → returns `(wLbl, remainingLabels)`
2. Uses `wLbl.isLoop` to decide loop/block branch target

### What you need to prove

**Step 1**: Add a helper lemma connecting IR label lookup to Wasm label resolution. Use `lean_goal` at L9797 to see what's available, then write:

```lean
private theorem ir_wasm_label_resolve
    (hlabels : ir.labels.length = w.labels.length)
    (hlabel_content : ∀ i, i < ir.labels.length →
      ∃ wl, w.labels[i]? = some wl ∧
        EmitCodeCorr ir.labels[i]!.onBranch wl.onBranch ∧
        EmitCodeCorr ir.labels[i]!.onExit wl.onExit ∧
        ir.labels[i]!.isLoop = wl.isLoop)
    (hfind : irFindLabel? ir.labels label = some (idx, irLbl))
    : ∃ wLbl wLabels',
        resolveBranch? w.labels idx = some (wLbl, wLabels') ∧
        EmitCodeCorr irLbl.onBranch wLbl.onBranch ∧
        EmitCodeCorr irLbl.onExit wLbl.onExit ∧
        irLbl.isLoop = wLbl.isLoop
```

**BUT FIRST**: Check whether `hlabels` and `hlabel_content` (or similar) actually exist in `EmitSimRel`. Use `lean_hover_info` on `EmitSimRel` to see its fields.

**Step 2**: If the fields don't exist yet, add them. Propagate to all construction sites (mechanical).

**Step 3**: Write the br case proof using the label resolution helper.

**Step 4**: brIf is br + a conditional check. Same pattern with an `if toBoolean cond` branch.

### If label infrastructure is too much

If adding label correspondence fields is too much work, at minimum:
1. Use `lean_goal` at L9797 and L9800 to document what's needed
2. Structure each sorry into subcases (like call was structured)
3. Leave targeted sorries with comments about what's blocked

### DON'T work on:
- LowerSimRel (12 sorries) — blocked by 1:N stepping
- call/callIndirect — blocked by multi-frame (`hframes_one`)
- init sorries — need LowerCodeCorr from lower proof

## Rules
- `bash scripts/lake_build_concise.sh` to build
- Log to agents/wasmspec/log.md
- Do NOT break the build
- CLOSE sorries, don't decompose them into more sorries
- Use `lean_goal` + `lean_multi_attempt` BEFORE editing
