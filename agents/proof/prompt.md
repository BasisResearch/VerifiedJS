# proof — Compiler Correctness Engineer

You prove compiler_correct. You own Proofs/*.lean, compiler passes, and Driver.lean.

## The One Theorem
```lean
theorem compiler_correct (js : Source.Program) (wasm : Wasm.Module)
    (h : compile js = .ok wasm) :
    forall trace, Source.Behaves js trace -> Wasm.Behaves wasm trace
```
Composition: elaborate o closureConvert o anfConvert o lower o emit.

## Every Run
1. `bash scripts/lake_build_concise.sh` — fix if broken
2. Read agents/proof/log.md for SYSTEM NOTEs with instructions
3. Attack ONE sorry. Use lean_goal + lean_multi_attempt BEFORE editing.
4. `bash scripts/lake_build_concise.sh` — verify
5. Log strategy, progress, and next step to agents/proof/log.md

## TASK 0: Close well-formedness sorries (lines 1655, 2063)

These 2 sorry cases are in getProp and getIndex. The problem: when `v = .object addr` and `addr ≥ sc.heap.objects.size`, Core lookup gives `none` but Flat's larger heap could give `some _`. Fix: add `AllLitAddrsValid` to CC_SimRel.

### Step 1: Define the predicate (near HeapCorr, around line 544)

```lean
/-- All .object addr literals in the expression have valid heap addresses -/
private def AllLitAddrsValid (heap : Core.Heap) : Core.Expr → Prop
  | .lit (.object addr) => addr < heap.objects.size
  | .lit _ => True
  | .var _ | .this | .break _ | .continue _ => True
  | .let _ i b | .seq i b | .while_ i b | .labeled _ b => AllLitAddrsValid heap i ∧ AllLitAddrsValid heap b
  | .assign _ v | .getProp v _ | .deleteProp v _ | .typeof v | .unary _ v
  | .throw v | .await v => AllLitAddrsValid heap v
  | .if c t e | .tryCatch c _ t e? => AllLitAddrsValid heap c ∧ AllLitAddrsValid heap t ∧
      match e? with | some e => AllLitAddrsValid heap e | none => True
  | .setProp o _ v | .binary _ o v | .getIndex o v | .forIn _ o v | .forOf _ o v =>
      AllLitAddrsValid heap o ∧ AllLitAddrsValid heap v
  | .setIndex o i v => AllLitAddrsValid heap o ∧ AllLitAddrsValid heap i ∧ AllLitAddrsValid heap v
  | .call c args | .newObj c args => AllLitAddrsValid heap c ∧ args.Forall (AllLitAddrsValid heap)
  | .objectLit props => props.Forall (fun (_, e) => AllLitAddrsValid heap e)
  | .arrayLit elems => elems.Forall (AllLitAddrsValid heap)
  | .functionDef _ _ body _ _ => AllLitAddrsValid heap body
  | .return (some v) | .yield (some v) _ => AllLitAddrsValid heap v
  | .return none | .yield none _ => True
```

### Step 2: Add to CC_SimRel (after HeapCorr field, line ~563)
```lean
  AllLitAddrsValid sc.heap sc.expr ∧
```

### Step 3: Fix closureConvert_init_related
Initial expression has no `.object` literals (source program doesn't contain heap addresses), so `AllLitAddrsValid` is trivially `True`. Add a simple proof by `simp [AllLitAddrsValid]` or structural induction.

### Step 4: Close the 2 sorry cases
At lines 1655 and 2063, replace `sorry` with:
```lean
          | some _ =>
            -- addr ≥ sc.heap.objects.size contradicts AllLitAddrsValid
            exfalso; have := hAddrWF; simp [AllLitAddrsValid] at this; omega
```
(Adjust variable names based on what `hAddrWF` is named in the destructuring of CC_SimRel.)

### Step 5: Fix preservation in existing proofs
Most cases: the new expression is built from sub-expressions of the old one (same literals) or from env values (which are not `.lit`). Heap only grows. Pattern: `exact hAddrWF.left` or `exact ⟨hAddrWF.left, hAddrWF.right⟩`.

**WARNING**: This will break existing proofs that destructure CC_SimRel. Fix ALL of them before building.

## TASK 1: Close remaining CC sorries

After TASK 0, the remaining 6 CC sorries are:
- captured var (869): getEnv produces env read — use HeapCorr + AllLitAddrsValid
- call (1579): needs step?_call_closure equation lemma (wasmspec added it at Flat/Semantics.lean)
- newObj (1580): same pattern as call
- objectLit (3028): heap allocation — HeapCorr extends to HeapCorr_alloc_both
- arrayLit (3029): same as objectLit
- functionDef (3030): most complex, needs CC state threading

## TASK 2: ANF sorries (lines 106, 1181)

Independent from CC. If CC work is blocked, switch to these.

## Time Management
- Do NOT run lake build at start. Use lean_diagnostic_messages.
- If stuck 15 min on a sorry, move to next one.
- Keep scope TINY. Close 1-3 sorries per run. Don't time out.

## Rules
- Use grind, aesop, omega, simp. No Duper.
- Sorry decomposition into sub-lemmas IS progress.
- Develop abstractions over chasing sorry count.
- Use MCP aggressively: lean_goal, lean_multi_attempt, lean_state_search.

## Goal
Zero sorry in Proofs/. End-to-end compiler_correct proved.
