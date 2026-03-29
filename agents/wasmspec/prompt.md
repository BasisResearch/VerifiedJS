# wasmspec — APPLY BREAK/CONTINUE FIX FIRST, THEN MULTI-STEP

## STEP 0: Kill stuck processes

```bash
ps aux | grep -E "lean" | grep wasmspec | grep -v grep
```
Kill ANY lean worker running for >5 minutes:
```bash
kill -9 <PID>
```

## YOUR FILE: `VerifiedJS/Wasm/Semantics.lean` (you are the ONLY agent who can write it)

## Current sorry count: 18 (grep -c), 16 actual step_sim + 2 call/callIndirect

## PHASE 1: Apply break/continue fix (-2 sorries, ~30 min)

jsspec analyzed all 12 step_sim sorries. break (L6876) and continue (L6879) reduce to `⊢ False`
because `br` with empty label stack is impossible. The fix:

### Step 1: Add field to LowerSimRel (after `hframes_one` field, ~L6646)
```lean
  /- break/continue lower to [br target] which needs a matching label.
     With empty labels, br traps and traces diverge. -/
  hcode_no_br : ∀ target, ir.code = [IRInstr.br target] →
    ∃ idx lbl, irFindLabel? ir.labels target = some (idx, lbl)
```

### Step 2: Prove hcode_no_br at EVERY LowerSimRel construction site
At each `exact { ... }` or `⟨ ... ⟩` that builds a LowerSimRel, add:
```lean
  hcode_no_br := by intro _ h; simp at h
```
This works because successor code is never `[.br target]` — it's `[]` or `[.call _]` etc.

### Step 3: Replace break sorry (L6876)
```lean
  have hc := hrel.hcode; rw [hexpr] at hc
  obtain ⟨target, hcode_eq⟩ := hc.break_inv
  exfalso
  have ⟨idx, lbl, hfind⟩ := hrel.hcode_no_br target hcode_eq
  rw [hrel.hlabels_empty] at hfind
  simp [irFindLabel?, irFindLabel?.go] at hfind
```

### Step 4: Replace continue sorry (L6879) — identical proof

### Step 5: `lake build VerifiedJS.Wasm.Semantics`

## PHASE 2: Remaining 10 step_sim sorries (L6798-L6873)

jsspec's analysis: all 10 remaining cases need multi-step IR execution or label tracking.

**Start with simplest multi-step cases:**

### L6864: return (some t) — 2 IR steps
- IR code = `argCode ++ [return_]`
- Step 1: execute argCode (evaluate trivial arg)
- Step 2: return_

### L6867: yield — 3+ steps
### L6870: await — 2+ steps

## PHASE 3: L10857-L10919 (call/callIndirect) — SKIP unless Phase 1-2 done

## WORKFLOW
1. `lean_goal` BEFORE every sorry attempt
2. `lean_multi_attempt` to test tactics
3. `lake build VerifiedJS.Wasm.Semantics` after EVERY edit
4. If build breaks: `git checkout VerifiedJS/Wasm/Semantics.lean` within 2 minutes
5. LOG every 15 min to agents/wasmspec/log.md

## FILES: `VerifiedJS/Wasm/Semantics.lean` (rw)
## DO NOT EDIT: `VerifiedJS/Proofs/*.lean`
