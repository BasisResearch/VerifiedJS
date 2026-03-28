# proof — ANF IS YOUR ONLY PRIORITY

## STATUS: ANF has 14 sorries. 6+ DAYS UNTOUCHED. CC and Wasm can wait.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean` — 14 sorries in `anfConvert_step_star`.

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## ARCHITECTURE: What you need to know

The main theorem `anfConvert_step_star` (L1082) proves: for each ANF step, there exist matching Flat steps with equal observable traces. The `var` case (L1095-1133) is DONE (all goals close). The remaining 14 sorry cases are at L1096-1148.

Key hypotheses in every case:
- `hsa : sa.expr = ANF.Expr.<constructor> ...` — which ANF expr we're in
- `hstep_eq : ANF.step? sa = some (ev, sa')` — the ANF step
- `hnorm : (ANF.normalizeExpr sf.expr k).run n = .ok (sa.expr, m)` — normalizeExpr relates sf.expr to sa.expr
- `hk_triv` — continuation preserves trivials
- `hheap`, `henv`, `htrace` — heap/env/trace correspondence

## DESIGN BUG: break/continue (L1146, L1148) — SKIP THESE

ANF.step? for break produces `.silent`. Flat.step? for break produces `.error "break:..."`.
Since `observableTrace` only filters `.silent`, `observableTrace [.silent] = []` but `observableTrace [.error msg] = [.error msg]`.
These DO NOT MATCH. This is an unfixable design issue. Leave these as sorry.

## PRIORITY 1: labeled (L1144) — EASIEST CASE

ANF.step? for `.labeled label body` produces `(.silent, pushTrace {s with expr := body} .silent)`.
normalizeExpr (.labeled label body) k = `do { bodyExpr ← normalizeExpr body k; pure (.labeled label bodyExpr) }`.

Strategy:
```lean
| labeled label body =>
  obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
  simp only [] at hsa; subst hsa
  simp [ANF.step?, ANF.pushTrace] at hstep_eq
  obtain ⟨rfl, rfl⟩ := hstep_eq
  -- hnorm tells us: normalizeExpr sf.expr k produces .labeled label body_anf
  -- Need normalizeExpr inversion: sf.expr = .labeled label body_flat
  -- Flat.step? for .labeled steps to body with .silent
  -- Take 1 Flat step: sf → sf' with expr=body_flat, ev=.silent
  -- observableTrace [.silent] = [] = observableTrace [.silent] ✓
  -- New SimRel: sa'.expr = body, sf'.expr = body_flat, same k
  sorry
```

The key blocker: you need `normalizeExpr_labeled_inv` to invert hnorm. Check if jsspec wrote it in `.lake/_tmp_fix/`. If not, prove it inline:

```lean
-- From hnorm and hsa: normalizeExpr sf.expr k produces .labeled label body_anf
-- normalizeExpr ONLY produces .labeled from .labeled input (check the definition)
-- So sf.expr = .labeled label' body_flat for some body_flat
```

Use `lean_hover_info` on `ANF.normalizeExpr` at the labeled case (Convert.lean:114-116) to verify.

## PRIORITY 2: return none (L1152)

ANF.step? for `.return none` produces `(.silent, pushTrace {s with expr := .trivial .litUndefined} .silent)`.
normalizeExpr (.return none) k = `pure (.return none)`.

So from hnorm: `normalizeExpr sf.expr k` produces `.return none` → sf.expr = `.return none`.
Flat.step? for `.return none`: check what it does. If .silent, this is straightforward.
Take 1 Flat step, match events, build new SimRel with .trivial .litUndefined / .lit .undefined.

## PRIORITY 3: throw (L1148)

ANF.step? for `.throw arg` evaluates the trivial arg. Produces `.error "throw"` or `.error msg`.
normalizeExpr (.throw arg) k = `normalizeExpr arg (fun argTriv => pure (.throw argTriv))`.
This is harder — requires normalizeExpr reasoning.

## PRIORITY 4: var not-found (L1096) and var trace (L1115 — already closed!)

L1096 needs VarFreeIn inversion. May be closeable with `hewf` (ExprWellFormed) contradiction.

## WORKFLOW FOR EACH CASE

1. `lean_goal` at the sorry line to see exact goal state
2. `obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa; simp only [] at hsa; subst hsa`
3. `simp [ANF.step?, ANF.pushTrace] at hstep_eq` to learn ev and sa'
4. Analyze hnorm to determine sf.expr (normalizeExpr inversion)
5. Show Flat.Steps from sf to sf'
6. Construct new ANF_SimRel
7. Use `lean_multi_attempt` to try closing sub-goals

## DO NOT TOUCH CC or Wasm files.
## Build: `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Log progress to agents/proof/log.md
