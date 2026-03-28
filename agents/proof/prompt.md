# proof — INSTALL LEMMAS THEN CLOSE ANF CASES

## STATUS: ANF has 13 sorries. 7 DAYS UNTOUCHED. THIS IS EMERGENCY PRIORITY.

File: `VerifiedJS/Proofs/ANFConvertCorrect.lean` — 13 sorries in `anfConvert_step_star`.
File: `VerifiedJS/ANF/Convert.lean` — YOU OWN THIS FILE. Install lemmas below.

## BUILD STATUS: PASSES (sorry warnings only). DO NOT BREAK IT.

## STEP 0: INSTALL SIMP LEMMAS INTO Convert.lean (5 MINUTES)

Open `VerifiedJS/ANF/Convert.lean`. Before `end VerifiedJS.ANF` (currently L227), add these PROVEN lemmas:

```lean
@[simp] theorem normalizeExpr_return_none (k : Trivial → ConvM Expr) :
    normalizeExpr (.return none) k = pure (.return none) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_return_some (v : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.return (some v)) k =
      normalizeExpr v (fun t => pure (.return (some t))) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_throw (arg : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.throw arg) k =
      normalizeExpr arg (fun argTriv => pure (.throw argTriv)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_var (name : String) (k : Trivial → ConvM Expr) :
    normalizeExpr (.var name) k = k (.var name) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_this (k : Trivial → ConvM Expr) :
    normalizeExpr .this k = k (.var "this") := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_await (arg : Flat.Expr) (k : Trivial → ConvM Expr) :
    normalizeExpr (.await arg) k =
      normalizeExpr arg (fun argTriv => pure (.await argTriv)) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_yield_none (delegate : Bool) (k : Trivial → ConvM Expr) :
    normalizeExpr (.yield none delegate) k = pure (.yield none delegate) := by
  simp [normalizeExpr]

@[simp] theorem normalizeExpr_yield_some (v : Flat.Expr) (delegate : Bool) (k : Trivial → ConvM Expr) :
    normalizeExpr (.yield (some v) delegate) k =
      normalizeExpr v (fun t => pure (.yield (some t) delegate)) := by
  simp [normalizeExpr]

theorem normalizeExpr_return_none_run (k : Trivial → ConvM Expr) (n : Nat) :
    StateT.run (normalizeExpr (.return none) k) n = .ok (.return none, n) := by
  simp only [normalizeExpr]; rfl

theorem normalizeExpr_break_run (label : Option Flat.LabelName)
    (k : Trivial → ConvM Expr) (n : Nat) :
    StateT.run (normalizeExpr (.break label) k) n = .ok (.break label, n) := by
  simp only [normalizeExpr]; rfl

theorem normalizeExpr_continue_run (label : Option Flat.LabelName)
    (k : Trivial → ConvM Expr) (n : Nat) :
    StateT.run (normalizeExpr (.continue label) k) n = .ok (.continue label, n) := by
  simp only [normalizeExpr]; rfl
```

After installing: `lake build VerifiedJS.ANF.Convert` to verify. Then proceed to cases.

## CASE 1: labeled (L1158) — EASIEST, DO FIRST

ANF.step? for `.labeled _ body` → `(.silent, pushTrace {s with expr := body} .silent)`.
Flat.step? for `.labeled _ body` → `(.silent, pushTrace {s with expr := body} .silent)`.
normalizeExpr (.labeled label body) k = `do { bodyExpr ← normalizeExpr body k; pure (.labeled label bodyExpr) }`.

Both sides produce `.silent` and step into the body. The SimRel just shifts from `.labeled` to body.

```lean
  | labeled label body =>
    obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa
    simp only [] at hsa; subst hsa
    simp [ANF.step?, ANF.pushTrace] at hstep_eq
    obtain ⟨rfl, rfl⟩ := hstep_eq
    -- hnorm: normalizeExpr sf.expr k n = .ok (.labeled label body, m)
    -- From normalizeExpr_labeled: sf.expr must be .labeled label body_flat for some body_flat
    -- Flat.step? for .labeled: steps to body_flat with .silent
    -- Take 1 Flat step, events match: [.silent] ~ [.silent]
    -- New SimRel: sa'.expr = body, sf'.expr = body_flat, same k
    -- The key: from hnorm, we need to extract body_flat and show normalizeExpr body_flat k = .ok (body, m)
    sorry
```

Strategy: use `lean_goal` at the sorry to see the exact goal. Then:
1. From `hnorm` and `normalizeExpr_labeled`, sf.expr must start with `.labeled`. Case split or use `have` to extract this.
2. Show Flat takes 1 step (`.silent`).
3. Build new SimRel with the SAME `k`, matching body expressions.

## CASE 2: return none (L1152)

ANF.step? for `.return none` → `(.silent, pushTrace {s with expr := .trivial .litUndefined} .silent)`.
Flat.step? for `.return none` → `(.error "return:undefined", pushTrace {s with expr := .lit .undefined} (.error "return:undefined"))`.

**CRITICAL**: Events DON'T match directly! ANF produces `.silent`, Flat produces `.error "return:undefined"`.
observableTrace [.silent] = [] and observableTrace [.error "return:undefined"] = [.error "return:undefined"].
These are NOT equal. This case may be BLOCKED like break/continue.

Check `observableTrace` definition first. If `.error` events starting with "return:" are also filtered, it works. Otherwise this case is blocked.

## CASE 3: yield none (L1154) — LIKELY EASY

ANF.step? for `.yield none _` → `(.silent, pushTrace {s with expr := .trivial .litUndefined} .silent)`.
Flat.step? for `.yield none _` → `(.silent, pushTrace {s with expr := .lit .undefined} .silent)`.

Both produce `.silent`. Similar to labeled.

From hnorm: `normalizeExpr sf.expr k n = .ok (.yield none delegate, m)` and `normalizeExpr_yield_none` → sf.expr = `.yield none delegate`.

## CASE 4: await (L1156) — MEDIUM

ANF.step? for `.await arg` with evalTrivial:
- `.ok v` → `(.silent, pushTrace {s with expr := .trivial (trivialOfValue v)} .silent)`.
- `.error msg` → `(.error msg, pushTrace {s with expr := .trivial .litUndefined} (.error msg))`.

Flat.step? for `.await arg`:
- `exprValue? arg = some v` → `(.silent, pushTrace {s with expr := .lit v} .silent)`.
- else → step inner `arg`.

The `hnorm` tells us sf.expr is transformed through normalizeExpr(.await arg). Need to relate evalTrivial on ANF side to exprValue? on Flat side.

## CASES TO SKIP: break (L1160), continue (L1162) — DESIGN BUG, LEAVE AS SORRY

## WORKFLOW FOR EACH CASE
1. `lean_goal` at the sorry line to see exact goal state
2. `obtain ⟨sa_expr, sa_env, sa_heap, sa_trace⟩ := sa; simp only [] at hsa; subst hsa`
3. `simp [ANF.step?, ANF.pushTrace] at hstep_eq` to learn ev and sa'
4. Analyze hnorm to determine sf.expr (using the new simp lemmas)
5. Show Flat.Steps from sf to sf'
6. Construct new ANF_SimRel
7. Use `lean_multi_attempt` to try closing sub-goals

## DO NOT TOUCH CC or Wasm files.
## Build: `lake build VerifiedJS.ANF.Convert` then `lake build VerifiedJS.Proofs.ANFConvertCorrect`
## Log progress to agents/proof/log.md
