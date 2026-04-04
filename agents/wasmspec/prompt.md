# wasmspec — Prove normalizeExpr output satisfies NoNestedAbrupt

## Your break/continue analysis was EXCELLENT. Group G is PARKED.

## ABSOLUTE RULES
- **DO NOT** edit ClosureConvertCorrect.lean — jsspec owns it
- **DO NOT** run `lake build` anything large
- **DO NOT** use while/until/for loops, pgrep, sleep loops
- MEMORY: 7.7GB total, NO swap. ~4GB available.
- You CAN edit ANFConvertCorrect.lean

## NEW DIRECTION: Support the proof agent's NoNestedAbrupt approach

The proof agent is adding a `NoNestedAbrupt` predicate to Group D theorems. For the end-to-end proof to compose, we need to show normalizeExpr OUTPUT satisfies NoNestedAbrupt.

## YOUR TASK: Prove normalizeExpr_preserves_noNestedAbrupt

### Step 1: Check if proof agent has defined NoNestedAbrupt yet

Search ANFConvertCorrect.lean for `NoNestedAbrupt`. If not defined, define it yourself (coordinate — don't duplicate if it exists):

```lean
inductive NoNestedAbrupt : Flat.Expr → Prop where
  | lit : NoNestedAbrupt (.lit v)
  | var : NoNestedAbrupt (.var x)
  | this : NoNestedAbrupt .this
  | throw (harg : isTrivialChain arg = true ∨ arg.isValue) : NoNestedAbrupt (.throw arg)
  | return_ (harg : isTrivialChain arg = true ∨ arg.isValue) : NoNestedAbrupt (.return_ arg)
  | yield (harg : isTrivialChain arg = true ∨ arg.isValue) : NoNestedAbrupt (.yield arg)
  | await (harg : isTrivialChain arg = true ∨ arg.isValue) : NoNestedAbrupt (.await arg)
  | seq (ha : NoNestedAbrupt a) (hb : NoNestedAbrupt b) : NoNestedAbrupt (.seq a b)
  -- ... other constructors recursively require NoNestedAbrupt on sub-exprs
```

### Step 2: Prove normalizeExpr output satisfies NoNestedAbrupt

```lean
theorem normalizeExpr_noNestedAbrupt (e : Flat.Expr) (k : ANF.Trivial → ANF.ConvM ANF.Expr)
    (hk : ∀ t n, ∃ m e', (k t).run n = .ok (e', m) ∧ NoNestedAbrupt e')
    (n m : Nat) (e' : ANF.Expr)
    (hnorm : (ANF.normalizeExpr e k).run n = .ok (e', m)) :
    NoNestedAbrupt e' := by
  sorry -- induction on e
```

**Key insight**: `normalizeExpr` for `.throw e` calls `normalizeExpr e (fun t => pure (.throw t))`.
The continuation produces `.throw (.trivial t)` where `t` is a Trivial — by definition a trivial chain. So the argument IS a trivial chain, which is exactly what NoNestedAbrupt.throw requires.

Same pattern for return, yield, await. For compound cases: `bindComplex` wraps in `.seq`, recurse via IH.

### Step 3: Prove anfConvert output satisfies NoNestedAbrupt

This theorem bridges the gap from anfConvert (top-level) to the Group D theorems:

```lean
theorem anfConvert_noNestedAbrupt (e : Flat.Expr) (n m : Nat) (e' : ANF.Expr)
    (h : (ANF.anfConvert e).run n = .ok (e', m)) :
    NoNestedAbrupt e' := by
  -- anfConvert calls normalizeExpr with k = pure ∘ .trivial
  -- Apply normalizeExpr_noNestedAbrupt
  sorry
```

### Group G: PARKED
L8195 and L8248 blocked by Flat.step? dead code after break. Your analysis was correct. Will coordinate cross-cutting fix later.

## Build command
`lake build VerifiedJS.Proofs.ANFConvertCorrect`

## COORDINATE WITH PROOF AGENT
Both you and proof agent edit ANFConvertCorrect.lean. Check git status before editing. If proof agent has uncommitted changes that conflict, work around them. Use `lean_goal` to verify line numbers before editing.

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/wasmspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/wasmspec/log.md`
