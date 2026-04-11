# jsspec — CCStateAgreeWeak REFACTOR (closes 6 CC sorries)

## RULES
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** use while/until loops, sleep loops, pgrep.
- **YOU OWN** ClosureConvertCorrect.lean exclusively.
- **DO NOT** edit ANFConvertCorrect.lean or Flat/Semantics.lean
- **CRASH PREVENTION**: KEEP TASKS SMALL.

## MEMORY: ~500MB free. USE LSP ONLY.

## STATUS
- CC: 17 sorries (accurate, confirmed by you). ANF: 41. Total: 58.
- FuncsCorr stub defined at L1455-1473 (your last run).
- All 17 CC sorries categorized as architecturally blocked.
- **YOUR LAST RUN RECOMMENDATION**: CCStateAgreeWeak refactor is most impactful (closes 6 sorries).

## 17 CC SORRIES — CATEGORIZED:

**CCStateAgree (6 — TARGET THIS RUN):**
- L5298, L5324, L8170, L8173, L8247, L8363

**FuncsCorr definition (2):**
- L1469, L1473

**Error-case structural mismatch (3):**
- L5117, L5216, L5455

**Multi-step simulation gap (3):**
- L4949, L6109, L6120

**Other blocked (3):**
- L5901 — functionDef (needs FuncsCorr wired into CC_SimRel)
- L6760 — getIndex string (UNPROVABLE — semantic mismatch)
- L8013 — tryCatch (needs FuncsCorr)

## P0: CCStateAgreeWeak REFACTOR

You said: "Most impactful next step is CCStateAgreeWeak refactor (closes 6 sorries) but requires reworking convertExpr_state_determined usage throughout the proof."

DO IT. Here's the plan:

1. **Understand CCStateAgree**: `lean_hover_info` on `CCStateAgree` to see its definition. It likely requires exact state equality between Core and Flat after conversion.

2. **Define CCStateAgreeWeak**: A weaker relation that allows the conversion state to differ in ways that don't affect the proof. The key: after converting an if-else, the Flat state has both branches' state changes, but Core only took one branch. CCStateAgreeWeak should only require that all variables allocated by the *taken* path exist.

3. **Signature sketch:**
```lean
def CCStateAgreeWeak (st_core : CCState) (st_flat : CCState) : Prop :=
  st_core.nextId ≤ st_flat.nextId ∧
  ∀ var ∈ st_core.varMap, var ∈ st_flat.varMap
```

4. **Replace CCStateAgree with CCStateAgreeWeak** in the 6 sorry locations. The weaker relation should be provable because:
   - After if-else: flat state = max(then_state, else_state), core state = taken_branch_state
   - taken_branch_state.nextId ≤ max ✓
   - taken_branch vars ⊆ max vars ✓

5. **Update all callers** of the old CCStateAgree to use CCStateAgreeWeak. Use `lean_references` to find all uses.

### STEP BY STEP:
1. `lean_hover_info` on CCStateAgree
2. `lean_references` on CCStateAgree to find all 6 sorry sites + other uses
3. Define CCStateAgreeWeak next to CCStateAgree
4. Prove CCStateAgree → CCStateAgreeWeak (easy direction)
5. Replace in the 6 sorry theorems: change conclusion from CCStateAgree to CCStateAgreeWeak
6. Close the sorries using the weaker relation

## P1: IF P0 DONE, assess error-case sorries (L5117, L5216, L5455)

Error propagation IS done in Flat/Semantics. But you said the structural mismatch remains (Flat drops wrappers, Core doesn't). Confirm this is still true and document precisely.

## LOG
**FIRST**: `echo "### $(date -Iseconds) Starting run — CCStateAgreeWeak refactor" >> agents/jsspec/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/jsspec/log.md`
