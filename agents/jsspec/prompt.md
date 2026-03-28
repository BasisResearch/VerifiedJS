# jsspec — WRITE CC EASY WINS + SUPPORT PROOF AGENT

## STATUS: Staging lemmas delivered. Proof agent will integrate them. Focus on CC now.

## CURRENT SORRY COUNT: ANF=13, CC=18, Wasm=20, Lower=1 → 52 total

## PRIORITY 0: CLOSE EASY CC SORRIES

File: `VerifiedJS/Proofs/ClosureConvertCorrect.lean`

The CC file has 18 actual sorries. Some are easy no-confusion/exfalso cases. Focus on these:

### L2866 (objectLit), L2867 (arrayLit):
These are stub implementations (objectLit/arrayLit not fully implemented in closure convert).
Use `lean_goal` at these lines to check the goal. If the closureConvert for these produces `.lit .undefined` (stub), then the simulation is trivially:
```lean
  | objectLit props =>
    -- closureConvert produces stub → step? on stub = step? on source
    sorry -- check goal first
```

### L2868 (functionDef):
Check with `lean_goal`. If it's a design issue, leave it.

### L2588 (call), L2589 (newObj):
These are complex (need multi-step simulation). SKIP.

### L2595, L2654, L2724 (value sub-cases with heap reasoning):
SKIP — need heap invariant.

### L2648 (setProp), L2718 (setIndex):
Check if the non-value case (expression stepping) is provable. The pattern: if the sub-expression steps, the overall expression steps the same way.

### L2147, L2169 (CCState threading in if/while):
These are about CCState mismatches when the conversion creates different states for then/else branches. SKIP — need CCState invariant refactor.

### L2989 (while_ CCState):
SKIP — same CCState issue.

## PRIORITY 1: WRITE TEMPLATE FOR PROOF AGENT'S EXFALSO CASES

Write into `.lake/_tmp_fix/VerifiedJS/Proofs/anf_exfalso_template.lean` a complete template file showing the expansion of `| _ => sorry` at L1563 with all the exfalso cases. The proof agent can copy this directly.

Include:
1. All trivial cases (var, lit, this) with complete proofs
2. All bindComplex cases with complete proofs
3. Control flow cases (break, continue, return-none, yield-none, throw, await)
4. Leave compound cases (let, seq, if) as sorry with comments

## PRIORITY 2: Check if forIn/forOf sorries (L1132, L1133) can be closed

These are permanently excluded (`forIn => sorry`, `forOf => sorry`). The `supported` predicate should exclude them. Check if there's a `supported` hypothesis available. If so:
```lean
  | forIn => exfalso; simp [Flat.Expr.supported] at h_supported
```

## DO NOT edit: ANFConvertCorrect.lean, EmitCorrect.lean, EndToEnd.lean, LowerCorrect.lean
## YOU CAN edit: .lake/_tmp_fix/**, VerifiedJS/Core/*, VerifiedJS/Flat/*, ClosureConvertCorrect.lean
## Log to agents/jsspec/log.md
