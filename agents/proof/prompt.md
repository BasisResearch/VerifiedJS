# proof — CLOSE 20 SORRY TOKENS IN 60 SECONDS (then 15+ more)

## YOU ALREADY COMPLETED Phase 3 — GREAT WORK (5/6 CCState stepping cases done)
Let, if, seq, binary, getIndex stepping all DONE. Only while_ CCState (L2957) remains.

## STEP 1 (DO THIS IMMEDIATELY — ONE sed COMMAND): 20 sorry tokens gone

Run this EXACT command (copy-paste, do not modify):
```bash
sed -i "s/exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, sorry, sorry⟩/exact ⟨congrArg Prod.fst hconv', congrArg Prod.snd hconv'⟩, hAgreeIn, hAgreeOut⟩/g" VerifiedJS/Proofs/ClosureConvertCorrect.lean
```

This fixes 10 IDENTICAL lines (L2078, L2393, L2490, L2615, L2744, L2833, L2925, L3129, L3267, L3354).
`hAgreeIn` and `hAgreeOut` are ALWAYS in scope from the IH `obtain` on preceding lines.

**DO NOT BUILD YET** — do Step 2 first to batch changes.

## STEP 2: Fix value-base CCStateAgree sorries (single sorry after ⟨rfl, rfl⟩)

These have pattern: `⟨rfl, rfl⟩, sorry⟩`. The sorry needs `CCStateAgree st st` (trivial — same state).

**Simple var/this value cases** (L1825, L1848, L1876, L1899):
Replace `sorry⟩` with `⟨rfl, rfl⟩⟩`

**Assign/throw value cases** (L2026, L2867):
Replace `sorry⟩` with `by simp [Flat.convertExpr]; exact ⟨rfl, rfl⟩⟩`

**Return/yield/await/break/continue/labeled value-base** (L1932, L2994, L3017, L3043, L3073, L3155, L3181, L3211, L3298):
Use `lean_goal` to check what CCStateAgree looks like. Most should be `⟨rfl, rfl⟩⟩`.

**If/seq value-base** (L2115, L2137, L2245, L2339, L2779):
These are trickier — `sorry⟩` may need `by simp [Flat.convertExpr, CCStateAgree]` or specific state threading.
Use `lean_goal` at each, try `lean_multi_attempt` with: `["⟨rfl, rfl⟩", "by simp [Flat.convertExpr]; exact ⟨rfl, rfl⟩", "by simp [CCStateAgree, Flat.convertExpr]"]`

**NOW BUILD**: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`

## STEP 3: while_ CCState (L2957) — last Phase 3 case

Follow your own pattern from let/if/seq:
```lean
have hcond := convertExpr_state_determined cond scope envVar envMap st st_a' <agree>.1 <agree>.2
-- while_ duplicates: cond appears twice, body appears twice
-- Chain convertExpr_state_determined for each copy
```

Use `lean_goal` at L2957 to see what's needed.

## STEP 4: Harder expression cases (if time)

Remaining after Steps 1-3:
- call (L2556), newObj (L2557): need sub-expression stepping (jsspec has patches in .lake/_tmp_fix/)
- setProp (L2616), setIndex (L2686): need heap reasoning
- objectLit (L2834), arrayLit (L2835), functionDef (L2836): design issues (jsspec documented)
- tryCatch (L2926): error case analysis needed
- forIn/forOf (L1132/1133): stubs, skip
- Main suffices (L1797): skip

## DO NOT TOUCH: ANFConvertCorrect, LowerCorrect, Wasm/Semantics

## Build: `lake build VerifiedJS.Proofs.ClosureConvertCorrect`
## Log progress to agents/proof/log.md.
