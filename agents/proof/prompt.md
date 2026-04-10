# proof — FIX OOM + CLOSE COMPOUND SORRIES

## RULES
- Edit: ANFConvertCorrect.lean ONLY (except L17760-17813 which wasmspec owns)
- **DO NOT** run `lake build` — USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)
- **DO NOT** use while/until loops, sleep loops, pgrep

## MEMORY: 7.7GB total, NO swap. ~500MB free. USE LSP ONLY.

## CRITICAL: ANF BUILD IS OOM-KILLED (exit 137)

ANFConvertCorrect.lean is 18,698 lines. `lake build` runs out of memory and gets SIGKILL'd. The "missing alternatives" errors at L14390 are SPURIOUS — all alternatives exist, Lean just dies before reaching them.

### IMMEDIATE ACTION: Split the file or reduce proof size

The if_branch section (L13148-L15590, ~2400 lines) is the largest proof block and is architecturally blocked (K-mismatch). Consider:

1. **Option A**: Extract the if_branch proof into a separate file (ANFConvertCorrect_IfBranch.lean). This reduces memory pressure.
2. **Option B**: Collapse the proven trivialChain fuel induction (L14516-L14757, ~240 lines of duplicated lit/var/this/seq cases) into a helper lemma.
3. **Option C**: Replace the entire if_branch `| succ d ih =>` body with a single sorry, since it's blocked by K-mismatch anyway. This trades 24 sorries for 1 but lets the file compile.

**RECOMMENDED**: Option C first (unblocks build), then work on compound sorries.

## P0: MAKE THE FILE COMPILE (sorry-collapse if_branch)

At L14388-L15590, the `| succ d ih =>` case of the if_branch induction has ~30 alternatives, most sorry'd. Replace the entire body with:
```lean
  | succ d ih =>
    intro e hd hif env heap trace funcs cs K n m cond then_ else_ v hnorm hewf heval hbool
    sorry -- if_branch: architecturally blocked by K-mismatch (see PROOF_BLOCKERS.md blocker R)
```

This collapses ~24 sorries into 1, reducing file complexity and letting Lean compile within memory.

**THEN** also check if any other large proof blocks can be similarly collapsed. Target: get the file under 16K lines.

## P1: CLOSE COMPOUND SORRIES (after build compiles)

These 7 compound sorries are unblocked by Flat.step? error propagation:
- L11772 — throw compound
- L11923 — return compound inner_val
- L11929 — compound HasReturnInHead
- L12106 — compound HasAwaitInHead
- L12264 — compound HasYieldInHead

Key lemmas: `step?_seq_error` (~L2271), `step?_let_init_error` (~L2283)

## P2: anfConvert_step_star (L17372) — CRITICAL

This is the ENTIRE ANF correctness theorem. It has been sorry'd for 5+ DAYS. Even if the individual case sorries can't be closed yet, verify:
1. The case structure is complete (all Flat.Expr constructors handled)
2. Per-constructor sorries exist for every case
3. No monolithic sorry covering multiple cases

## CONCURRENCY
- wasmspec works on L17760, L17813 (break/continue compound)
- jsspec works on ClosureConvertCorrect.lean
- **YOU** own ALL of ANFConvertCorrect.lean EXCEPT L17760-17813

## WORKFLOW
1. `echo "### $(date -Iseconds) Starting run — fixing OOM build" >> agents/proof/log.md`
2. Collapse if_branch `| succ d ih =>` to single sorry
3. Verify file size dropped; attempt LSP check
4. If build passes, work on P1 compound sorries
5. `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`

## NON-NEGOTIABLE: The file MUST compile. If it doesn't compile, nothing else matters.
