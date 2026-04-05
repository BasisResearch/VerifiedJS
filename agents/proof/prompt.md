# proof — 28 sorries in ANF. CRITICAL: 8 are LSP-verified, just replace them!

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~4.4GB available (supervisor killed its build).
Use LSP tools only — no `lake build`.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L12630 and L13436 zones
- **YOU** own everything else
- DO NOT touch those lines

## PROGRESS: ANF 28 actual sorries + CC 11 = 39 total. BUILD IS FIXED.

## ===== PRIORITY 0: REINSTATE 8 VERIFIED PROOFS (L9066-9073) =====

**THIS IS YOUR #1 JOB.** The build is FIXED. You verified 8 proofs via LSP in a previous run but left them as sorry. NOW reinstate them.

The 8 sorry cases at their CURRENT line numbers:

| Line | Case | Steps_ctx_b | step?_ctx |
|------|------|-------------|-----------|
| L9066 | unary_arg h_arg | Steps_unary_ctx_b | step?_unary_ctx |
| L9067 | typeof_arg h_arg | Steps_typeof_ctx_b | step?_typeof_ctx |
| L9068 | deleteProp_obj h_obj | Steps_deleteProp_ctx_b | step?_deleteProp_ctx |
| L9069 | getProp_obj h_obj | Steps_getProp_ctx_b | step?_getProp_ctx |
| L9070 | assign_val h_val | Steps_assign_ctx_b | step?_assign_ctx |
| L9071 | getEnv_env h_env | Steps_getEnv_ctx_b | step?_getEnv_ctx |
| L9072 | makeClosure_env h_env | Steps_makeClosure_env_ctx_b | step?_makeClosure_env_ctx |
| L9073 | binary_lhs h_lhs | Steps_binary_lhs_ctx_b | step?_binary_lhs_ctx |

**KEY INSIGHTS YOU DISCOVERED:**
- Use `simp only [ANF.normalizeExpr] at hnorm` (NOT specific simp lemmas)
- `rename_i` order follows LSP goal context order, NOT constructor parameter order
- Each case follows the EXACT template of the proved cases above (e.g., throw_arg). Copy-paste and adapt.

**Use lean_goal at each line to see exact goal, then write the proof. Verify with lean_multi_attempt or lean_diagnostic_messages.**

## PRIORITY 1: After reinstating 8 proofs, work on GROUP B

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L10321 | compound HasThrowInHead |
| L10478 | compound HasReturnInHead |
| L10655 | compound HasAwaitInHead |
| L10813 | compound HasYieldInHead |

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L10472 | throw compound inner_val |
| L10649 | return compound inner_arg |
| L10807 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10869 | return (some val): compound |
| L10873 | yield (some val): compound |
| L10874 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10964 | While condition value case |
| L10976 | Condition-steps case |

### GROUP F: BLOCKED — do NOT work on these (5 sorries)
| L14277, L14295, L14298, L15612, L15665 |

### ALSO: L9074 catch-all needs more Steps_X_ctx_b helpers (jsspec building them)

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
