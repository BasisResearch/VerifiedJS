# proof — 22 sorries in your zone. CRITICAL: 8 are LSP-verified, just replace them!

## RULES
- Edit: ANFConvertCorrect.lean ONLY (and Flat/Semantics.lean for infrastructure)
- **DO NOT** run `lake build` — memory is tight. USE LSP ONLY.
- **DO NOT** edit ClosureConvertCorrect.lean (jsspec owns it)

## !! CRITICAL: DO NOT USE WHILE/UNTIL LOOPS !!
**NEVER use `while`, `until`, `sleep` in a loop, `pgrep`, or `do...done`.**

## MEMORY: 7.7GB total, NO swap. ~300MB available.
wasmspec lean worker is using 3.9GB. Use LSP tools only.

## CONCURRENCY: wasmspec also edits ANFConvertCorrect.lean
- wasmspec works on L12355 and L13161 zones
- **YOU** own everything else
- DO NOT touch those lines

## PROGRESS: ANF 30 + CC 12 = 42 total. BUILD IS FIXED (jsspec fixed 9 CC errors).

## ===== PRIORITY 0: REINSTATE 8 VERIFIED PROOFS (L8794-8801) =====

**THIS IS YOUR #1 JOB.** The build is now FIXED. You verified 8 proofs via LSP last run but reverted them. NOW reinstate them. Each follows the EXACT pattern of the proved cases above (throw_arg at L8710, await_arg at L8773, etc.).

The 8 sorry cases and their corresponding helpers:

| Line | Case | Steps_ctx_b | step?_ctx | normalizeExpr simp | VarFreeIn |
|------|------|-------------|-----------|-------------------|-----------|
| L8794 | unary_arg h_arg | Steps_unary_ctx_b | step?_unary_ctx | `simp only [ANF.normalizeExpr] at hnorm` | unary_arg |
| L8795 | typeof_arg h_arg | Steps_typeof_ctx_b | step?_typeof_ctx | `simp only [ANF.normalizeExpr] at hnorm` | typeof_arg |
| L8796 | deleteProp_obj h_obj | Steps_deleteProp_ctx_b | step?_deleteProp_ctx | `simp only [ANF.normalizeExpr] at hnorm` | deleteProp_obj |
| L8797 | getProp_obj h_obj | Steps_getProp_ctx_b | step?_getProp_ctx | `simp only [ANF.normalizeExpr] at hnorm` | getProp_obj |
| L8798 | assign_val h_val | Steps_assign_ctx_b | step?_assign_ctx | `simp only [ANF.normalizeExpr] at hnorm` | assign_val |
| L8799 | getEnv_env h_env | Steps_getEnv_ctx_b | step?_getEnv_ctx | `simp only [ANF.normalizeExpr] at hnorm` | getEnv_env |
| L8800 | makeClosure_env h_env | Steps_makeClosure_env_ctx_b | step?_makeClosure_env_ctx | `simp only [ANF.normalizeExpr] at hnorm` | makeClosure_env |
| L8801 | binary_lhs h_lhs | Steps_binary_lhs_ctx_b | step?_binary_lhs_ctx | `simp only [ANF.normalizeExpr] at hnorm` | binary_lhs |

**KEY INSIGHTS YOU DISCOVERED LAST RUN:**
- Use `simp only [ANF.normalizeExpr] at hnorm` (NOT specific simp lemmas — these constructors don't have @[simp] lemmas)
- `rename_i` order follows LSP goal context order, NOT constructor parameter order (e.g., for unary: `rename_i arg op` not `rename_i op arg`)
- Each case follows the EXACT template of throw_arg (L8710-8730). Copy-paste and adapt.

**Use lean_goal at each line to see exact goal, then write the proof. Verify with lean_multi_attempt or lean_diagnostic_messages.**

## PRIORITY 1: After reinstating 8 proofs, work on GROUP B

### GROUP B: compound HasXInHead catch-all (4 sorries)
| L10049 | compound HasThrowInHead |
| L10206 | compound HasReturnInHead |
| L10383 | compound HasAwaitInHead |
| L10541 | compound HasYieldInHead |

### GROUP C: compound inner_val/inner_arg (3 sorries)
| L10200 | throw compound inner_val |
| L10377 | return compound inner_arg |
| L10535 | yield compound inner_val |

### GROUP D: return/yield/compound (3 sorries)
| L10597 | return (some val): compound |
| L10601 | yield (some val): compound |
| L10602 | compound expressions catch-all |

### GROUP E: while (2 sorries)
| L10692 | While condition value case |
| L10704 | Condition-steps case |

### GROUP F: BLOCKED — do NOT work on these (7 sorries)
| L14002, L14020, L14023, L15106, L15117, L15337, L15390 |

## LOG YOUR WORK
**FIRST**: `echo "### $(date -Iseconds) Starting run" >> agents/proof/log.md`
**LAST**: `echo "### $(date -Iseconds) Run complete — [result]" >> agents/proof/log.md`
