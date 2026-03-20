/-
  VerifiedJS.Tactics — Import and demonstrate all available automated tactics.

  Agents: import this file in your Proofs/ files to get access to all tactics:
    import VerifiedJS.Tactics
-/
import Canonical
import Duper

-- ===== CANONICAL =====
-- Canonical is a term synthesizer. It searches for proof terms.
-- Usage: `canonical <timeout_ms>` or `canonical <timeout_ms> [premise1, premise2]`
example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  canonical 5000

-- ===== DUPER =====
-- Duper is a first-order theorem prover. Give it relevant lemmas.
-- Usage: `duper [lemma1, lemma2, ...]`
example (p q : Prop) (hp : p) (hpq : p → q) : q := by
  duper [hp, hpq]

-- ===== GRIND =====
-- Congruence closure + case splitting. Try this FIRST on every goal.
example (n : Nat) (h : n = 3) : n + 1 = 4 := by
  grind

-- ===== AESOP =====
-- Rule-based automation. Good for goals involving constructors and type classes.
example (p : Prop) (hp : p) : p := by
  aesop

-- ===== OMEGA =====
-- Linear arithmetic on Nat/Int.
example (n : Nat) (h : n > 5) : n > 3 := by
  omega

-- ===== DECIDE =====
-- Decidable propositions (finite types only).
example : (2 + 2 : Nat) = 4 := by
  decide

-- ===== RECOMMENDED PROOF STRATEGY =====
-- For each sorry, try in this order:
-- 1. grind
-- 2. aesop
-- 3. canonical 10000
-- 4. duper [relevant_lemmas]
-- 5. omega (for arithmetic)
-- 6. simp [lemmas] then try above on remaining goals
-- 7. Break into subgoals with constructor/cases/intro, then try above on each
