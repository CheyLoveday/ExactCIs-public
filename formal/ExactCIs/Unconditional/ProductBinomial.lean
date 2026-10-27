/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.FiniteProbability
import CarfSpine.ModelInstantiation

/-!
# Finite product-binomial probability

This module advances the finite product-mass part of `U-DESIGN-001` (#48).
The sample space uses natural counts bounded by the fixed group sizes. The
mass is exactly the product of the existing spine binomial formula, including
probabilities zero and one. No OR null parameterisation, Boschloo ordering,
structural-effect valuation, coverage result, or Python correspondence follows
from this construction alone.
-/

namespace ExactCIs.Unconditional.ProductBinomial

/-- Every possible pair of successes for the two fixed group sizes. -/
abbrev Outcome (n1 n0 : ℕ) := Fin (n1 + 1) × Fin (n0 + 1)

/-- The canonical table orientation is `(x, n1-x; y, n0-y)`. -/
def toTable {n1 n0 : ℕ} (outcome : Outcome n1 n0) : Table where
  a := outcome.1.val
  b := n1 - outcome.1.val
  c := outcome.2.val
  d := n0 - outcome.2.val

/-- Conversion to a table preserves the first fixed group size. -/
theorem toTable_n1 {n1 n0 : ℕ} (outcome : Outcome n1 n0) :
    (toTable outcome).n1 = n1 := by
  have bound := outcome.1.isLt
  simp only [toTable, Table.n1]
  omega

/-- Conversion to a table preserves the second fixed group size. -/
theorem toTable_n0 {n1 n0 : ℕ} (outcome : Outcome n1 n0) :
    (toTable outcome).n0 = n0 := by
  have bound := outcome.2.isLt
  simp only [toTable, Table.n0]
  omega

/-- One binomial mass sums to one by the finite binomial theorem. The identity
is algebraic and does not require a probability-domain assumption. -/
theorem binomial_sum (n : ℕ) (p : ℝ) :
    ∑ y : Fin (n + 1), Exactcis.Spine.binMass n y.val p = 1 := by
  rw [Fin.sum_univ_eq_sum_range (fun y => Exactcis.Spine.binMass n y p)]
  calc
    ∑ y ∈ Finset.range (n + 1), Exactcis.Spine.binMass n y p =
        (p + (1 - p)) ^ n := by
      rw [add_pow]
      apply Finset.sum_congr rfl
      intro y _
      unfold Exactcis.Spine.binMass
      ring
    _ = 1 := by simp

/-- The joint mass is the product of the two previously banked binomial
formulas. Both probability parameters remain explicit. -/
noncomputable def weight {n1 n0 : ℕ} (p1 p0 : ℝ)
    (outcome : Outcome n1 n0) : ℝ :=
  Exactcis.Spine.binMass n1 outcome.1.val p1 *
    Exactcis.Spine.binMass n0 outcome.2.val p0

/-- The sample-space sum of joint weights is one. -/
theorem weight_sum (n1 n0 : ℕ) (p1 p0 : ℝ) :
    ∑ outcome : Outcome n1 n0, weight p1 p0 outcome = 1 := by
  rw [Fintype.sum_prod_type]
  simp only [weight, ← Finset.mul_sum, binomial_sum, mul_one]

/-- Every weight is nonnegative on the closed probability square. -/
theorem weight_nonnegative {n1 n0 : ℕ} {p1 p0 : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Outcome n1 n0) : 0 ≤ weight p1 p0 outcome :=
  mul_nonneg (Exactcis.Spine.binMass_nonneg _ _ first.1 first.2)
    (Exactcis.Spine.binMass_nonneg _ _ second.1 second.2)

/-- The concrete normalized finite independent-binomial model. The arguments
include the probability-domain evidence needed for nonnegative mass. -/
noncomputable def mass (n1 n0 : ℕ) (p1 p0 : ℝ)
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1) :
    FiniteMass (Outcome n1 n0) where
  support := Finset.univ
  weight := weight p1 p0
  nonnegative := fun outcome _ => weight_nonnegative first second outcome
  normalizes := weight_sum n1 n0 p1 p0

/-- Target-facing normalization identity for the concrete finite mass. -/
theorem mass_sum (n1 n0 : ℕ) (p1 p0 : ℝ)
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1) :
    ∑ outcome ∈ (mass n1 n0 p1 p0 first second).support,
      (mass n1 n0 p1 p0 first second).weight outcome = 1 :=
  (mass n1 n0 p1 p0 first second).normalizes

/-- Explicit bridge to the existing banked mass expression. -/
theorem mass_weight_eq_spine {n1 n0 : ℕ} (p1 p0 : ℝ)
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Outcome n1 n0) :
    (mass n1 n0 p1 p0 first second).weight outcome =
      Exactcis.Spine.binMass n1 outcome.1.val p1 *
        Exactcis.Spine.binMass n0 outcome.2.val p0 := rfl

/-- At probability zero only zero successes have positive mass. -/
theorem binomial_at_zero (n y : ℕ) :
    Exactcis.Spine.binMass n y 0 = if y = 0 then 1 else 0 := by
  by_cases zero : y = 0
  · subst y
    simp [Exactcis.Spine.binMass]
  · simp [Exactcis.Spine.binMass, zero]

/-- At probability one only all successes have positive mass. -/
theorem binomial_at_one (n y : ℕ) (bounded : y ≤ n) :
    Exactcis.Spine.binMass n y 1 = if y = n then 1 else 0 := by
  by_cases full : y = n
  · subst y
    simp [Exactcis.Spine.binMass]
  · have difference : n - y ≠ 0 := by omega
    simp [Exactcis.Spine.binMass, full, difference]

/-- First-arm probability zero excludes outcomes with a first-arm success. -/
theorem weight_first_zero {n1 n0 : ℕ} (p0 : ℝ)
    (outcome : Outcome n1 n0) (unsupported : outcome.1.val ≠ 0) :
    weight 0 p0 outcome = 0 := by
  simp [weight, binomial_at_zero, unsupported]

/-- First-arm probability one excludes outcomes with a first-arm failure. -/
theorem weight_first_one {n1 n0 : ℕ} (p0 : ℝ)
    (outcome : Outcome n1 n0) (unsupported : outcome.1.val ≠ n1) :
    weight 1 p0 outcome = 0 := by
  have bounded : outcome.1.val ≤ n1 := Nat.le_of_lt_succ outcome.1.isLt
  simp [weight, binomial_at_one n1 outcome.1.val bounded, unsupported]

/-- Second-arm probability zero excludes outcomes with a second-arm success. -/
theorem weight_second_zero {n1 n0 : ℕ} (p1 : ℝ)
    (outcome : Outcome n1 n0) (unsupported : outcome.2.val ≠ 0) :
    weight p1 0 outcome = 0 := by
  simp [weight, binomial_at_zero, unsupported]

/-- Second-arm probability one excludes outcomes with a second-arm failure. -/
theorem weight_second_one {n1 n0 : ℕ} (p1 : ℝ)
    (outcome : Outcome n1 n0) (unsupported : outcome.2.val ≠ n0) :
    weight p1 1 outcome = 0 := by
  have bounded : outcome.2.val ≤ n0 := Nat.le_of_lt_succ outcome.2.isLt
  simp [weight, binomial_at_one n0 outcome.2.val bounded, unsupported]

end ExactCIs.Unconditional.ProductBinomial
