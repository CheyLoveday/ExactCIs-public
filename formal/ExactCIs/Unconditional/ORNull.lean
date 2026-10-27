/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ProductBinomial

/-!
# Finite positive odds-ratio null model

The real finite-effect model has `psi > 0` and nuisance `q ∈ [0,1]`.
This module connects its exact product-binomial mass to U0's OR-MASS formula,
including both nuisance endpoints. It does not define the structural effect
values zero/infinity, Boschloo masks, Bernstein coefficients, or coverage.
-/

namespace ExactCIs.Unconditional.ORNull

open ProductBinomial

/-- Denominator of the finite odds-ratio probability link. -/
def denominator (psi q : ℝ) : ℝ := 1 - q + psi * q

/-- Transformed first-arm probability; the second-arm probability is `q`. -/
noncomputable def p1 (psi q : ℝ) : ℝ := psi * q / denominator psi q

/-- Interior compactified coordinate for a finite positive effect. -/
noncomputable def compact (psi : ℝ) : ℝ := psi / (1 + psi)

/-- The two denominator forms in U0 are identical. -/
theorem denominator_alt (psi q : ℝ) :
    denominator psi q = 1 + (psi - 1) * q := by
  unfold denominator
  ring

/-- Every finite positive effect maps strictly inside the compact domain. -/
theorem compact_mem_Ioo {psi : ℝ} (positive : 0 < psi) :
    compact psi ∈ Set.Ioo (0 : ℝ) 1 := by
  have sum_positive : 0 < 1 + psi := by linarith
  constructor
  · exact div_pos positive sum_positive
  · exact (div_lt_one sum_positive).mpr (by linarith)

/-- Exact bridge to the denominator used by the existing interior model. -/
theorem denominator_eq_compact {psi : ℝ} (positive : 0 < psi) (q : ℝ) :
    denominator psi q = (1 + psi) * Exactcis.Spine.denom (compact psi) q := by
  have nonzero : 1 + psi ≠ 0 := ne_of_gt (by linarith : 0 < 1 + psi)
  unfold denominator compact Exactcis.Spine.denom
  field_simp [nonzero]
  ring

/-- The finite-effect denominator is positive on the entire closed nuisance
interval, by transport of the existing interior-stratum positivity theorem. -/
theorem denominator_pos {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : 0 < denominator psi q := by
  have interior := compact_mem_Ioo positive
  rw [denominator_eq_compact positive q]
  exact mul_pos (by linarith)
    (Exactcis.Spine.denom_pos interior.1 interior.2 nuisance.1 nuisance.2)

/-- Both probability links are the same on their common mathematical domain. -/
theorem p1_eq_compact {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    p1 psi q = Exactcis.Spine.p1 (compact psi) q := by
  have interior := compact_mem_Ioo positive
  have compact_nonzero :=
    (Exactcis.Spine.denom_pos interior.1 interior.2 nuisance.1 nuisance.2).ne'
  have sum_nonzero : 1 + psi ≠ 0 := ne_of_gt (by linarith : 0 < 1 + psi)
  rw [p1, denominator_eq_compact positive q, Exactcis.Spine.p1]
  change psi * q / ((1 + psi) * Exactcis.Spine.denom (compact psi) q) =
    (psi / (1 + psi)) * q / Exactcis.Spine.denom (compact psi) q
  field_simp [compact_nonzero, sum_nonzero]

/-- The transformed probability remains in the closed unit interval. -/
theorem p1_mem_Icc {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : p1 psi q ∈ Set.Icc (0 : ℝ) 1 := by
  rw [p1_eq_compact positive nuisance]
  have interior := compact_mem_Ioo positive
  exact Exactcis.Spine.p1_mem_Icc interior.1 interior.2 nuisance.1 nuisance.2

/-- The first-arm failure probability has the same positive denominator. -/
theorem one_sub_p1 {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    1 - p1 psi q = (1 - q) / denominator psi q := by
  have nonzero := (denominator_pos positive nuisance).ne'
  unfold p1
  field_simp [nonzero]
  unfold denominator
  ring

/-- The finite OR null cross-product equation includes `q=0` and `q=1`.
An odds quotient is not asserted at those degenerate nuisance endpoints. -/
theorem parameterization {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    p1 psi q * (1 - q) = psi * q * (1 - p1 psi q) := by
  rw [one_sub_p1 positive nuisance, p1]
  ring

/-- Rational arithmetic specializes to the identical real probability link. -/
theorem rationalCoercion (psi q : ℚ) :
    ((psi * q / (1 - q + psi * q) : ℚ) : ℝ) = p1 (psi : ℝ) (q : ℝ) := by
  simp [p1, denominator]

/-- No pole is introduced at the all-failure nuisance endpoint. -/
theorem p1_at_zero (psi : ℝ) : p1 psi 0 = 0 := by
  simp [p1, denominator]

/-- No pole is introduced at the all-success nuisance endpoint. -/
theorem p1_at_one {psi : ℝ} (positive : 0 < psi) : p1 psi 1 = 1 := by
  simp [p1, denominator, ne_of_gt positive]

/-- The complete OR-MASS numerator for one bounded-count outcome. -/
noncomputable def numerator {n1 n0 : ℕ} (psi q : ℝ)
    (outcome : Outcome n1 n0) : ℝ :=
  (n1.choose outcome.1.val : ℝ) * (n0.choose outcome.2.val : ℝ) *
    psi ^ outcome.1.val * q ^ (outcome.1.val + outcome.2.val) *
    (1 - q) ^ (n1 + n0 - (outcome.1.val + outcome.2.val))

/-- Clearing the transformed arm uses exactly its own sample size. -/
theorem first_binomial_identity (n x : ℕ) (bounded : x ≤ n)
    {psi q : ℝ} (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    Exactcis.Spine.binMass n x (p1 psi q) =
      (n.choose x : ℝ) * psi ^ x * q ^ x * (1 - q) ^ (n - x) /
        denominator psi q ^ n := by
  have exponents : x + (n - x) = n := by omega
  unfold Exactcis.Spine.binMass
  rw [one_sub_p1 positive nuisance, p1, div_pow, div_pow, mul_pow]
  calc
    (n.choose x : ℝ) * (psi ^ x * q ^ x / denominator psi q ^ x) *
        ((1 - q) ^ (n - x) / denominator psi q ^ (n - x)) =
      (n.choose x : ℝ) * psi ^ x * q ^ x * (1 - q) ^ (n - x) /
        (denominator psi q ^ x * denominator psi q ^ (n - x)) := by ring
    _ = _ := by rw [← pow_add, exponents]

/-- The pointwise OR-MASS identity for the existing joint weight formula. -/
theorem weight_identity {n1 n0 : ℕ} {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Outcome n1 n0) :
    ProductBinomial.weight (p1 psi q) q outcome =
      numerator psi q outcome / denominator psi q ^ n1 := by
  have first_bound : outcome.1.val ≤ n1 := Nat.le_of_lt_succ outcome.1.isLt
  have second_bound : outcome.2.val ≤ n0 := Nat.le_of_lt_succ outcome.2.isLt
  have exponents : n1 - outcome.1.val + (n0 - outcome.2.val) =
      n1 + n0 - (outcome.1.val + outcome.2.val) := by omega
  unfold ProductBinomial.weight
  rw [first_binomial_identity n1 outcome.1.val first_bound positive nuisance]
  unfold Exactcis.Spine.binMass numerator
  rw [pow_add, ← exponents, pow_add]
  ring

/-- The finite OR null is the normalized product-binomial model at its actual
real probability parameters. -/
noncomputable def mass (n1 n0 : ℕ) (psi q : ℝ) (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : FiniteMass (Outcome n1 n0) :=
  ProductBinomial.mass n1 n0 (p1 psi q) q (p1_mem_Icc positive nuisance) nuisance

/-- U0 OR-MASS, including the transformed-group exponent `n1`. -/
theorem massIdentity {n1 n0 : ℕ} {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Outcome n1 n0) :
    (mass n1 n0 psi q positive nuisance).weight outcome =
      numerator psi q outcome / (1 + (psi - 1) * q) ^ n1 := by
  change ProductBinomial.weight (p1 psi q) q outcome = _
  rw [weight_identity positive nuisance, denominator_alt]

/-- The common denominator is strictly positive even for a zero-trial arm. -/
theorem denominatorPower_pos (n1 : ℕ) {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    0 < (1 + (psi - 1) * q) ^ n1 := by
  rw [← denominator_alt]
  exact pow_pos (denominator_pos positive nuisance) n1

/-- The raw fixed-mask objective is defined without proof-valued arguments,
so its continuity can be stated on the full real nuisance interval. -/
noncomputable def objective {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi q : ℝ) : ℝ := ∑ outcome ∈ mask, ProductBinomial.weight (p1 psi q) q outcome

/-- Any exact finite mask has the sum of its OR-MASS numerators over the same
positive denominator. No actual Boschloo mask is assumed or constructed. -/
theorem eventMassIdentity {n1 n0 : ℕ} {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (mask : Finset (Outcome n1 n0)) :
    (mass n1 n0 psi q positive nuisance).eventMass mask =
      (∑ outcome ∈ mask, numerator psi q outcome) / (1 + (psi - 1) * q) ^ n1 := by
  unfold FiniteMass.eventMass
  simp_rw [massIdentity positive nuisance]
  rw [Finset.sum_div]

/-- The raw objective agrees with the normalized finite model's event mass. -/
theorem objective_eq_eventMass {n1 n0 : ℕ} {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (mask : Finset (Outcome n1 n0)) :
    objective mask psi q = (mass n1 n0 psi q positive nuisance).eventMass mask := rfl

/-- Every fixed-mask objective is continuous over the full real nuisance
interval for a finite positive effect. -/
theorem continuous {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) :
    ContinuousOn (objective mask psi) (Set.Icc (0 : ℝ) 1) := by
  have link_continuous : ContinuousOn (p1 psi) (Set.Icc (0 : ℝ) 1) := by
    unfold p1 denominator
    apply ContinuousOn.div
    · fun_prop
    · fun_prop
    · intro q nuisance
      exact (denominator_pos positive nuisance).ne'
  unfold objective ProductBinomial.weight
  apply continuousOn_finsetSum
  intro outcome _
  exact ((Exactcis.Spine.binMass_continuous _ _).comp_continuousOn link_continuous).mul
    (Exactcis.Spine.binMass_continuous _ _).continuousOn

/-- Reciprocal effect transport must also transform nuisance to the old first
arm probability. This link identity includes both nuisance endpoints. -/
theorem reciprocalLink {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : p1 psi⁻¹ (p1 psi q) = q := by
  have psi_nonzero := positive.ne'
  have original_nonzero := (denominator_pos positive nuisance).ne'
  have reciprocal_positive : 0 < psi⁻¹ := inv_pos.mpr positive
  have transformed_nuisance := p1_mem_Icc positive nuisance
  have transformed_nonzero :=
    (denominator_pos reciprocal_positive transformed_nuisance).ne'
  unfold p1 at transformed_nonzero ⊢
  unfold denominator at transformed_nonzero original_nonzero ⊢
  field_simp [psi_nonzero, original_nonzero, transformed_nonzero]
  ring

/-- Swapping groups preserves each point mass under reciprocal-effect and
transformed-nuisance transport. This says nothing about directional ordering. -/
theorem groupSwapMass {n1 n0 : ℕ} {psi q : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (outcome : Outcome n1 n0) :
    (mass n1 n0 psi q positive nuisance).weight outcome =
      (mass n0 n1 psi⁻¹ (p1 psi q) (inv_pos.mpr positive)
        (p1_mem_Icc positive nuisance)).weight outcome.swap := by
  change ProductBinomial.weight (p1 psi q) q outcome =
    ProductBinomial.weight (p1 psi⁻¹ (p1 psi q)) (p1 psi q) outcome.swap
  rw [reciprocalLink positive nuisance]
  unfold ProductBinomial.weight
  exact mul_comm _ _

end ExactCIs.Unconditional.ORNull
