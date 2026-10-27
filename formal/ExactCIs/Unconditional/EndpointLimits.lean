/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.EndpointOrdering

/-! # Actual finite-mask strata and endpoint limits

The uniform epsilon statements quantify over every real nuisance, not a grid.
The opposite direction is bounded by one from the existing probability theorem.
These facts do not assert continuity of the singular full probability square.
-/
namespace ExactCIs.Unconditional.EndpointLimits

open ProductBinomial BoschlooOrdering EndpointOrdering StructuralLimits

theorem eventual_zero_mask {n1 n0 : ℕ} (observed : Outcome n1 n0) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ psi : ℝ, 0 < psi → psi ≤ delta →
      ∀ candidate ∈ mask .greater psi observed,
        min observed.1.val (n0 - observed.2.val) ≤
          min candidate.1.val (n0 - candidate.2.val) := by
  obtain ⟨delta, positive, bound, stratum⟩ := eventual_stratum .greater observed
  refine ⟨delta, positive, bound, ?_⟩
  intro psi hp small candidate member
  have selected := (Finset.mem_filter.mp member).2
  rw [statistic_factor .greater candidate hp, statistic_factor .greater observed hp] at selected
  exact stratum psi hp small candidate (by simpa using selected)

theorem eventual_infinity_mask {n1 n0 : ℕ} (observed : Outcome n1 n0) :
    ∃ M : ℝ, 1 < M ∧ ∀ psi : ℝ, M ≤ psi →
      ∀ candidate ∈ mask .less psi observed,
        min observed.2.val (n1 - observed.1.val) ≤
          min candidate.2.val (n1 - candidate.1.val) := by
  obtain ⟨delta, positive, _, stratum⟩ := eventual_stratum .less observed
  refine ⟨2 + 1 / delta, by have := div_pos zero_lt_one positive; linarith, ?_⟩
  intro psi large candidate member
  have hp : 0 < psi := by have := div_pos zero_lt_one positive; linarith
  have small : psi⁻¹ ≤ delta := by
    rw [← one_div, div_le_iff₀ hp]
    have : 1 / delta ≤ psi := by linarith
    have := (div_le_iff₀ positive).mp this
    nlinarith
  have selected := (Finset.mem_filter.mp member).2
  rw [statistic_factor .less candidate hp, statistic_factor .less observed hp] at selected
  exact stratum psi⁻¹ (inv_pos.mpr hp) small candidate (by simpa using selected)

/-- The same constant and region work simultaneously for mass and supremum. -/
theorem zero_bounds {n1 n0 : ℕ} (observed : Outcome n1 n0) :
    ∃ C delta : ℝ, 0 < C ∧ 0 < delta ∧ delta ≤ 1 ∧
      ∀ psi : ℝ, 0 < psi → psi ≤ delta →
        (∀ q ∈ Set.Icc (0 : ℝ) 1, ORNull.objective (mask .greater psi observed) psi q ≤
          C * psi ^ min observed.1.val (n0 - observed.2.val)) ∧
        BoschlooValidity.value .greater psi observed ≤
          C * psi ^ min observed.1.val (n0 - observed.2.val) := by
  obtain ⟨delta, positive, bound, stratum⟩ := eventual_zero_mask observed
  refine ⟨totalCoefficient n1 n0, delta, totalCoefficient_pos _ _, positive, bound, ?_⟩
  intro psi hp small
  exact ⟨fun q hq => zero_mask_bound hp hq _ (stratum psi hp small),
    zero_supremum_bound hp _ (stratum psi hp small)⟩

theorem infinity_bounds {n1 n0 : ℕ} (observed : Outcome n1 n0) :
    ∃ C M : ℝ, 0 < C ∧ 1 < M ∧ ∀ psi : ℝ, M ≤ psi →
      (∀ q ∈ Set.Icc (0 : ℝ) 1, ORNull.objective (mask .less psi observed) psi q ≤
        C / psi ^ min observed.2.val (n1 - observed.1.val)) ∧
      BoschlooValidity.value .less psi observed ≤
        C / psi ^ min observed.2.val (n1 - observed.1.val) := by
  obtain ⟨M, large, stratum⟩ := eventual_infinity_mask observed
  refine ⟨totalCoefficient n1 n0, M, totalCoefficient_pos _ _, large, ?_⟩
  intro psi hp
  have positive : 0 < psi := lt_trans zero_lt_one (large.trans_le hp)
  exact ⟨fun q hq => infinity_mask_bound positive hq _ (stratum psi hp),
    infinity_supremum_bound positive _ (stratum psi hp)⟩

/-- An unsupported zero endpoint has a vanishing finite greater p-value and
uniformly vanishing finite-mask mass. The exponent is the observed common order. -/
theorem zero_uniform_limit {n1 n0 : ℕ} (observed : Outcome n1 n0)
    (unsupported : ¬ Structural.Supported .zero observed) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧
      ∀ psi : ℝ, 0 < psi → psi ≤ delta →
        BoschlooValidity.value .greater psi observed < epsilon ∧
        ∀ q ∈ Set.Icc (0 : ℝ) 1,
          ORNull.objective (mask .greater psi observed) psi q < epsilon := by
  have rpos : 0 < min observed.1.val (n0 - observed.2.val) := by
    have := observed.2.isLt
    simp only [Structural.Supported, not_or] at unsupported
    omega
  obtain ⟨C, delta, hc, hd, hdone, bounds⟩ := zero_bounds observed
  intro epsilon he
  refine ⟨min delta (epsilon / (2 * C)), lt_min hd (by positivity),
    (min_le_left _ _).trans hdone, ?_⟩
  intro psi hp small
  obtain ⟨mass, sup⟩ := bounds psi hp (small.trans (min_le_left _ _))
  have psmall : psi ≤ 1 := small.trans ((min_le_left _ _).trans hdone)
  have pbound : psi ^ min observed.1.val (n0 - observed.2.val) ≤ psi :=
    pow_le_of_le_one hp.le psmall (Nat.ne_zero_of_lt rpos)
  have strict : C * psi ^ min observed.1.val (n0 - observed.2.val) < epsilon := by
    have hh := (le_div_iff₀ (by positivity : 0 < 2 * C)).mp
      (small.trans (min_le_right delta (epsilon / (2 * C))))
    nlinarith [mul_le_mul_of_nonneg_left pbound hc.le]
  exact ⟨sup.trans_lt strict, fun q hq => (mass q hq).trans_lt strict⟩

theorem infinity_uniform_limit {n1 n0 : ℕ} (observed : Outcome n1 n0)
    (unsupported : ¬ Structural.Supported .infinity observed) :
    ∀ epsilon : ℝ, 0 < epsilon → ∃ M : ℝ, 1 < M ∧ ∀ psi : ℝ, M ≤ psi →
      BoschlooValidity.value .less psi observed < epsilon ∧
      ∀ q ∈ Set.Icc (0 : ℝ) 1,
        ORNull.objective (mask .less psi observed) psi q < epsilon := by
  have rpos : 0 < min observed.2.val (n1 - observed.1.val) := by
    have := observed.1.isLt
    simp only [Structural.Supported, not_or] at unsupported
    omega
  obtain ⟨C, M, hc, hm, bounds⟩ := infinity_bounds observed
  intro epsilon he
  refine ⟨max M (2 * C / epsilon), hm.trans_le (le_max_left _ _), ?_⟩
  intro psi large
  have hp : 0 < psi := lt_trans zero_lt_one (hm.trans_le ((le_max_left _ _).trans large))
  obtain ⟨mass, sup⟩ := bounds psi ((le_max_left _ _).trans large)
  have at_least : 1 ≤ psi := (hm.trans_le ((le_max_left _ _).trans large)).le
  have powlarge : psi ≤ psi ^ min observed.2.val (n1 - observed.1.val) :=
    le_self_pow₀ at_least (Nat.ne_zero_of_lt rpos)
  have strict : C / psi ^ min observed.2.val (n1 - observed.1.val) < epsilon := by
    rw [div_lt_iff₀ (pow_pos hp _)]
    have hh := (div_le_iff₀ he).mp ((le_max_right M (2 * C / epsilon)).trans large)
    nlinarith [mul_le_mul_of_nonneg_left powlarge he.le]
  exact ⟨sup.trans_lt strict, fun q hq => (mass q hq).trans_lt strict⟩

theorem zero_excludes_neighbourhood {n1 n0 : ℕ} (observed : Outcome n1 n0)
    (unsupported : ¬ Structural.Supported .zero observed) {r : ℝ} (level : 0 < r) :
    ∃ delta : ℝ, 0 < delta ∧ ∀ psi : ℝ, 0 < psi → psi ≤ delta →
      ¬ BoschlooValidity.Accepted psi r observed := by
  obtain ⟨delta, positive, _, bound⟩ := zero_uniform_limit observed unsupported r level
  exact ⟨delta, positive, fun psi hp small accepted =>
    (not_le_of_gt (bound psi hp small).1) accepted.1⟩

theorem infinity_excludes_neighbourhood {n1 n0 : ℕ} (observed : Outcome n1 n0)
    (unsupported : ¬ Structural.Supported .infinity observed) {r : ℝ} (level : 0 < r) :
    ∃ M : ℝ, 1 < M ∧ ∀ psi : ℝ, M ≤ psi → ¬ BoschlooValidity.Accepted psi r observed := by
  obtain ⟨M, large, bound⟩ := infinity_uniform_limit observed unsupported r level
  exact ⟨M, large, fun psi hp accepted => (not_le_of_gt (bound psi hp).1) accepted.2⟩

end ExactCIs.Unconditional.EndpointLimits
