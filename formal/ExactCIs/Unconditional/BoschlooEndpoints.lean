/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooValidity
import ExactCIs.Unconditional.InteriorRoot

/-! # The actual full-mask / interior-root split

These are nuisance endpoints at a finite positive effect. They do not assign
the separately tagged structural effects zero and infinity.
-/
namespace ExactCIs.Unconditional.BoschlooEndpoints

open ProductBinomial BoschlooOrdering

def failure (n1 n0 : ℕ) : Outcome n1 n0 := (0, 0)

def success (n1 n0 : ℕ) : Outcome n1 n0 :=
  (⟨n1, Nat.lt_succ_self _⟩, ⟨n0, Nat.lt_succ_self _⟩)

theorem failure_tail_one {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) : statistic direction psi (failure n1 n0) = 1 := by
  have singleton : FNCH.Support.valid n1 n0 0 = {0} := by
    ext k
    simp only [FNCH.Support.mem_valid_iff, Finset.mem_singleton]
    omega
  exact singleton_tail (by omega) positive singleton direction

theorem success_tail_one {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) : statistic direction psi (success n1 n0) = 1 := by
  have singleton : FNCH.Support.valid n1 n0 (n1 + n0) = {n1} := by
    ext k
    simp only [FNCH.Support.mem_valid_iff, Finset.mem_singleton]
    omega
  exact singleton_tail (by omega) positive singleton direction

theorem full_iff_tail_one {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0) :
    mask direction psi observed = Finset.univ ↔ statistic direction psi observed = 1 := by
  classical
  constructor
  · intro full
    have member : failure n1 n0 ∈ mask direction psi observed := by rw [full]; simp
    have bound := (Finset.mem_filter.mp member).2
    rw [failure_tail_one positive direction] at bound
    exact le_antisymm (statistic_mem_Icc positive direction observed).2 bound
  · exact full_mask_of_one positive direction observed

theorem nontrivial_excludes_endpoints {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0)
    (nontrivial : statistic direction psi observed < 1) :
    failure n1 n0 ∉ mask direction psi observed ∧ success n1 n0 ∉ mask direction psi observed := by
  classical
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and,
    failure_tail_one positive direction, success_tail_one positive direction, not_le]
  exact ⟨nontrivial, nontrivial⟩

theorem weight_zero_zero {n1 n0 : ℕ} (o : Outcome n1 n0) :
    weight 0 0 o = if o = failure n1 n0 then 1 else 0 := by
  by_cases first : o.1.val = 0 <;> by_cases second : o.2.val = 0 <;>
    simp [weight, binomial_at_zero, failure, Prod.ext_iff, Fin.ext_iff, first, second]

theorem weight_one_one {n1 n0 : ℕ} (o : Outcome n1 n0) :
    weight 1 1 o = if o = success n1 n0 then 1 else 0 := by
  unfold weight
  rw [binomial_at_one _ _ (Nat.le_of_lt_succ o.1.isLt),
    binomial_at_one _ _ (Nat.le_of_lt_succ o.2.isLt)]
  by_cases first : o.1.val = n1 <;> by_cases second : o.2.val = n0 <;>
    simp [success, Prod.ext_iff, Fin.ext_iff, first, second]

theorem objective_zero {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (psi : ℝ) :
    ORNull.objective mask psi 0 = if failure n1 n0 ∈ mask then 1 else 0 := by
  classical
  simp [ORNull.objective, ORNull.p1_at_zero, weight_zero_zero]

theorem objective_one {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) {psi : ℝ}
    (positive : 0 < psi) :
    ORNull.objective mask psi 1 = if success n1 n0 ∈ mask then 1 else 0 := by
  classical
  simp [ORNull.objective, ORNull.p1_at_one positive, weight_one_one]

theorem value_eq_objective_mul {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    ORBernstein.value mask psi q = ORNull.objective mask psi q * (1 + (psi - 1) * q) ^ n1 := by
  exact (eq_div_iff (ORNull.denominatorPower_pos n1 positive nuisance).ne').mp
    (ORBernstein.event_identity positive nuisance mask) |>.symm

theorem nontrivial_threshold_endpoints {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0)
    (nontrivial : statistic direction psi observed < 1) :
    ORBernstein.threshold (mask direction psi observed) psi r 0 = -r ∧
      ORBernstein.threshold (mask direction psi observed) psi r 1 = -r * psi ^ n1 := by
  obtain ⟨left, right⟩ := nontrivial_excludes_endpoints positive direction observed nontrivial
  have hz : (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  have ho : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by simp
  simp [ORBernstein.threshold, value_eq_objective_mul positive hz,
    value_eq_objective_mul positive ho, objective_zero, objective_one _ positive, left, right]

theorem threshold_continuous {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (psi r : ℝ) :
    Continuous (ORBernstein.threshold mask psi r) := by
  unfold ORBernstein.threshold ORBernstein.value ORBernstein.basis
  fun_prop

theorem accept_iff_interior_root {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    (level : 0 < r) (direction : Direction) (observed : Outcome n1 n0)
    (nontrivial : statistic direction psi observed < 1) :
    r ≤ BoschlooValidity.value direction psi observed ↔
      ∃ q ∈ Set.Ioo (0 : ℝ) 1,
        ORBernstein.threshold (mask direction psi observed) psi r q = 0 := by
  obtain ⟨left, right⟩ := nontrivial_threshold_endpoints positive direction observed nontrivial
  rw [BoschlooValidity.value, NuisanceSupremum.threshold_iff positive]
  apply InteriorRoot.nonnegative_iff_interior_root
    (threshold_continuous _ psi r).continuousOn
  · rw [left]; linarith
  · rw [right]
    exact mul_neg_of_neg_of_pos (neg_neg_of_pos level) (pow_pos positive _)

end ExactCIs.Unconditional.BoschlooEndpoints
