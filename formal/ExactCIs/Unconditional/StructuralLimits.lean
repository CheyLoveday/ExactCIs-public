/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooValidity
import ExactCIs.Unconditional.Structural

/-! # Nuisance-uniform endpoint mass bounds

These estimates use the finite positive OR mass, uniformly for every nuisance
in the closed unit interval. Actual-mask corollaries explicitly consume an
exponent-stratum premise; no tagged endpoint mask replaces the finite mask.
-/
namespace ExactCIs.Unconditional.StructuralLimits

open ProductBinomial BoschlooOrdering

noncomputable def coefficient {n1 n0 : ℕ} (o : Outcome n1 n0) : ℝ :=
  (n1.choose o.1.val : ℝ) * n0.choose o.2.val

noncomputable def totalCoefficient (n1 n0 : ℕ) : ℝ :=
  ∑ o : Outcome n1 n0, coefficient o

theorem coefficient_pos {n1 n0 : ℕ} (o : Outcome n1 n0) : 0 < coefficient o := by
  unfold coefficient
  exact mul_pos (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ o.1.isLt))
    (by exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ o.2.isLt))

theorem totalCoefficient_pos (n1 n0 : ℕ) : 0 < totalCoefficient n1 n0 := by
  apply Finset.sum_pos'
  · intro o _; exact (coefficient_pos o).le
  · exact ⟨(0, 0), Finset.mem_univ _, coefficient_pos _⟩

theorem probability_pair_bound {p q : ℝ} (hp : p ∈ Set.Icc (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) {x y r : ℕ} (hx : r ≤ x) (hy : r ≤ y) :
    p ^ x * q ^ y ≤ (p * q) ^ r := by
  rw [mul_pow]
  exact mul_le_mul (pow_le_pow_of_le_one hp.1 hp.2 hx)
    (pow_le_pow_of_le_one hq.1 hq.2 hy) (pow_nonneg hq.1 _) (pow_nonneg hp.1 _)

theorem weight_pair_bound {n1 n0 : ℕ} {p q : ℝ}
    (hp : p ∈ Set.Icc (0 : ℝ) 1) (hq : q ∈ Set.Icc (0 : ℝ) 1)
    (o : Outcome n1 n0) {r : ℕ} (hx : r ≤ o.1.val) (hy : r ≤ n0 - o.2.val) :
    weight p q o ≤ coefficient o * (p * (1 - q)) ^ r := by
  have hp' : 1 - p ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hp.1, hp.2]
  have hq' : 1 - q ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> linarith [hq.1, hq.2]
  have small : (1 - p) ^ (n1 - o.1.val) * q ^ o.2.val ≤ 1 := by
    exact mul_le_one₀ (pow_le_one₀ hp'.1 hp'.2) (pow_nonneg hq.1 _)
      (pow_le_one₀ hq.1 hq.2)
  calc
    weight p q o = coefficient o * (p ^ o.1.val * (1 - q) ^ (n0 - o.2.val)) *
        ((1 - p) ^ (n1 - o.1.val) * q ^ o.2.val) := by
      unfold weight coefficient Exactcis.Spine.binMass
      ring
    _ ≤ coefficient o * (p ^ o.1.val * (1 - q) ^ (n0 - o.2.val)) * 1 := by
      exact mul_le_mul_of_nonneg_left small
        (mul_nonneg (coefficient_pos o).le
          (mul_nonneg (pow_nonneg hp.1 _) (pow_nonneg hq'.1 _)))
    _ ≤ coefficient o * (p * (1 - q)) ^ r := by
      rw [mul_one]
      exact mul_le_mul_of_nonneg_left (probability_pair_bound hp hq' hx hy)
        (coefficient_pos o).le

theorem link_pair_bound {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : ORNull.p1 psi q * (1 - q) ≤ psi := by
  have hp := ORNull.p1_mem_Icc positive nuisance
  rw [ORNull.parameterization positive nuisance]
  calc
    psi * q * (1 - ORNull.p1 psi q) ≤ psi * 1 * 1 := by
      gcongr <;> linarith [hp.1, hp.2, nuisance.1, nuisance.2]
    _ = psi := by ring

theorem zero_weight_bound {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (o : Outcome n1 n0) {r : ℕ}
    (hx : r ≤ o.1.val) (hy : r ≤ n0 - o.2.val) :
    weight (ORNull.p1 psi q) q o ≤ coefficient o * psi ^ r := by
  apply (weight_pair_bound (ORNull.p1_mem_Icc positive nuisance) nuisance o hx hy).trans
  apply mul_le_mul_of_nonneg_left _ (coefficient_pos o).le
  exact pow_le_pow_left₀ (mul_nonneg (ORNull.p1_mem_Icc positive nuisance).1
    (sub_nonneg.mpr nuisance.2)) (link_pair_bound positive nuisance) r

theorem infinity_weight_bound {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (o : Outcome n1 n0) {r : ℕ}
    (hy : r ≤ o.2.val) (hx : r ≤ n1 - o.1.val) :
    weight (ORNull.p1 psi q) q o ≤ coefficient o / psi ^ r := by
  have bound := zero_weight_bound (inv_pos.mpr positive)
    (ORNull.p1_mem_Icc positive nuisance) o.swap hy hx
  rw [ORNull.reciprocalLink positive nuisance] at bound
  have swapped : weight q (ORNull.p1 psi q) o.swap = weight (ORNull.p1 psi q) q o := by
    simp only [weight, Prod.swap]; ring
  rw [swapped] at bound
  simpa [coefficient, mul_comm, inv_pow, div_eq_mul_inv] using bound

theorem zero_mask_bound {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (R : Finset (Outcome n1 n0)) {r : ℕ}
    (stratum : ∀ o ∈ R, r ≤ min o.1.val (n0 - o.2.val)) :
    ORNull.objective R psi q ≤ totalCoefficient n1 n0 * psi ^ r := by
  calc
    ORNull.objective R psi q ≤ ∑ o ∈ R, coefficient o * psi ^ r := by
      apply Finset.sum_le_sum
      intro o ho
      exact zero_weight_bound positive nuisance o ((le_min_iff.mp (stratum o ho)).1)
        ((le_min_iff.mp (stratum o ho)).2)
    _ ≤ ∑ o : Outcome n1 n0, coefficient o * psi ^ r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun o _ _ => mul_nonneg (coefficient_pos o).le (pow_nonneg positive.le _))
    _ = totalCoefficient n1 n0 * psi ^ r := by rw [totalCoefficient, Finset.sum_mul]

theorem infinity_mask_bound {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (R : Finset (Outcome n1 n0)) {r : ℕ}
    (stratum : ∀ o ∈ R, r ≤ min o.2.val (n1 - o.1.val)) :
    ORNull.objective R psi q ≤ totalCoefficient n1 n0 / psi ^ r := by
  calc
    ORNull.objective R psi q ≤ ∑ o ∈ R, coefficient o / psi ^ r := by
      apply Finset.sum_le_sum
      intro o ho
      exact infinity_weight_bound positive nuisance o ((le_min_iff.mp (stratum o ho)).1)
        ((le_min_iff.mp (stratum o ho)).2)
    _ ≤ ∑ o : Outcome n1 n0, coefficient o / psi ^ r := by
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun o _ _ => div_nonneg (coefficient_pos o).le (pow_nonneg positive.le _))
    _ = totalCoefficient n1 n0 / psi ^ r := by rw [totalCoefficient, Finset.sum_div]

theorem zero_supremum_bound {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (R : Finset (Outcome n1 n0)) {r : ℕ}
    (stratum : ∀ o ∈ R, r ≤ min o.1.val (n0 - o.2.val)) :
    NuisanceSupremum.value R psi ≤ totalCoefficient n1 n0 * psi ^ r := by
  obtain ⟨q, hq, eq⟩ := NuisanceSupremum.attained positive R
  rw [← eq]
  exact zero_mask_bound positive hq R stratum

theorem infinity_supremum_bound {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (R : Finset (Outcome n1 n0)) {r : ℕ}
    (stratum : ∀ o ∈ R, r ≤ min o.2.val (n1 - o.1.val)) :
    NuisanceSupremum.value R psi ≤ totalCoefficient n1 n0 / psi ^ r := by
  obtain ⟨q, hq, eq⟩ := NuisanceSupremum.attained positive R
  rw [← eq]
  exact infinity_mask_bound positive hq R stratum

end ExactCIs.Unconditional.StructuralLimits
