/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ORNull

/-!
# Common-degree Bernstein representation of the actual OR mass

U0 B.4, U-OR-BERN-001 and U-OR-CONTROL-001: a fixed mask on the natural product-binomial
sample space has a degree `n1+n0` numerator and positive denominator
coefficients. Coefficient ratios are conditional mask masses at a fixed total.
This module concerns finite positive effects, not structural effect endpoints,
moving Boschloo masks, concrete subdivision/checkers, or Python execution.
-/

namespace ExactCIs.Unconditional.ORBernstein

open ProductBinomial

abbrev Index (n1 n0 : ℕ) := Fin (n1 + n0 + 1)

def total {n1 n0 : ℕ} (o : Outcome n1 n0) : Index n1 n0 :=
  ⟨o.1.val + o.2.val, by have := o.1.isLt; have := o.2.isLt; omega⟩

noncomputable def factor {n1 n0 : ℕ} (psi : ℝ) (o : Outcome n1 n0) : ℝ :=
  (n1.choose o.1.val : ℝ) * (n0.choose o.2.val : ℝ) * psi ^ o.1.val

noncomputable def coefficient {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi : ℝ) (k : Index n1 n0) : ℝ :=
  (∑ o ∈ mask, if total o = k then factor psi o else 0) /
    (n1 + n0).choose k.val

noncomputable def basis {n1 n0 : ℕ} (k : Index n1 n0) (q : ℝ) : ℝ :=
  ((n1 + n0).choose k.val : ℝ) * q ^ k.val * (1 - q) ^ (n1 + n0 - k.val)

noncomputable def value {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi q : ℝ) : ℝ := ∑ k : Index n1 n0, coefficient mask psi k * basis k q

def rationalCoefficient {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi : ℚ) (k : Index n1 n0) : ℚ :=
  (∑ o ∈ mask, if total o = k then
    (n1.choose o.1.val : ℚ) * (n0.choose o.2.val : ℚ) * psi ^ o.1.val else 0) /
    (n1 + n0).choose k.val

theorem rational_coercion {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi : ℚ) (k : Index n1 n0) :
    (rationalCoefficient mask psi k : ℝ) = coefficient mask (psi : ℝ) k := by
  unfold rationalCoefficient coefficient factor
  push_cast
  congr 1
  apply Finset.sum_congr rfl
  intro o _
  split_ifs <;> push_cast <;> rfl

theorem choose_pos {n1 n0 : ℕ} (k : Index n1 n0) :
    (0 : ℝ) < (n1 + n0).choose k.val := by
  exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ k.isLt)

theorem factor_pos {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (o : Outcome n1 n0) : 0 < factor psi o := by
  have h1 : (0 : ℝ) < n1.choose o.1.val := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ o.1.isLt)
  have h0 : (0 : ℝ) < n0.choose o.2.val := by
    exact_mod_cast Nat.choose_pos (Nat.le_of_lt_succ o.2.isLt)
  exact mul_pos (mul_pos h1 h0) (pow_pos positive _)

theorem coefficient_nonneg {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) (k : Index n1 n0) :
    0 ≤ coefficient mask psi k := by
  apply div_nonneg _ (choose_pos k).le
  apply Finset.sum_nonneg
  intro o _
  split_ifs
  · exact (factor_pos positive o).le
  · exact le_rfl

theorem coefficient_mono {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    {left right : Finset (Outcome n1 n0)} (included : left ⊆ right)
    (k : Index n1 n0) : coefficient left psi k ≤ coefficient right psi k := by
  apply div_le_div_of_nonneg_right _ (choose_pos k).le
  apply Finset.sum_le_sum_of_subset_of_nonneg included
  intro o _ _
  split_ifs
  · exact (factor_pos positive o).le
  · exact le_rfl

/-- Each total between zero and N has an actual bounded-count outcome. -/
theorem total_surjective (n1 n0 : ℕ) : Function.Surjective (@total n1 n0) := by
  intro k
  let x := min k.val n1
  have kbound := k.isLt
  have hx : x ≤ n1 := min_le_right _ _
  have hxk : x ≤ k.val := min_le_left _ _
  have hy : k.val - x ≤ n0 := by dsimp [x]; omega
  refine ⟨(⟨x, by omega⟩, ⟨k.val - x, by omega⟩), ?_⟩
  apply Fin.ext
  simp only [total]
  omega

theorem denominator_coefficient_pos {n1 n0 : ℕ} {psi : ℝ}
    (positive : 0 < psi) (k : Index n1 n0) :
    0 < coefficient Finset.univ psi k := by
  apply div_pos _ (choose_pos k)
  obtain ⟨o, ho⟩ := total_surjective n1 n0 k
  apply Finset.sum_pos'
  · intro a _
    split_ifs
    · exact (factor_pos positive a).le
    · exact le_rfl
  · exact ⟨o, Finset.mem_univ o, by simpa [ho] using factor_pos positive o⟩

theorem basis_nonneg {n1 n0 : ℕ} (k : Index n1 n0) {q : ℝ}
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ basis k q :=
  mul_nonneg (mul_nonneg (choose_pos k).le (pow_nonneg nuisance.1 _))
    (pow_nonneg (sub_nonneg.mpr nuisance.2) _)

/-- Actual OR numerators regrouped by total successes, with no approximation. -/
theorem numerator_identity {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi q : ℝ) : value mask psi q = ∑ o ∈ mask, ORNull.numerator psi q o := by
  unfold value coefficient
  simp_rw [div_mul_eq_mul_div, Finset.sum_mul, Finset.sum_div]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro o _
  rw [Finset.sum_eq_single (total o)]
  · simp only [ite_true]
    unfold factor basis ORNull.numerator total
    have h := (choose_pos (total o)).ne'
    dsimp [total] at h
    field_simp
  · intro k _ different
    simp [Ne.symm different]
  · simp

theorem event_identity {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass mask =
      value mask psi q / (1 + (psi - 1) * q) ^ n1 := by
  rw [numerator_identity, ORNull.eventMassIdentity positive nuisance]

theorem denominator_identity {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    value (Finset.univ : Finset (Outcome n1 n0)) psi q =
      (1 + (psi - 1) * q) ^ n1 := by
  have h := event_identity positive nuisance (Finset.univ : Finset (Outcome n1 n0))
  have normalized : (ORNull.mass n1 n0 psi q positive nuisance).eventMass Finset.univ = 1 :=
    (ORNull.mass n1 n0 psi q positive nuisance).normalizes
  rw [normalized] at h
  exact (div_eq_one_iff_eq (ORNull.denominatorPower_pos n1 positive nuisance).ne').mp h.symm

noncomputable def control {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi : ℝ) (k : Index n1 n0) : ℝ :=
  coefficient mask psi k / coefficient Finset.univ psi k

theorem control_mem_Icc {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) (k : Index n1 n0) :
    control mask psi k ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (coefficient_nonneg positive mask k)
      (denominator_coefficient_pos positive k).le
  · exact (div_le_one (denominator_coefficient_pos positive k)).mpr
      (coefficient_mono positive (Finset.subset_univ mask) k)

/-- Ratios equal the conditional mask probabilities given the total-success
fibre. This identity is independent of nuisance, including endpoint limits. -/
theorem control_fibre_ratio {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi : ℝ) (k : Index n1 n0) : control mask psi k =
      (∑ o ∈ mask, if total o = k then factor psi o else 0) /
      (∑ o : Outcome n1 n0, if total o = k then factor psi o else 0) := by
  unfold control coefficient
  exact div_div_div_cancel_right₀ (choose_pos k).ne' _ _

theorem fibre_weight_sum {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0))
    (k : Index n1 n0) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
        (mask.filter (fun o => total o = k)) =
      (q ^ k.val * (1 - q) ^ (n1 + n0 - k.val) /
        (1 + (psi - 1) * q) ^ n1) *
      (∑ o ∈ mask, if total o = k then factor psi o else 0) := by
  unfold FiniteMass.eventMass
  rw [Finset.sum_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro o _
  by_cases h : total o = k
  · simp only [h, ite_true]
    rw [ORNull.massIdentity positive nuisance]
    have indices := congrArg Fin.val h
    dsimp [total] at indices
    unfold ORNull.numerator factor
    rw [indices]
    ring
  · simp [h]

/-- For interior nuisance the total-success event has positive probability,
and the actual conditional event probability is exactly the control ratio.
At nuisance endpoints the coefficient ratio remains its algebraic extension. -/
theorem conditional_mass_ratio {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (interior : q ∈ Set.Ioo (0 : ℝ) 1) (mask : Finset (Outcome n1 n0))
    (k : Index n1 n0) :
    let nuisance : q ∈ Set.Icc (0 : ℝ) 1 := ⟨interior.1.le, interior.2.le⟩
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
        (mask.filter (fun o => total o = k)) /
      (ORNull.mass n1 n0 psi q positive nuisance).eventMass
        (Finset.univ.filter (fun o => total o = k)) = control mask psi k := by
  dsimp only
  rw [fibre_weight_sum positive ⟨interior.1.le, interior.2.le⟩,
    fibre_weight_sum positive ⟨interior.1.le, interior.2.le⟩, control_fibre_ratio]
  have scale_positive : 0 < q ^ k.val * (1 - q) ^ (n1 + n0 - k.val) /
      (1 + (psi - 1) * q) ^ n1 :=
    div_pos (mul_pos (pow_pos interior.1 _) (pow_pos (sub_pos.mpr interior.2) _))
      (ORNull.denominatorPower_pos n1 positive ⟨interior.1.le, interior.2.le⟩)
  exact mul_div_mul_left _ _ scale_positive.ne'

theorem total_mass_pos {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (interior : q ∈ Set.Ioo (0 : ℝ) 1) (k : Index n1 n0) :
    let nuisance : q ∈ Set.Icc (0 : ℝ) 1 := ⟨interior.1.le, interior.2.le⟩
    0 < (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter (fun o => total o = k)) := by
  dsimp only
  rw [fibre_weight_sum positive ⟨interior.1.le, interior.2.le⟩]
  apply mul_pos
  · exact div_pos
      (mul_pos (pow_pos interior.1 _) (pow_pos (sub_pos.mpr interior.2) _))
      (ORNull.denominatorPower_pos n1 positive ⟨interior.1.le, interior.2.le⟩)
  · have h := denominator_coefficient_pos positive k
    unfold coefficient at h
    exact (div_pos_iff_of_pos_right (choose_pos k)).mp h

theorem equality_null_polynomial {n1 n0 : ℕ} {q : ℝ}
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    (ORNull.mass n1 n0 1 q (by norm_num) nuisance).eventMass mask = value mask 1 q := by
  rw [event_identity (by norm_num) nuisance mask]
  simp

theorem control_bounds {n1 n0 : ℕ} {psi q lo hi : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0))
    (lower : ∀ k, lo ≤ control mask psi k) (upper : ∀ k, control mask psi k ≤ hi) :
    lo ≤ (ORNull.mass n1 n0 psi q positive nuisance).eventMass mask ∧
      (ORNull.mass n1 n0 psi q positive nuisance).eventMass mask ≤ hi := by
  have hl : lo * value (Finset.univ : Finset (Outcome n1 n0)) psi q ≤ value mask psi q := by
    unfold value
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have bound := (le_div_iff₀ (denominator_coefficient_pos positive k)).mp (lower k)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right bound (basis_nonneg k nuisance)
  have hu : value mask psi q ≤ hi * value (Finset.univ : Finset (Outcome n1 n0)) psi q := by
    unfold value
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k _
    have bound := (div_le_iff₀ (denominator_coefficient_pos positive k)).mp (upper k)
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right bound (basis_nonneg k nuisance)
  rw [event_identity positive nuisance mask]
  rw [denominator_identity positive nuisance] at hl hu
  exact ⟨(le_div_iff₀ (ORNull.denominatorPower_pos n1 positive nuisance)).mpr hl,
    (div_le_iff₀ (ORNull.denominatorPower_pos n1 positive nuisance)).mpr hu⟩

noncomputable def threshold {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0))
    (psi r q : ℝ) : ℝ := value mask psi q - r * value (Finset.univ : Finset (Outcome n1 n0)) psi q

theorem threshold_iff {n1 n0 : ℕ} {psi q r : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    r ≤ (ORNull.mass n1 n0 psi q positive nuisance).eventMass mask ↔
      0 ≤ threshold mask psi r q := by
  rw [event_identity positive nuisance mask,
    le_div_iff₀ (ORNull.denominatorPower_pos n1 positive nuisance)]
  unfold threshold
  rw [denominator_identity positive nuisance]
  exact sub_nonneg.symm

theorem strict_rejection_iff {n1 n0 : ℕ} {psi q r : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass mask < r ↔
      threshold mask psi r q < 0 := by
  have h := threshold_iff (r := r) positive nuisance mask
  exact lt_iff_lt_of_le_iff_le h

end ExactCIs.Unconditional.ORBernstein
