/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ORBernstein
import CarfSpine.ThresholdTangency

/-! # Attained fixed-mask OR nuisance suprema

The nuisance domain is the entire real closed unit interval. The effect is
finite and positive in every semantic theorem. Structural effects are separate.
-/
namespace ExactCIs.Unconditional.NuisanceSupremum

open ProductBinomial

noncomputable def value {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (psi : ℝ) : ℝ :=
  sSup (ORNull.objective mask psi '' Set.Icc (0 : ℝ) 1)

theorem attained {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, ORNull.objective mask psi q = value mask psi := by
  exact (isCompact_Icc.image_of_continuousOn (ORNull.continuous positive mask)).sSup_mem
    ((Set.nonempty_Icc.mpr zero_le_one).image _)

theorem point_le {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (mask : Finset (Outcome n1 n0)) :
    ORNull.objective mask psi q ≤ value mask psi :=
  le_csSup (isCompact_Icc.image_of_continuousOn
    (ORNull.continuous positive mask)).bddAbove ⟨q, nuisance, rfl⟩

theorem mem_Icc {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) : value mask psi ∈ Set.Icc (0 : ℝ) 1 := by
  obtain ⟨q, nuisance, h⟩ := attained positive mask
  rw [← h, ORNull.objective_eq_eventMass positive nuisance]
  exact ⟨FiniteMass.eventMass_nonnegative _ (Finset.subset_univ _),
    FiniteMass.eventMass_le_one _ (Finset.subset_univ _)⟩

theorem accept_iff {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) :
    r ≤ value mask psi ↔ ∃ q ∈ Set.Icc (0 : ℝ) 1, r ≤ ORNull.objective mask psi q :=
  (Exactcis.Spine.exists_ge_iff_le_sSup (ORNull.continuous positive mask) r).symm

theorem reject_iff {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) :
    value mask psi < r ↔ ∀ q ∈ Set.Icc (0 : ℝ) 1, ORNull.objective mask psi q < r :=
  (Exactcis.Spine.forall_lt_iff_sSup_lt (ORNull.continuous positive mask) r).symm

theorem threshold_iff {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    (mask : Finset (Outcome n1 n0)) :
    r ≤ value mask psi ↔
      ∃ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ ORBernstein.threshold mask psi r q := by
  rw [accept_iff positive mask]
  constructor
  · rintro ⟨q, nuisance, accepted⟩
    exact ⟨q, nuisance, (ORBernstein.threshold_iff positive nuisance mask).mp accepted⟩
  · rintro ⟨q, nuisance, accepted⟩
    exact ⟨q, nuisance, (ORBernstein.threshold_iff positive nuisance mask).mpr accepted⟩

theorem mono {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    {lower upper : Finset (Outcome n1 n0)} (included : lower ⊆ upper) :
    value lower psi ≤ value upper psi := by
  obtain ⟨q, nuisance, h⟩ := attained positive lower
  rw [← h]
  exact (FiniteMass.eventMass_mono (ORNull.mass n1 n0 psi q positive nuisance)
    included (Finset.subset_univ _)).trans (point_le positive nuisance upper)

theorem accept_from_lower {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    {lower actual : Finset (Outcome n1 n0)} (included : lower ⊆ actual)
    (accepted : r ≤ value lower psi) : r ≤ value actual psi :=
  accepted.trans (mono positive included)

theorem reject_from_upper {n1 n0 : ℕ} {psi r : ℝ} (positive : 0 < psi)
    {actual upper : Finset (Outcome n1 n0)} (included : actual ⊆ upper)
    (rejected : value upper psi < r) : value actual psi < r :=
  (mono positive included).trans_lt rejected

theorem full {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi) :
    value (Finset.univ : Finset (Outcome n1 n0)) psi = 1 := by
  obtain ⟨q, nuisance, h⟩ := attained positive (Finset.univ : Finset (Outcome n1 n0))
  rw [← h, ORNull.objective_eq_eventMass positive nuisance]
  exact (ORNull.mass n1 n0 psi q positive nuisance).normalizes

theorem empty {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi) :
    value (∅ : Finset (Outcome n1 n0)) psi = 0 := by
  obtain ⟨q, _, h⟩ := attained positive (∅ : Finset (Outcome n1 n0))
  rw [← h]
  simp [ORNull.objective]

end ExactCIs.Unconditional.NuisanceSupremum
