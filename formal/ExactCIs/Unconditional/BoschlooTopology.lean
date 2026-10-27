/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooValidity
import CarfSpine.AcceptedSetTopology

/-! # Actual inclusive-mask topology on the positive effect domain

Nuisance clamping changes nothing on the evaluated [0,1] domain and supplies
globally nonnegative masses to the reused semicontinuity theorem. Structural
effects remain separate; full-square probability-link continuity is not used.
-/
namespace ExactCIs.Unconditional.BoschlooTopology

open Polynomial ProductBinomial BoschlooOrdering

abbrev Positive := {x : ℝ // 0 < x}

noncomputable def outcomeMass {n1 n0 : ℕ} (o : Outcome n1 n0) (z : Positive × ℝ) : ℝ :=
  weight (ORNull.p1 z.1 (Exactcis.Spine.clamp01 z.2)) (Exactcis.Spine.clamp01 z.2) o

theorem outcomeMass_continuous {n1 n0 : ℕ} (o : Outcome n1 n0) : Continuous (outcomeMass o) := by
  have psi : Continuous (fun z : Positive × ℝ => (z.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have q : Continuous (fun z : Positive × ℝ => Exactcis.Spine.clamp01 z.2) :=
    Exactcis.Spine.clamp01_continuous.comp continuous_snd
  have link : Continuous (fun z : Positive × ℝ => ORNull.p1 z.1 (Exactcis.Spine.clamp01 z.2)) :=
    (psi.mul q).div ((continuous_const.sub q).add (psi.mul q))
      (fun z => (ORNull.denominator_pos z.1.property (Exactcis.Spine.clamp01_mem_Icc z.2)).ne')
  exact ((Exactcis.Spine.binMass_continuous n1 o.1).comp link).mul
    ((Exactcis.Spine.binMass_continuous n0 o.2).comp q)

theorem outcomeMass_nonnegative {n1 n0 : ℕ} (o : Outcome n1 n0) (z : Positive × ℝ) :
    0 ≤ outcomeMass o z :=
  weight_nonnegative (ORNull.p1_mem_Icc z.1.property (Exactcis.Spine.clamp01_mem_Icc z.2))
    (Exactcis.Spine.clamp01_mem_Icc z.2) o

def region {n1 n0 : ℕ} (direction : Direction) (candidate observed : Outcome n1 n0) :
    Set (Positive × ℝ) :=
  {z | realEval (comparisonPolynomial direction candidate observed) z.1 ≤ 0}

theorem region_closed {n1 n0 : ℕ} (direction : Direction)
    (candidate observed : Outcome n1 n0) : IsClosed (region direction candidate observed) := by
  exact isClosed_le
    (((comparisonPolynomial direction candidate observed).map (Rat.castHom ℝ)).continuous.comp
      (continuous_subtype_val.comp continuous_fst)) continuous_const

noncomputable def probability {n1 n0 : ℕ} (direction : Direction)
    (observed : Outcome n1 n0) (psi : Positive) (q : ℝ) : ℝ :=
  ∑ o : Outcome n1 n0, (region direction o observed).indicator (outcomeMass o) (psi, q)

theorem probability_usc {n1 n0 : ℕ} (direction : Direction) (observed : Outcome n1 n0) :
    UpperSemicontinuous (fun z : Positive × ℝ => probability direction observed z.1 z.2) := by
  apply upperSemicontinuous_sum
  intro o _
  exact Exactcis.Spine.upperSemicontinuous_indicator_of_continuous
    (region_closed direction o observed) (outcomeMass_continuous o) (outcomeMass_nonnegative o)

theorem probability_agreement {n1 n0 : ℕ} (direction : Direction)
    (observed : Outcome n1 n0) (psi : Positive) {q : ℝ} (nuisance : q ∈ Set.Icc (0 : ℝ) 1) :
    probability direction observed psi q =
      ORNull.objective (mask direction psi observed) psi q := by
  classical
  have mask_eq : mask direction psi observed =
      Finset.univ.filter (fun o => o ∈ mask direction psi observed) := by ext o; simp
  rw [ORNull.objective, mask_eq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro o _
  by_cases member : o ∈ mask direction psi observed
  · have included : (psi, q) ∈ region direction o observed :=
      (mask_iff_polynomial psi.property direction o observed).mp member
    simp only [Set.indicator_of_mem included, if_pos member, outcomeMass,
      Exactcis.Spine.clamp01_eq_self nuisance]
  · have excluded : (psi, q) ∉ region direction o observed :=
      fun included => member ((mask_iff_polynomial psi.property direction o observed).mpr included)
    simp only [Set.indicator_of_notMem excluded, if_neg member]

theorem value_agreement {n1 n0 : ℕ} (direction : Direction)
    (observed : Outcome n1 n0) (psi : Positive) :
    BoschlooValidity.value direction psi observed =
      sSup (probability direction observed psi '' Set.Icc (0 : ℝ) 1) := by
  unfold BoschlooValidity.value NuisanceSupremum.value
  congr 1
  ext y
  constructor
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, probability_agreement direction observed psi hq⟩
  · rintro ⟨q, hq, rfl⟩
    exact ⟨q, hq, (probability_agreement direction observed psi hq).symm⟩

theorem directional_usc {n1 n0 : ℕ} (direction : Direction) (observed : Outcome n1 n0) :
    UpperSemicontinuous (fun psi : Positive => BoschlooValidity.value direction psi observed) := by
  simpa only [value_agreement] using Exactcis.Spine.usc_sSup_image_of_compact
    (probability direction observed) (probability_usc direction observed)

theorem accepted_closed_positive {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) :
    IsClosed {psi : Positive | BoschlooValidity.Accepted psi r observed} := by
  convert ((directional_usc .greater observed).isClosed_preimage r).inter
    ((directional_usc .less observed).isClosed_preimage r) using 1
  ext psi
  simp [BoschlooValidity.Accepted]

end ExactCIs.Unconditional.BoschlooTopology
