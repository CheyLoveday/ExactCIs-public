/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooOrdering
import ExactCIs.Unconditional.NuisanceSupremum

/-! # Actual finite-positive Boschloo p-values and error bounds

Each direction uses its own nuisance supremum. Validity is pointwise in every
real positive null effect and every real nuisance in the closed unit interval.
-/
namespace ExactCIs.Unconditional.BoschlooValidity

open ProductBinomial BoschlooOrdering

noncomputable def value {n1 n0 : ℕ} (direction : Direction) (psi : ℝ)
    (observed : Outcome n1 n0) : ℝ :=
  NuisanceSupremum.value (mask direction psi observed) psi

theorem mem_Icc {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0) :
    value direction psi observed ∈ Set.Icc (0 : ℝ) 1 :=
  NuisanceSupremum.mem_Icc positive _

theorem point_le {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (direction : Direction)
    (observed : Outcome n1 n0) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass (mask direction psi observed) ≤
      value direction psi observed :=
  NuisanceSupremum.point_le positive nuisance _

theorem full_value {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0)
    (one : statistic direction psi observed = 1) : value direction psi observed = 1 := by
  unfold value
  rw [full_mask_of_one positive direction observed one]
  exact NuisanceSupremum.full positive

theorem superuniform {n1 n0 : ℕ} {psi q cutoff : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (nonnegative : 0 ≤ cutoff)
    (direction : Direction) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter fun observed => value direction psi observed ≤ cutoff) ≤ cutoff := by
  classical
  apply le_trans (FiniteMass.eventMass_mono _ ?_ (Finset.subset_univ _))
    (fixed_nuisance_superuniform positive nuisance nonnegative direction)
  intro observed h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (point_le positive nuisance direction observed).trans (Finset.mem_filter.mp h).2⟩

theorem strict_rejection_bound {n1 n0 : ℕ} {psi q r : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (nonnegative : 0 ≤ r)
    (direction : Direction) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter fun observed => value direction psi observed < r) ≤ r := by
  classical
  apply le_trans (FiniteMass.eventMass_mono _ ?_ (Finset.subset_univ _))
    (superuniform positive nuisance nonnegative direction)
  intro observed h
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp h).2.le⟩

/-- A finite union bound with the support hypotheses exposed. -/
theorem event_union_le {α : Type} [DecidableEq α] (mass : FiniteMass α)
    (left right : Finset α) (contained : left ∩ right ⊆ mass.support) :
    mass.eventMass (left ∪ right) ≤ mass.eventMass left + mass.eventMass right := by
  have equality := Finset.sum_union_inter (s₁ := left) (s₂ := right) (f := mass.weight)
  have nonnegative := mass.eventMass_nonnegative contained
  unfold FiniteMass.eventMass at *
  linarith

def Accepted {n1 n0 : ℕ} (psi r : ℝ) (observed : Outcome n1 n0) : Prop :=
  r ≤ value .greater psi observed ∧ r ≤ value .less psi observed

attribute [local instance] Classical.propDecidable

theorem two_sided_rejection_bound {n1 n0 : ℕ} {psi q r : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (nonnegative : 0 ≤ r) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter fun observed => ¬ Accepted psi r observed) ≤ 2 * r := by
  classical
  have event_eq : (Finset.univ.filter fun observed : Outcome n1 n0 =>
      ¬ Accepted psi r observed) =
      (Finset.univ.filter fun observed => value .greater psi observed < r) ∪
      (Finset.univ.filter fun observed => value .less psi observed < r) := by
    ext observed
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Accepted,
      not_and_or, not_le]
  rw [event_eq]
  have union_le := event_union_le (ORNull.mass n1 n0 psi q positive nuisance)
    (Finset.univ.filter fun observed => value .greater psi observed < r)
    (Finset.univ.filter fun observed => value .less psi observed < r)
    (Finset.subset_univ _)
  have greater := strict_rejection_bound positive nuisance nonnegative (n1 := n1) (n0 := n0)
    Direction.greater
  have less := strict_rejection_bound positive nuisance nonnegative (n1 := n1) (n0 := n0)
    Direction.less
  linarith

theorem alpha_rejection_bound {n1 n0 : ℕ} {psi q alpha : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (nonnegative : 0 ≤ alpha) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter fun observed => ¬ Accepted psi (alpha / 2) observed) ≤ alpha := by
  have bound := two_sided_rejection_bound (n1 := n1) (n0 := n0) positive nuisance
    (div_nonneg nonnegative (by norm_num : (0 : ℝ) ≤ 2))
  linarith

theorem zero_level_accepted {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (observed : Outcome n1 n0) : Accepted psi 0 observed :=
  ⟨(mem_Icc positive .greater observed).1, (mem_Icc positive .less observed).1⟩

end ExactCIs.Unconditional.BoschlooValidity
