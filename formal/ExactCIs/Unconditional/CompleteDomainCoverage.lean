/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooValidity
import ExactCIs.Unconditional.Structural

/-! # Ideal coverage on the complete extended OR domain

The tagged infinity state and finite zero use direct structural fibres. Positive
finite effects use the actual Fisher masks and real-continuum nuisance suprema.
Returned-set coverage is conditional on a stated enclosure property, not on an
implementation theorem or a conditional-on-return probability assertion.
-/
namespace ExactCIs.Unconditional.CompleteDomainCoverage

open ProductBinomial

attribute [local instance] Classical.propDecidable

def Matches (effect : EffectState) (p1 p0 : ℝ) : Prop :=
  match effect with
  | .finite psi _ =>
      if psi = 0 then Structural.Fibre .zero p1 p0
      else p1 * (1 - p0) = psi * p0 * (1 - p1)
  | .positiveInfinity => Structural.Fibre .infinity p1 p0

def Accepted {n1 n0 : ℕ} (effect : EffectState) (r : ℝ) (observed : Outcome n1 n0) : Prop :=
  match effect with
  | .finite psi _ =>
      if psi = 0 then Structural.Accepted .zero r observed
      else BoschlooValidity.Accepted psi r observed
  | .positiveInfinity => Structural.Accepted .infinity r observed

/-- The finite cross-product null equation gives exactly the already proved
OR nuisance parameterization, including the all-zero and all-one corners. -/
theorem finite_link {psi p1 p0 : ℝ} (positive : 0 < psi)
    (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (equation : p1 * (1 - p0) = psi * p0 * (1 - p1)) : p1 = ORNull.p1 psi p0 := by
  apply (eq_div_iff (ORNull.denominator_pos positive second).ne').mpr
  unfold ORNull.denominator
  nlinarith [equation]

theorem ideal_rejection_bound {n1 n0 : ℕ} (effect : EffectState) {p1 p0 alpha : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (model : Matches effect p1 p0) (level : alpha ∈ Set.Icc (0 : ℝ) 1) :
    (mass n1 n0 p1 p0 first second).eventMass
      (Finset.univ.filter fun observed => ¬ Accepted effect (alpha / 2) observed) ≤ alpha := by
  have side_le_one : alpha / 2 ≤ 1 := by linarith [level.2]
  cases effect with
  | finite psi nonnegative =>
      by_cases zero : psi = 0
      · subst psi
        have fibre : Structural.Fibre .zero p1 p0 := by simpa [Matches] using model
        simp only [Accepted, ite_true]
        rw [Structural.rejection_mass_zero first second fibre side_le_one]
        exact level.1
      · have positive : 0 < psi := lt_of_le_of_ne nonnegative (Ne.symm zero)
        have equation : p1 * (1 - p0) = psi * p0 * (1 - p1) := by
          simpa only [Matches, if_neg zero] using model
        have link := finite_link positive second equation
        subst p1
        simpa only [Accepted, if_neg zero, ORNull.mass] using
          BoschlooValidity.alpha_rejection_bound (n1 := n1) (n0 := n0) positive second level.1
  | positiveInfinity =>
      have fibre : Structural.Fibre .infinity p1 p0 := model
      change (mass n1 n0 p1 p0 first second).eventMass
        (Finset.univ.filter fun o => ¬ Structural.Accepted .infinity (alpha / 2) o) ≤ alpha
      rw [Structural.rejection_mass_zero first second fibre side_le_one]
      exact level.1

theorem ideal_coverage {n1 n0 : ℕ} (effect : EffectState) {p1 p0 alpha : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (model : Matches effect p1 p0) (level : alpha ∈ Set.Icc (0 : ℝ) 1) :
    1 - alpha ≤ (mass n1 n0 p1 p0 first second).eventMass
      (Finset.univ.filter fun observed => Accepted effect (alpha / 2) observed) := by
  have rejection := ideal_rejection_bound (n1 := n1) (n0 := n0) effect first second model level
  have partition := Finset.sum_filter_add_sum_filter_not
    (Finset.univ : Finset (Outcome n1 n0))
    (fun observed => Accepted effect (alpha / 2) observed) (weight p1 p0)
  rw [weight_sum] at partition
  change _ ≤ ∑ o ∈ Finset.univ.filter (fun o => Accepted effect (alpha / 2) o), weight p1 p0 o
  change (∑ o ∈ Finset.univ.filter (fun o => ¬ Accepted effect (alpha / 2) o),
    weight p1 p0 o) ≤ alpha at rejection
  linarith

/-- A failed/refused observation has `none` and contributes no return-and-miss
event. The returned set may be an outward hull, but its containment is an
explicit hypothesis that a future global checker must establish. -/
theorem return_and_miss_bound {n1 n0 : ℕ} (effect : EffectState) {p1 p0 alpha : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (model : Matches effect p1 p0) (level : alpha ∈ Set.Icc (0 : ℝ) 1)
    (returned : Outcome n1 n0 → Option (Set EffectState))
    (encloses : ∀ observed enclosed, returned observed = some enclosed →
      ∀ tested, Accepted tested (alpha / 2) observed → tested ∈ enclosed) :
    (mass n1 n0 p1 p0 first second).eventMass
      (Finset.univ.filter fun observed =>
        ∃ enclosed, returned observed = some enclosed ∧ effect ∉ enclosed) ≤ alpha := by
  apply le_trans (FiniteMass.eventMass_mono _ ?_ (Finset.subset_univ _))
    (ideal_rejection_bound effect first second model level)
  intro observed h
  obtain ⟨enclosed, didReturn, missed⟩ := (Finset.mem_filter.mp h).2
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    fun accepted => missed (encloses observed enclosed didReturn effect accepted)⟩

theorem zero_level_accepted {n1 n0 : ℕ} (effect : EffectState) (observed : Outcome n1 n0) :
    Accepted effect 0 observed := by
  cases effect with
  | finite psi nonnegative =>
      by_cases zero : psi = 0
      · simpa only [Accepted, if_pos zero] using Structural.zero_level_accepted .zero observed
      · simpa only [Accepted, if_neg zero] using
          BoschlooValidity.zero_level_accepted (lt_of_le_of_ne nonnegative (Ne.symm zero)) observed
  | positiveInfinity => exact Structural.zero_level_accepted .infinity observed

end ExactCIs.Unconditional.CompleteDomainCoverage
