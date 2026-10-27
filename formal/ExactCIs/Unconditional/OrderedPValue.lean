import ExactCIs.FiniteProbability
import Mathlib

/-! Finite inclusive principal-set p-values and their exact validity. -/

namespace ExactCIs.Unconditional.OrderedPValue

variable {α : Type} [DecidableEq α]

/-- The inclusive principal set of a finite statistic at the observed value. -/
noncomputable def principal (mass : FiniteMass α) (statistic : α → ℝ)
    (observation : α) : Finset α := by
  classical
  exact mass.support.filter fun candidate =>
    statistic candidate ≤ statistic observation

/-- Its exact finite-mass p-value, with equality included. -/
noncomputable def value (mass : FiniteMass α) (statistic : α → ℝ)
    (observation : α) : ℝ :=
  mass.eventMass (principal mass statistic observation)

/-- Exact equality is included: a supported observation belongs to its own
principal set. -/
theorem self_mem_principal (mass : FiniteMass α) (statistic : α → ℝ)
    {observation : α} (supported : observation ∈ mass.support) :
    observation ∈ principal mass statistic observation := by
  classical
  simp [principal, supported]

/-- For every nonnegative cutoff, an inclusive principal-set p-value is
super-uniform under its own finite mass. No continuity, grid, or asymptotic
approximation enters this statement. -/
theorem superuniform (mass : FiniteMass α) (statistic : α → ℝ)
    (cutoff : ℝ) (cutoff_nonnegative : 0 ≤ cutoff) :
    mass.eventMass
      (mass.support.filter fun observation =>
        value mass statistic observation ≤ cutoff) ≤ cutoff := by
  classical
  let event : Finset α := mass.support.filter fun observation =>
    value mass statistic observation ≤ cutoff
  change mass.eventMass event ≤ cutoff
  by_cases event_nonempty : event.Nonempty
  · obtain ⟨maximal, maximal_mem, maximal_score⟩ :=
      event.exists_max_image statistic event_nonempty
    have contained : event ⊆ principal mass statistic maximal := by
      intro observation observation_mem
      have in_support : observation ∈ mass.support :=
        (Finset.mem_filter.mp observation_mem).1
      change observation ∈ mass.support.filter fun candidate =>
        statistic candidate ≤ statistic maximal
      exact Finset.mem_filter.mpr
        ⟨in_support, maximal_score observation observation_mem⟩
    have principal_contained :
        principal mass statistic maximal ⊆ mass.support := by
      intro observation observation_mem
      change observation ∈ mass.support.filter
        (fun candidate => statistic candidate ≤ statistic maximal) at observation_mem
      exact (Finset.mem_filter.mp observation_mem).1
    have maximal_below : value mass statistic maximal ≤ cutoff :=
      (Finset.mem_filter.mp maximal_mem).2
    exact (mass.eventMass_mono contained principal_contained).trans maximal_below
  · have event_empty : event = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp event_nonempty
    rw [event_empty]
    simpa [FiniteMass.eventMass] using cutoff_nonnegative

end ExactCIs.Unconditional.OrderedPValue
