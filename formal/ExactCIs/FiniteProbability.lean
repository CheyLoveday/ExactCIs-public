import ExactCIs.Table
import Mathlib

/-! Finite exact-mass primitives used by later distribution modules. -/

namespace ExactCIs

/-- A finite nonnegative mass function whose listed support normalizes to one. -/
structure FiniteMass (α : Type) [DecidableEq α] where
  support : Finset α
  weight : α → ℝ
  nonnegative : ∀ x ∈ support, 0 ≤ weight x
  normalizes : ∑ x ∈ support, weight x = 1

namespace FiniteMass

variable {α : Type} [DecidableEq α]

/-- Exact mass of an event represented by a finite subset of the support. -/
def eventMass (mass : FiniteMass α) (event : Finset α) : ℝ :=
  ∑ x ∈ event, mass.weight x

theorem eventMass_nonnegative (mass : FiniteMass α) {event : Finset α}
    (contained : event ⊆ mass.support) : 0 ≤ mass.eventMass event := by
  unfold eventMass
  exact Finset.sum_nonneg fun x member => mass.nonnegative x (contained member)

theorem eventMass_le_one (mass : FiniteMass α) {event : Finset α}
    (contained : event ⊆ mass.support) : mass.eventMass event ≤ 1 := by
  unfold eventMass
  calc
    ∑ x ∈ event, mass.weight x ≤ ∑ x ∈ mass.support, mass.weight x :=
      Finset.sum_le_sum_of_subset_of_nonneg contained fun x member _ =>
        mass.nonnegative x member
    _ = 1 := mass.normalizes

theorem eventMass_mono (mass : FiniteMass α) {left right : Finset α}
    (included : left ⊆ right) (contained : right ⊆ mass.support) :
    mass.eventMass left ≤ mass.eventMass right := by
  unfold eventMass
  exact Finset.sum_le_sum_of_subset_of_nonneg included fun x member _ =>
    mass.nonnegative x (contained member)

theorem support_eventMass (mass : FiniteMass α) :
    mass.eventMass mass.support = 1 := mass.normalizes

end FiniteMass

end ExactCIs
