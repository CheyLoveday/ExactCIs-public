import ExactCIs.FNCH.PositiveNormalizer
import ExactCIs.FiniteProbability
import Mathlib

/-! A concrete finite FNCH probability mass for feasible margins. -/

namespace ExactCIs.FNCH.NormalizedMass

/-- At every feasible margin and positive finite effect, the FNCH weights
define a normalized finite probability mass. This is a real mathematical
construction; it does not assert floating-point runtime correspondence. -/
noncomputable def finiteMass (n1 n0 events : ℕ) (theta : ℝ)
    (margin : events ≤ n1 + n0) (theta_pos : 0 < theta) : FiniteMass ℕ := by
  let z : ℝ := ∑ k ∈ Support.valid n1 n0 events,
    Recurrence.unnormalizedWeight n1 n0 k (events - k) theta
  have z_pos : 0 < z := PositiveNormalizer.normalizer_pos n1 n0 events margin theta_pos
  have z_ne : z ≠ 0 := ne_of_gt z_pos
  refine {
    support := Support.valid n1 n0 events
    weight := fun k => Recurrence.unnormalizedWeight n1 n0 k (events - k) theta / z
    nonnegative := ?_
    normalizes := ?_
  }
  · intro k member
    exact div_nonneg
      (le_of_lt (PositiveNormalizer.weight_pos n1 n0 events theta_pos member))
      (le_of_lt z_pos)
  · change (∑ k ∈ Support.valid n1 n0 events,
        Recurrence.unnormalizedWeight n1 n0 k (events - k) theta / z) = 1
    rw [← Finset.sum_div]
    exact div_self z_ne

end ExactCIs.FNCH.NormalizedMass
