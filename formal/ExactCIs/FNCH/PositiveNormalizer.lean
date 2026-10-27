import ExactCIs.FNCH.Recurrence
import Mathlib

/-! Positive FNCH normalisation on every feasible fixed-margin fibre. -/

namespace ExactCIs.FNCH.PositiveNormalizer

/-- A feasible event margin always has a conditional support point, including
the two degenerate margins. -/
theorem valid_nonempty (n1 n0 events : ℕ) (margin : events ≤ n1 + n0) :
    (Support.valid n1 n0 events).Nonempty := by
  refine ⟨events - n0, ?_⟩
  apply Support.mem_valid_iff.mpr
  constructor
  · omega
  constructor
  · exact le_refl _
  · omega

/-- Every listed FNCH weight is strictly positive at a positive effect. -/
theorem weight_pos (n1 n0 events : ℕ) {k : ℕ} {theta : ℝ}
    (theta_pos : 0 < theta) (member : k ∈ Support.valid n1 n0 events) :
    0 < Recurrence.unnormalizedWeight n1 n0 k (events - k) theta := by
  have bounds := Support.mem_valid_iff.mp member
  have second_bound : events - k ≤ n0 := by omega
  have first_choose : 0 < (n1.choose k : ℝ) := by
    exact_mod_cast Nat.choose_pos bounds.1
  have second_choose : 0 < (n0.choose (events - k) : ℝ) := by
    exact_mod_cast Nat.choose_pos second_bound
  unfold Recurrence.unnormalizedWeight
  exact mul_pos (mul_pos first_choose second_choose) (pow_pos theta_pos _)

/-- The finite FNCH denominator is positive; no unproved `Z ≠ 0`
assumption is needed on a valid margin and positive effect. -/
theorem normalizer_pos (n1 n0 events : ℕ) {theta : ℝ}
    (margin : events ≤ n1 + n0) (theta_pos : 0 < theta) :
    0 < ∑ k ∈ Support.valid n1 n0 events,
      Recurrence.unnormalizedWeight n1 n0 k (events - k) theta := by
  apply Finset.sum_pos
  · intro k member
    exact weight_pos n1 n0 events theta_pos member
  · exact valid_nonempty n1 n0 events margin

end ExactCIs.FNCH.PositiveNormalizer
