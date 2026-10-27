import ExactCIs.Numerics.BracketCertificate
import Mathlib

/-! The generic fixed-null interior-root reduction, before Boschloo specialisation. -/

namespace ExactCIs.Unconditional.InteriorRoot

/-- When both nuisance endpoints have strictly negative threshold values,
acceptance at any nuisance point is equivalent to an interior zero. A zero
witness includes tangency and repeated roots; this theorem does not assume a
grid, an argmax computation, or a simple root. The Boschloo full-mask and
structural branches must be handled before applying it. -/
theorem nonnegative_iff_interior_root {h : ℝ → ℝ}
    (continuous : ContinuousOn h (Set.Icc 0 1))
    (left_negative : h 0 < 0) (right_negative : h 1 < 0) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ h q) ↔
      ∃ q ∈ Set.Ioo (0 : ℝ) 1, h q = 0 := by
  constructor
  · rintro ⟨q, q_closed, q_nonnegative⟩
    have q_positive : 0 < q := by
      by_contra not_positive
      have q_zero : q = 0 := le_antisymm (le_of_not_gt not_positive) q_closed.1
      rw [q_zero] at q_nonnegative
      linarith
    have q_below_one : q < 1 := by
      by_contra not_below
      have q_one : q = 1 := le_antisymm q_closed.2 (le_of_not_gt not_below)
      rw [q_one] at q_nonnegative
      linarith
    let bracket : ExactCIs.Numerics.Bracket h := {
      left := 0
      right := q
      ordered := le_of_lt q_positive
      left_nonpositive := le_of_lt left_negative
      right_nonnegative := q_nonnegative
    }
    have continuous_bracket : ContinuousOn h (Set.Icc bracket.left bracket.right) := by
      apply continuous.mono
      intro x x_in
      exact ⟨x_in.1, x_in.2.trans (le_of_lt q_below_one)⟩
    obtain ⟨root, root_closed, root_zero⟩ := bracket.root_exists continuous_bracket
    have root_positive : 0 < root := by
      by_contra not_positive
      have at_zero : root = 0 := le_antisymm (le_of_not_gt not_positive) root_closed.1
      rw [at_zero] at root_zero
      linarith
    exact ⟨root, ⟨root_positive, lt_of_le_of_lt root_closed.2 q_below_one⟩, root_zero⟩
  · rintro ⟨q, q_open, q_zero⟩
    exact ⟨q, ⟨le_of_lt q_open.1, le_of_lt q_open.2⟩, by simp [q_zero]⟩

end ExactCIs.Unconditional.InteriorRoot
