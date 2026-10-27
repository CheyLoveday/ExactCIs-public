import ExactCIs.FNCH.Support
import Mathlib

/-! Exact positive-ratio FNCH weights and their adjacent recurrence. -/

namespace ExactCIs.FNCH.Recurrence

/-- Exact unnormalised FNCH weight for first-group count `k` and second-group
count `l` at a positive odds ratio `theta`. -/
noncomputable def unnormalizedWeight (n1 n0 k l : ℕ) (theta : ℝ) : ℝ :=
  (n1.choose k : ℝ) * (n0.choose l : ℝ) * theta ^ k

theorem unnormalizedWeight_nonnegative (n1 n0 k l : ℕ) {theta : ℝ}
    (theta_nonnegative : 0 ≤ theta) :
    0 ≤ unnormalizedWeight n1 n0 k l theta := by
  unfold unnormalizedWeight
  positivity

/-- The first binomial-coefficient adjacent ratio, expressed over the reals. -/
theorem choose_succ_ratio (n k : ℕ) :
    (n.choose (k + 1) : ℝ) =
      (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ) := by
  have adjacent :
      (n.choose (k + 1) : ℝ) * ((k + 1 : ℕ) : ℝ) =
        (n.choose k : ℝ) * ((n - k : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n k
  field_simp
  exact adjacent

/-- The second binomial-coefficient adjacent ratio, whose denominator is
positive at a valid predecessor. -/
theorem choose_pred_ratio (n r : ℕ) (below : r < n) :
    (n.choose r : ℝ) =
      (n.choose (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) / ((n - r : ℕ) : ℝ) := by
  have adjacent :
      (n.choose (r + 1) : ℝ) * ((r + 1 : ℕ) : ℝ) =
        (n.choose r : ℝ) * ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.choose_succ_right_eq n r
  have denominator_positive : 0 < ((n - r : ℕ) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt below
  exact (eq_div_iff (ne_of_gt denominator_positive)).mpr adjacent.symm

/-- For an adjacent pair `(k, r + 1) -> (k + 1, r)`, exact weights satisfy

`w(k+1,r) = w(k,r+1) * (n1-k)/(k+1) * (r+1)/(n0-r) * theta`.

Substituting `r + 1 = m - k` gives the package FNCH recurrence
`w_theta(k+1) = w_theta(k) * ((n1-k)/(k+1)) *
((m-k)/(n0-m+k+1)) * theta`; the predecessor form avoids unsound truncated
natural subtraction in the formal statement. -/
theorem adjacentWeight (n1 n0 k r : ℕ) (theta : ℝ) (_first_below : k < n1)
    (second_below : r < n0) (_theta_positive : 0 < theta) :
    unnormalizedWeight n1 n0 (k + 1) r theta =
      unnormalizedWeight n1 n0 k (r + 1) theta *
        (((n1 - k : ℕ) : ℝ) / ((k + 1 : ℕ) : ℝ)) *
        (((r + 1 : ℕ) : ℝ) / ((n0 - r : ℕ) : ℝ)) * theta := by
  unfold unnormalizedWeight
  rw [choose_succ_ratio, choose_pred_ratio n0 r second_below, pow_succ]
  ring

end ExactCIs.FNCH.Recurrence
