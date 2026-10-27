import ExactCIs.Table
import Mathlib

/-! Fixed-margin support definitions shared by the FNCH recurrence. -/

namespace ExactCIs.FNCH.Support

/-- Feasible first-group cases at the stated row totals and event margin. -/
abbrev valid (n1 n0 events : ℕ) : Finset ℕ :=
  fixedMarginSupport n1 n0 events

theorem mem_valid_iff {n1 n0 events k : ℕ} :
    k ∈ valid n1 n0 events ↔
      k ≤ n1 ∧ events - n0 ≤ k ∧ k ≤ events :=
  mem_fixedMarginSupport_iff

/-- If the first group has size zero and the total event margin fits in the
second group, the conditional support is the singleton `{0}`. -/
theorem singleton_of_first_group_zero {n0 events : ℕ} (events_fit : events ≤ n0) :
    valid 0 n0 events = {0} := by
  ext k
  simp [valid, fixedMarginSupport, Nat.sub_eq_zero_of_le events_fit]
  omega

/-- The exact one-step criterion for an adjacent support point. -/
theorem successor_mem_iff {n1 n0 events k : ℕ}
    (member : k ∈ valid n1 n0 events) :
    k + 1 ∈ valid n1 n0 events ↔ k < n1 ∧ k < events :=
  succ_mem_fixedMarginSupport_iff member

end ExactCIs.FNCH.Support
