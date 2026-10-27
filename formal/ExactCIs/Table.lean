import Mathlib

/-! Canonical two-by-two table orientation and fixed-margin support facts. -/

namespace ExactCIs

/-- The public table orientation: exposed cases, exposed non-cases, unexposed
cases, then unexposed non-cases. -/
structure Table where
  a : ℕ
  b : ℕ
  c : ℕ
  d : ℕ
  deriving Repr

namespace Table

/-- Size of the first (exposed) group. -/
def n1 (table : Table) : ℕ := table.a + table.b

/-- Size of the second (unexposed) group. -/
def n0 (table : Table) : ℕ := table.c + table.d

/-- Total number of outcome-positive observations. -/
def events (table : Table) : ℕ := table.a + table.c

/-- Total sample size. -/
def total (table : Table) : ℕ := table.n1 + table.n0

theorem total_eq_cells (table : Table) :
    table.total = table.a + table.b + table.c + table.d := by
  simp [total, n1, n0, Nat.add_assoc]

theorem events_le_total (table : Table) : table.events ≤ table.total := by
  simp [events, total, n1, n0]
  omega

end Table

/-- An effect value is either finite and nonnegative or the tagged positive
infinity structural state. -/
inductive EffectState where
  | finite (value : ℝ) (nonnegative : 0 ≤ value)
  | positiveInfinity

namespace EffectState

/-- Whether an effect is represented by a finite real value. -/
def IsFinite : EffectState → Prop
  | .finite _ _ => True
  | .positiveInfinity => False

theorem finite_isFinite (value : ℝ) (nonnegative : 0 ≤ value) :
    IsFinite (.finite value nonnegative) := by
  trivial

theorem positiveInfinity_not_isFinite : ¬ IsFinite .positiveInfinity := by
  simp [IsFinite]

theorem finite_nonnegative (value : ℝ) (nonnegative : 0 ≤ value) :
    0 ≤ value := nonnegative

end EffectState

/-- Feasible exposed-case counts at fixed row totals and fixed total events. -/
def fixedMarginSupport (n1 n0 events : ℕ) : Finset ℕ :=
  (Finset.range (n1 + 1)).filter fun k => events - n0 ≤ k ∧ k ≤ events

theorem mem_fixedMarginSupport_iff {n1 n0 events k : ℕ} :
    k ∈ fixedMarginSupport n1 n0 events ↔
      k ≤ n1 ∧ events - n0 ≤ k ∧ k ≤ events := by
  simp [fixedMarginSupport, and_left_comm]

theorem fixedMarginSupport_bounded_first_group {n1 n0 events k : ℕ}
    (member : k ∈ fixedMarginSupport n1 n0 events) : k ≤ n1 :=
  (mem_fixedMarginSupport_iff.mp member).1

theorem fixedMarginSupport_bounded_events {n1 n0 events k : ℕ}
    (member : k ∈ fixedMarginSupport n1 n0 events) : k ≤ events :=
  (mem_fixedMarginSupport_iff.mp member).2.2

/-- A valid support point has a valid successor exactly before both upper
bounds. This is the adjacency premise used by the FNCH recurrence. -/
theorem succ_mem_fixedMarginSupport_iff {n1 n0 events k : ℕ}
    (member : k ∈ fixedMarginSupport n1 n0 events) :
    k + 1 ∈ fixedMarginSupport n1 n0 events ↔ k < n1 ∧ k < events := by
  constructor
  · intro successor
    have bounds := mem_fixedMarginSupport_iff.mp successor
    omega
  · rintro ⟨below_n1, below_events⟩
    have bounds := mem_fixedMarginSupport_iff.mp member
    apply mem_fixedMarginSupport_iff.mpr
    constructor
    · omega
    constructor <;> omega

end ExactCIs
