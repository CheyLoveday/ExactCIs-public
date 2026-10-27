/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ProductBinomial

/-! # Direct structural OR endpoint support and inclusive decisions

U0 B.9's tuple order is (greater, less). The two structural fibres are unions
of boundary faces; no substitution into the finite-effect rational link occurs.
-/
namespace ExactCIs.Unconditional.Structural

open ProductBinomial

inductive Endpoint where
  | zero
  | infinity
  deriving DecidableEq

def Supported {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) : Prop :=
  match endpoint with
  | .zero => o.1.val = 0 ∨ o.2.val = n0
  | .infinity => o.2.val = 0 ∨ o.1.val = n1

instance {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) :
    Decidable (Supported endpoint o) := by
  cases endpoint <;> unfold Supported <;> infer_instance

def Fibre (endpoint : Endpoint) (p1 p0 : ℝ) : Prop :=
  match endpoint with
  | .zero => p1 = 0 ∨ p0 = 1
  | .infinity => p0 = 0 ∨ p1 = 1

def pair {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) : ℚ × ℚ :=
  if Supported endpoint o then (1, 1)
  else match endpoint with
  | .zero => (0, 1)
  | .infinity => (1, 0)

def Accepted {n1 n0 : ℕ} (endpoint : Endpoint) (r : ℝ) (o : Outcome n1 n0) : Prop :=
  r ≤ ((pair endpoint o).1 : ℝ) ∧ r ≤ ((pair endpoint o).2 : ℝ)

def check {n1 n0 : ℕ} (endpoint : Endpoint) (r : ℚ) (o : Outcome n1 n0) : Bool :=
  decide (r ≤ (pair endpoint o).1 ∧ r ≤ (pair endpoint o).2)

theorem check_iff {n1 n0 : ℕ} (endpoint : Endpoint) (r : ℚ) (o : Outcome n1 n0) :
    check endpoint r o = true ↔ Accepted endpoint (r : ℝ) o := by
  simp only [check, decide_eq_true_eq, Accepted]
  exact_mod_cast Iff.rfl

theorem supported_table_zero {n1 n0 : ℕ} (o : Outcome n1 n0) :
    Supported .zero o ↔ (toTable o).a = 0 ∨ (toTable o).d = 0 := by
  have := o.2.isLt
  simp only [Supported, toTable]
  omega

theorem supported_table_infinity {n1 n0 : ℕ} (o : Outcome n1 n0) :
    Supported .infinity o ↔ (toTable o).c = 0 ∨ (toTable o).b = 0 := by
  have := o.1.isLt
  simp only [Supported, toTable]
  omega

theorem pair_supported {n1 n0 : ℕ} {endpoint : Endpoint} {o : Outcome n1 n0}
    (supported : Supported endpoint o) : pair endpoint o = (1, 1) := by
  simp [pair, supported]

theorem pair_nonnegative {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) :
    (0 : ℚ) ≤ (pair endpoint o).1 ∧ (0 : ℚ) ≤ (pair endpoint o).2 := by
  by_cases h : Supported endpoint o <;> cases endpoint <;> simp [pair, h]

/-- This formula includes negative and zero levels as well as the ordinary
positive levels. No level-independent endpoint rejection is installed. -/
theorem accepted_iff {n1 n0 : ℕ} (endpoint : Endpoint) (r : ℝ) (o : Outcome n1 n0) :
    Accepted endpoint r o ↔ r ≤ 1 ∧ (r ≤ 0 ∨ Supported endpoint o) := by
  by_cases h : Supported endpoint o <;> cases endpoint <;> simp [Accepted, pair, h, and_comm]

theorem accepted_of_supported {n1 n0 : ℕ} {endpoint : Endpoint} {r : ℝ}
    (level : r ≤ 1) {o : Outcome n1 n0} (supported : Supported endpoint o) :
    Accepted endpoint r o :=
  (accepted_iff endpoint r o).mpr ⟨level, Or.inr supported⟩

theorem zero_level_accepted {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) :
    Accepted endpoint 0 o :=
  (accepted_iff endpoint 0 o).mpr ⟨zero_le_one, Or.inl le_rfl⟩

theorem positive_level_iff_supported {n1 n0 : ℕ} (endpoint : Endpoint) {r : ℝ}
    (level : r ∈ Set.Ioc (0 : ℝ) 1) (o : Outcome n1 n0) :
    Accepted endpoint r o ↔ Supported endpoint o := by
  simp only [accepted_iff, level.2, true_and, not_le.mpr level.1, false_or]

theorem unsupported_weight_zero {n1 n0 : ℕ} {endpoint : Endpoint} {p1 p0 : ℝ}
    (fibre : Fibre endpoint p1 p0) (o : Outcome n1 n0)
    (unsupported : ¬ Supported endpoint o) : weight p1 p0 o = 0 := by
  cases endpoint with
  | zero =>
      rcases fibre with first | second
      · rw [first]
        exact weight_first_zero p0 o (fun h => unsupported (Or.inl h))
      · rw [second]
        exact weight_second_one p1 o (fun h => unsupported (Or.inr h))
  | infinity =>
      rcases fibre with second | first
      · rw [second]
        exact weight_second_zero p1 o (fun h => unsupported (Or.inl h))
      · rw [first]
        exact weight_first_one p0 o (fun h => unsupported (Or.inr h))

theorem support_mass_one {n1 n0 : ℕ} {endpoint : Endpoint} {p1 p0 : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (fibre : Fibre endpoint p1 p0) :
    (mass n1 n0 p1 p0 first second).eventMass
      (Finset.univ.filter fun o => Supported endpoint o) = 1 := by
  change (∑ o ∈ Finset.univ.filter (fun o : Outcome n1 n0 => Supported endpoint o),
    weight p1 p0 o) = 1
  rw [← weight_sum n1 n0 p1 p0]
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro o _ absent
  exact unsupported_weight_zero fibre o (by simpa only [Finset.mem_filter, Finset.mem_univ,
    true_and] using absent)

attribute [local instance] Classical.propDecidable

theorem rejection_mass_zero {n1 n0 : ℕ} {endpoint : Endpoint} {p1 p0 r : ℝ}
    (first : p1 ∈ Set.Icc (0 : ℝ) 1) (second : p0 ∈ Set.Icc (0 : ℝ) 1)
    (fibre : Fibre endpoint p1 p0) (level : r ≤ 1) :
    (mass n1 n0 p1 p0 first second).eventMass
      (Finset.univ.filter fun o => ¬ Accepted endpoint r o) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro o rejected
  exact unsupported_weight_zero fibre o (fun h =>
    (Finset.mem_filter.mp rejected).2 (accepted_of_supported level h))

def swapEndpoint : Endpoint → Endpoint
  | .zero => .infinity
  | .infinity => .zero

theorem group_swap_supported {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) :
    Supported (swapEndpoint endpoint) o.swap ↔ Supported endpoint o := by
  cases endpoint <;> rfl

theorem group_swap_pair {n1 n0 : ℕ} (endpoint : Endpoint) (o : Outcome n1 n0) :
    pair (swapEndpoint endpoint) o.swap = (pair endpoint o).swap := by
  simp only [pair, group_swap_supported]
  by_cases h : Supported endpoint o
  · simp only [if_pos h]; rfl
  · simp only [if_neg h]; cases endpoint <;> rfl

end ExactCIs.Unconditional.Structural
