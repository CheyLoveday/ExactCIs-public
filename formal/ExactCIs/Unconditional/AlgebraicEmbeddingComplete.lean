/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicEmbedding
import ExactCIs.Unconditional.RootCountCompleteness

/-! # Every real algebraic root has a checked rational isolator

The definer may be reducible and may have repeated roots. The zero polynomial
is excluded. Existence does not supply a resource bound or a wire parser.
-/
namespace ExactCIs.Unconditional.AlgebraicEmbedding

open RootCertificate

/-- A finite real set can be isolated at any one of its members by rational
endpoints. Both endpoints are outside the set, even for rational members. -/
theorem rational_isolator_within {s cell : Set ℝ} (finite : s.Finite)
    {x : ℝ} (member : x ∈ s) (open_cell : IsOpen cell) (in_cell : x ∈ cell) :
    ∃ l u : ℚ, (l : ℝ) < x ∧ x < (u : ℝ) ∧
      Set.Icc (l : ℝ) u ⊆ cell ∧
      ∀ y ∈ Set.Icc (l : ℝ) u, y ∈ s ↔ y = x := by
  have open_complement : IsOpen (s \ {x})ᶜ := finite.sdiff.isClosed.isOpen_compl
  have inside : x ∈ cell ∩ (s \ {x})ᶜ := ⟨in_cell, by simp⟩
  obtain ⟨a, b, bounds, neighborhood⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp ((open_cell.inter open_complement).mem_nhds inside)
  obtain ⟨l, al, lx⟩ := exists_rat_btwn bounds.1
  obtain ⟨u, xu, ub⟩ := exists_rat_btwn bounds.2
  have inclusion : Set.Icc (l : ℝ) u ⊆ Set.Ioo a b :=
    fun _ hy => ⟨al.trans_le hy.1, hy.2.trans_lt ub⟩
  refine ⟨l, u, lx, xu, fun _ hy => (neighborhood (inclusion hy)).1, ?_⟩
  intro y hy
  constructor
  · intro root
    by_contra different
    exact (neighborhood (inclusion hy)).2 ⟨root, different⟩
  · intro equality
    simpa only [equality] using member

theorem rational_isolator {s : Set ℝ} (finite : s.Finite) {x : ℝ} (member : x ∈ s) :
    ∃ l u : ℚ, (l : ℝ) < x ∧ x < (u : ℝ) ∧
      ∀ y ∈ Set.Icc (l : ℝ) u, y ∈ s ↔ y = x := by
  obtain ⟨l, u, lx, xu, _, isolate⟩ :=
    rational_isolator_within finite member isOpen_univ (Set.mem_univ x)
  exact ⟨l, u, lx, xu, isolate⟩

/-- Every root of every nonzero rational polynomial is selected by finite,
accepted root-count data. No separability/irreducibility of the input is needed. -/
theorem exists_checked_isolator_within (d : Coefficients)
    (nonzero : PolynomialList.polynomial d ≠ 0) {x : ℝ} (root : eval d x = 0)
    {cell : Set ℝ} (open_cell : IsOpen cell) (in_cell : x ∈ cell) :
    ∃ l u : ℚ, ∃ c : RootCountCertificate.Certificate,
      check d l u c = true ∧ x ∈ Set.Ioo (l : ℝ) u ∧ Set.Icc (l : ℝ) u ⊆ cell := by
  classical
  obtain ⟨c, certified⟩ := RootCountCertificate.exists_certificate d nonzero
  obtain ⟨l, u, lx, xu, subset, isolate⟩ :=
    rational_isolator_within (RootCountCertificate.roots_finite certified) root open_cell in_cell
  have order : l < u := by exact_mod_cast lx.trans xu
  have left_nonzero : value d l ≠ 0 := by
    intro zero
    have real_zero : eval d (l : ℝ) = 0 := by rw [← value_coercion, zero]; simp
    have equal := (isolate l ⟨le_rfl, by exact_mod_cast order.le⟩).mp real_zero
    exact lx.ne equal
  have right_nonzero : value d u ≠ 0 := by
    intro zero
    have real_zero : eval d (u : ℝ) = 0 := by rw [← value_coercion, zero]; simp
    have equal := (isolate u ⟨by exact_mod_cast order.le, le_rfl⟩).mp real_zero
    exact xu.ne equal.symm
  have singleton : {y : ℝ | (l : ℝ) < y ∧ y ≤ (u : ℝ) ∧ eval d y = 0} = {x} := by
    ext y
    constructor
    · rintro ⟨lower, upper, zero⟩
      exact (isolate y ⟨lower.le, upper⟩).mp zero
    · intro equal
      have equality : y = x := equal
      subst y
      exact ⟨lx, xu.le, root⟩
  have count : RootCountCertificate.count c l u = 1 := by
    rw [RootCountCertificate.count_sound certified order.le, singleton, Set.ncard_singleton]
  refine ⟨l, u, c, ?_, ⟨lx, xu⟩, subset⟩
  simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using
    (show l < u ∧ value d l ≠ 0 ∧ value d u ≠ 0 ∧
      RootCountCertificate.check d c = true ∧ RootCountCertificate.count c l u = 1 from
      ⟨order, left_nonzero, right_nonzero, certified, count⟩)

theorem exists_checked_isolator (d : Coefficients)
    (nonzero : PolynomialList.polynomial d ≠ 0) {x : ℝ} (root : eval d x = 0) :
    ∃ l u : ℚ, ∃ c : RootCountCertificate.Certificate,
      check d l u c = true ∧ x ∈ Set.Ioo (l : ℝ) u := by
  obtain ⟨l, u, c, checked, bounds, _⟩ :=
    exists_checked_isolator_within d nonzero root isOpen_univ (Set.mem_univ x)
  exact ⟨l, u, c, checked, bounds⟩

/-- Positive event isolators satisfy the lower-endpoint guard of the actual
algebraic decision checker, rather than only enclosing a positive root. -/
theorem exists_positive_checked_isolator (d : Coefficients)
    (nonzero : PolynomialList.polynomial d ≠ 0) {x : ℝ} (root : eval d x = 0)
    (positive : 0 < x) :
    ∃ l u : ℚ, ∃ c : RootCountCertificate.Certificate,
      0 < l ∧ check d l u c = true ∧ x ∈ Set.Ioo (l : ℝ) u := by
  obtain ⟨l, u, c, checked, bounds, subset⟩ :=
    exists_checked_isolator_within d nonzero root isOpen_Ioi positive
  have lower : 0 < (l : ℝ) := subset ⟨le_rfl, (bounds.1.trans bounds.2).le⟩
  exact ⟨l, u, c, by exact_mod_cast lower, checked, bounds⟩

end ExactCIs.Unconditional.AlgebraicEmbedding
