/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicEmbeddingComplete
import ExactCIs.Unconditional.AlgebraicGeneration

/-! # Checked selected roots and strict rational refinements

Definers may be reducible or repeated. A checked open isolator, rather than
polynomial identity or a quotient-field assumption, selects the real value.
This is typed rational data after parsing, not a canonical byte parser.
-/
namespace ExactCIs.Unconditional.SelectedRoot

open RootCertificate

structure Root where
  definer : Coefficients
  lower : ℚ
  upper : ℚ
  certificate : RootCountCertificate.Certificate
  deriving Repr

def Root.check (a : Root) : Bool :=
  AlgebraicEmbedding.check a.definer a.lower a.upper a.certificate

def Root.Means (a : Root) (x : ℝ) : Prop :=
  x ∈ Set.Ioo (a.lower : ℝ) a.upper ∧ eval a.definer x = 0

theorem unique {a : Root} (checked : a.check = true) : ∃! x : ℝ, a.Means x :=
  AlgebraicEmbedding.check_sound checked

theorem same_value {a : Root} (checked : a.check = true) {x y : ℝ}
    (hx : a.Means x) (hy : a.Means y) : x = y := by
  obtain ⟨z, _, one⟩ := unique checked
  exact (one x hx).trans (one y hy).symm

theorem definer_nonzero {a : Root} (checked : a.check = true) :
    PolynomialList.polynomial a.definer ≠ 0 := by
  have parts : a.lower < a.upper ∧ value a.definer a.lower ≠ 0 ∧
      value a.definer a.upper ≠ 0 ∧
      RootCountCertificate.check a.definer a.certificate = true ∧
      RootCountCertificate.count a.certificate a.lower a.upper = 1 := by
    simpa only [Root.check, AlgebraicEmbedding.check, Bool.and_eq_true,
      decide_eq_true_eq, and_assoc] using checked
  intro zero
  have evaluated : eval a.definer (a.lower : ℝ) = 0 := by
    rw [← PolynomialList.polynomial_eval, zero]
    simp
  exact parts.2.1 (Rat.cast_eq_zero.mp ((value_coercion _ _).trans evaluated))

theorem integral {a : Root} (checked : a.check = true) {x : ℝ} (meaning : a.Means x) :
    IsIntegral ℚ x := by
  have algebraic : IsAlgebraic ℚ x :=
    ⟨PolynomialList.polynomial a.definer, definer_nonzero checked,
      by rw [← AlgebraicGeneration.eval_eq_aeval]; exact meaning.2⟩
  exact algebraic.isIntegral

structure Refinement where
  lower : ℚ
  upper : ℚ
  certificate : RootCountCertificate.Certificate
  deriving Repr

def Refinement.root (a : Root) (s : Refinement) : Root :=
  ⟨a.definer, s.lower, s.upper, s.certificate⟩

def Refinement.check (a : Root) (s : Refinement) : Bool :=
  (s.root a).check && decide (a.lower < s.lower ∧ s.upper < a.upper)

theorem refinement_sound {a : Root} {s : Refinement}
    (checked : s.check a = true) :
    (s.root a).check = true ∧ ∀ x, (s.root a).Means x → a.Means x := by
  have parts : (s.root a).check = true ∧ a.lower < s.lower ∧ s.upper < a.upper := by
    simpa only [Refinement.check, Bool.and_eq_true, decide_eq_true_eq] using checked
  refine ⟨parts.1, ?_⟩
  intro x meaning
  exact ⟨⟨(by exact_mod_cast parts.2.1 : (a.lower : ℝ) < s.lower).trans meaning.1.1,
    meaning.1.2.trans (by exact_mod_cast parts.2.2 : (s.upper : ℝ) < a.upper)⟩, meaning.2⟩

theorem refinement_preserves {a : Root} {s : Refinement}
    (base : a.check = true) (checked : s.check a = true) {x : ℝ} (meaning : a.Means x) :
    (s.root a).Means x := by
  obtain ⟨y, hy, _⟩ := unique (refinement_sound checked).1
  have same := same_value base meaning ((refinement_sound checked).2 y hy)
  exact same.symm ▸ hy

theorem exists_refinement_within {a : Root} (checked : a.check = true) {x : ℝ}
    (meaning : a.Means x) {cell : Set ℝ} (open_cell : IsOpen cell) (inside : x ∈ cell) :
    ∃ s : Refinement, s.check a = true ∧ (s.root a).Means x ∧
      Set.Icc (s.lower : ℝ) s.upper ⊆ cell := by
  obtain ⟨l, u, c, hc, bounds, subset⟩ := AlgebraicEmbedding.exists_checked_isolator_within
    a.definer (definer_nonzero checked) meaning.2
    (open_cell.inter isOpen_Ioo) ⟨inside, meaning.1⟩
  have left := (subset (show (l : ℝ) ∈ Set.Icc (l : ℝ) u from
    ⟨le_rfl, (bounds.1.trans bounds.2).le⟩)).2.1
  have right := (subset (show (u : ℝ) ∈ Set.Icc (l : ℝ) u from
    ⟨(bounds.1.trans bounds.2).le, le_rfl⟩)).2.2
  refine ⟨⟨l, u, c⟩, ?_, ⟨bounds, meaning.2⟩, fun y hy => (subset hy).1⟩
  simpa only [Refinement.check, Refinement.root, Root.check, hc, Bool.true_and,
    decide_eq_true_eq] using
    (show a.lower < l ∧ u < a.upper from ⟨by exact_mod_cast left, by exact_mod_cast right⟩)

end ExactCIs.Unconditional.SelectedRoot
