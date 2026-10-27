/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCountCompleteness

/-!
# Complete rational-polynomial closed-interval sign certificates

`some true` means an inclusive nonnegative witness exists; `some false` means
strict negativity on the whole interval. Invalid data returns `none`. Zero,
constant, endpoint, repeated and even roots use the same literal semantics.
-/
namespace ExactCIs.Unconditional.RootSignCertificate

open RootCertificate

def check (h : Coefficients) (a b : ℚ) (c : RootCountCertificate.Certificate) : Option Bool :=
  if a ≤ b then
    if 0 ≤ value h a then some true
    else if RootCountCertificate.check h c = true then
      some (decide (0 < RootCountCertificate.count c a b))
    else none
  else none

def Accepted (h : Coefficients) (a b : ℚ) : Prop :=
  ∃ x ∈ Set.Icc (a : ℝ) (b : ℝ), 0 ≤ eval h x

theorem negative_left_iff_root (h : Coefficients) (a b : ℚ)
    (negative : eval h (a : ℝ) < 0) :
    Accepted h a b ↔ ∃ x : ℝ, (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0 := by
  constructor
  · rintro ⟨x, hx, nonnegative⟩
    have ivt := intermediate_value_Icc hx.1 (continuous_eval h).continuousOn
      (show (0 : ℝ) ∈ Set.Icc (eval h a) (eval h x) from ⟨negative.le, nonnegative⟩)
    obtain ⟨y, hy, root⟩ := ivt
    refine ⟨y, lt_of_le_of_ne hy.1 ?_, hy.2.trans hx.2, root⟩
    intro equality
    rw [equality] at negative
    linarith
  · rintro ⟨x, hx, upper, root⟩
    exact ⟨x, ⟨hx.le, upper⟩, by rw [root]⟩

/-- Successful checking has exactly the requested real closed-interval semantics. -/
theorem checkerSound {h : Coefficients} {a b : ℚ} {c : RootCountCertificate.Certificate}
    {answer : Bool} (success : check h a b c = some answer) :
    a ≤ b ∧ (answer = true ↔ Accepted h a b) := by
  by_cases order : a ≤ b
  · by_cases left : 0 ≤ value h a
    · have answer_true : answer = true := by simpa [check, order, left] using success.symm
      have accepted : Accepted h a b := by
        refine ⟨a, ⟨le_rfl, by exact_mod_cast order⟩, ?_⟩
        rw [← value_coercion]
        exact_mod_cast left
      exact ⟨order, by simp [answer_true, accepted]⟩
    · by_cases certified : RootCountCertificate.check h c = true
      · have answer_eq : decide (0 < RootCountCertificate.count c a b) = answer := by
          simpa only [check, if_pos order, if_neg left, if_pos certified,
            Option.some.injEq] using success
        have negative : eval h (a : ℝ) < 0 := by
          rw [← value_coercion]
          exact_mod_cast lt_of_not_ge left
        refine ⟨order, ?_⟩
        rw [← answer_eq, decide_eq_true_eq]
        exact (RootCountCertificate.count_positive_iff certified order).trans
          (negative_left_iff_root h a b negative).symm
      · simp [check, order, left, certified] at success
  · simp [check, order] at success

/-- Every rational polynomial on every valid rational closed interval has a
finite accepted certificate. This is existence, not a budget or runtime claim. -/
theorem existsComplete (h : Coefficients) (a b : ℚ) (order : a ≤ b) :
    ∃ c : RootCountCertificate.Certificate, ∃ answer : Bool, check h a b c = some answer := by
  by_cases left : 0 ≤ value h a
  · exact ⟨⟨[], [], [], 0, [], [], [], [], 0⟩, true, by simp [check, order, left]⟩
  · have negative : eval h (a : ℝ) < 0 := by
      rw [← value_coercion]
      exact_mod_cast lt_of_not_ge left
    have nonzero : PolynomialList.polynomial h ≠ 0 := by
      intro zero
      have atLeft : eval h (a : ℝ) = 0 := by
        rw [← RootCountCertificate.realPolynomial_eval]
        simp [RootCountCertificate.realPolynomial, zero]
      rw [atLeft] at negative
      exact (lt_irrefl 0) negative
    obtain ⟨c, certified⟩ := RootCountCertificate.exists_certificate h nonzero
    exact ⟨c, decide (0 < RootCountCertificate.count c a b), by
      simp [check, order, left, certified]⟩

theorem rejected_strict {h : Coefficients} {a b : ℚ} {c : RootCountCertificate.Certificate}
    (rejected : check h a b c = some false) :
    ∀ x ∈ Set.Icc (a : ℝ) (b : ℝ), eval h x < 0 := by
  have hiff := (checkerSound rejected).2
  have none : ¬ Accepted h a b := by simpa using hiff.symm
  intro x hx
  exact lt_of_not_ge (fun h => none ⟨x, hx, h⟩)

end ExactCIs.Unconditional.RootSignCertificate
