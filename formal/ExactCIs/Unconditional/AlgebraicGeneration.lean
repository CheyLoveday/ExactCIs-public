/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ParametricGeneration
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.FieldTheory.Minpoly.Field

/-! # Complete modular identities at an algebraic real embedding

Generation chooses the minimal polynomial of the selected real number. An
arbitrary reducible input definer is not treated as defining a quotient field.
This file does not yet provide endpoint sign or complete decision packets.
-/
namespace ExactCIs.Unconditional.AlgebraicGeneration

open Polynomial AlgebraicSpecialization

noncomputable def definer (x : ℝ) : RootCertificate.Coefficients :=
  ParametricGeneration.coefficients (minpoly ℚ x)

theorem definer_spec (x : ℝ) : PolynomialList.polynomial (definer x) = minpoly ℚ x :=
  ParametricGeneration.coefficients_spec _

theorem definer_ne_zero {x : ℝ} (algebraic : IsIntegral ℚ x) :
    PolynomialList.polynomial (definer x) ≠ 0 := by
  rw [definer_spec]
  exact minpoly.ne_zero algebraic

theorem eval_eq_aeval (p : RootCertificate.Coefficients) (x : ℝ) :
    RootCertificate.eval p x = aeval x (PolynomialList.polynomial p) := by
  rw [← PolynomialList.polynomial_eval]
  rfl

theorem definer_root (x : ℝ) :
    RootCertificate.eval (definer x) x = 0 := by
  rw [eval_eq_aeval, definer_spec]
  exact minpoly.aeval ℚ x

theorem zero_check_complete {x : ℝ}
    (p : RootCertificate.Coefficients) (zero : RootCertificate.eval p x = 0) :
    ∃ quotient, AlgebraicCertificate.zeroCheck p (definer x) quotient = true := by
  obtain ⟨q, hq⟩ := minpoly.dvd ℚ x (by rwa [← eval_eq_aeval])
  obtain ⟨qs, encoded⟩ := PolynomialList.exists_coefficients q
  refine ⟨qs, (PolynomialList.identityCheck_iff _ _).mpr ?_⟩
  rw [PolynomialList.polynomial_mul, definer_spec, encoded]
  exact hq

theorem inverse_check_complete {x : ℝ} (algebraic : IsIntegral ℚ x)
    (p : RootCertificate.Coefficients) (nonzero : RootCertificate.eval p x ≠ 0) :
    ∃ inverse quotient,
      AlgebraicCertificate.inverseCheck (definer x) p inverse quotient = true := by
  have coprime : IsCoprime (PolynomialList.polynomial p) (minpoly ℚ x) := by
    apply IsCoprime.symm
    apply (minpoly.irreducible algebraic).coprime_iff_not_dvd.mpr
    intro divides
    exact nonzero ((eval_eq_aeval p x).trans ((minpoly.dvd_iff).mp divides))
  obtain ⟨a, b, hab⟩ := coprime
  obtain ⟨as, ha⟩ := PolynomialList.exists_coefficients a
  obtain ⟨bs, hb⟩ := PolynomialList.exists_coefficients (-b)
  refine ⟨as, bs, (PolynomialList.identityCheck_iff _ _).mpr ?_⟩
  simp only [PolynomialList.polynomial_mul, PolynomialList.polynomial_add,
    definer_spec, ha, hb, PolynomialList.polynomial, map_one, mul_zero, add_zero]
  calc
    PolynomialList.polynomial p * a = (a * PolynomialList.polynomial p +
      b * minpoly ℚ x) - b * minpoly ℚ x := by ring
    _ = _ := by rw [hab]; ring

theorem zero_rows_complete {x : ℝ}
    (ps : Bivariate) (zero : specialize x ps = 0) :
    ∃ witness, AlgebraicSpecialization.zeroCheck (definer x) ps witness = true := by
  induction ps with
  | nil => exact ⟨[], rfl⟩
  | cons p ps ih =>
    have head : RootCertificate.eval p x = 0 := by
      have h := congrArg (fun q : Polynomial ℝ => q.coeff 0) zero
      simpa [specialize] using h
    have tail : specialize x ps = 0 := by
      apply Polynomial.ext
      intro n
      have h := congrArg (fun q : Polynomial ℝ => q.coeff (n + 1)) zero
      simpa [specialize, coeff_X_mul] using h
    obtain ⟨q, hq⟩ := zero_check_complete p head
    obtain ⟨qs, hqs⟩ := ih tail
    exact ⟨q :: qs, by simp only [AlgebraicSpecialization.zeroCheck, hq, hqs, Bool.true_and]⟩

theorem identity_check_complete {x : ℝ}
    (ps qs : Bivariate) (equal : specialize x ps = specialize x qs) :
    ∃ witness, AlgebraicSpecialization.identityCheck (definer x) ps qs witness = true := by
  apply zero_rows_complete
  rw [specialize_add, specialize_scale, equal]
  simp [RootCertificate.eval]

/-- Every coefficient in Q(x) has a rational polynomial representative at the
selected algebraic embedding, without division by a possibly zero definer. -/
theorem coefficient_realization {x : ℝ} (algebraic : IsIntegral ℚ x)
    (c : IntermediateField.adjoin ℚ ({x} : Set ℝ)) :
    ∃ p : RootCertificate.Coefficients, RootCertificate.eval p x = (c : ℝ) := by
  have member : (c : ℝ) ∈ Algebra.adjoin ℚ ({x} : Set ℝ) := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic algebraic.isAlgebraic]
    exact c.property
  rw [Algebra.adjoin_singleton_eq_range_aeval] at member
  obtain ⟨p, hp⟩ := member
  obtain ⟨ps, hps⟩ := PolynomialList.exists_coefficients p
  exact ⟨ps, by rw [eval_eq_aeval, hps]; exact hp⟩

end ExactCIs.Unconditional.AlgebraicGeneration
