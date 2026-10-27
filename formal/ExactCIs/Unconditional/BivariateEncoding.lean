/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.StratumSignReplay

/-! # Exact polynomial meaning and completeness of bivariate list identities

Outer coefficients are rational polynomials in effect; the outer variable is
nuisance. Trailing zero rows and trailing zero coefficients are permitted.
-/
namespace ExactCIs.Unconditional.BivariateEncoding

open Polynomial AlgebraicSpecialization

noncomputable def polynomial : Bivariate → Polynomial (Polynomial ℚ)
  | [] => 0
  | p :: ps => C (PolynomialList.polynomial p) + X * polynomial ps

theorem polynomial_add (ps qs : Bivariate) :
    polynomial (add ps qs) = polynomial ps + polynomial qs := by
  induction ps generalizing qs with
  | nil => simp [add, polynomial]
  | cons p ps ih =>
    cases qs with
    | nil => simp [add, polynomial]
    | cons q qs => simp [add, polynomial, PolynomialList.polynomial_add, ih]; ring

theorem polynomial_scale (d : RootCertificate.Coefficients) (ps : Bivariate) :
    polynomial (scale d ps) = C (PolynomialList.polynomial d) * polynomial ps := by
  induction ps with
  | nil => simp [scale, polynomial]
  | cons p ps ih =>
    change polynomial (RootCertificate.mul d p :: scale d ps) = _
    rw [polynomial, polynomial, PolynomialList.polynomial_mul, map_mul, ih]
    ring

theorem polynomial_mul (ps qs : Bivariate) :
    polynomial (mul ps qs) = polynomial ps * polynomial qs := by
  induction ps with
  | nil => simp [mul, polynomial]
  | cons p ps ih =>
    rw [mul, polynomial_add, polynomial_scale, polynomial, polynomial, ih]
    simp only [PolynomialList.polynomial, map_zero, zero_add]
    ring

theorem polynomial_power (ps : Bivariate) (n : ℕ) :
    polynomial (power ps n) = polynomial ps ^ n := by
  induction n with
  | zero => simp [power, polynomial, PolynomialList.polynomial]
  | succ n ih => simp [power, polynomial_mul, ih, pow_succ, mul_comm]

theorem polynomial_derivative (ps : Bivariate) :
    polynomial (AlgebraicSpecialization.derivative ps) = (polynomial ps).derivative := by
  induction ps with
  | nil => simp [AlgebraicSpecialization.derivative, polynomial]
  | cons p ps ih =>
    simp [AlgebraicSpecialization.derivative, polynomial_add, polynomial, ih,
      Polynomial.derivative_mul, PolynomialList.polynomial]

theorem exists_bivariate (p : Polynomial (Polynomial ℚ)) :
    ∃ ps : Bivariate, polynomial ps = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨ps, hps⟩ := hp
    obtain ⟨qs, hqs⟩ := hq
    exact ⟨add ps qs, by rw [polynomial_add, hps, hqs]⟩
  | monomial n c =>
    obtain ⟨cs, hcs⟩ := PolynomialList.exists_coefficients c
    refine ⟨mul (power [[], [1]] n) [cs], ?_⟩
    simp only [polynomial_mul, polynomial_power, polynomial, PolynomialList.polynomial,
      map_zero, map_one, mul_zero, add_zero, mul_one, zero_add, hcs]
    rw [mul_comm, C_mul_X_pow_eq_monomial]

theorem zeroCheck_complete (ps : Bivariate) (zero : polynomial ps = 0) :
    AlgebraicSpecialization.zeroCheck [] ps (List.replicate ps.length []) = true := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    have head : PolynomialList.polynomial p = 0 := by
      have h := congrArg (fun q : Polynomial (Polynomial ℚ) => q.coeff 0) zero
      simpa [polynomial] using h
    have tail : polynomial ps = 0 := by
      apply Polynomial.ext
      intro n
      have h := congrArg (fun q : Polynomial (Polynomial ℚ) => q.coeff (n + 1)) zero
      simpa [polynomial, coeff_X_mul] using h
    have hc : AlgebraicCertificate.zeroCheck p [] [] = true := by
      apply (PolynomialList.identityCheck_iff _ _).mpr
      simpa [PolynomialList.polynomial_mul, PolynomialList.polynomial] using head
    simp only [List.length_cons, List.replicate_succ, AlgebraicSpecialization.zeroCheck,
      hc, ih tail, Bool.true_and]

/-- The actual executable bivariate identity test accepts every exact identity. -/
theorem identityCheck_complete (ps qs : Bivariate) (equal : polynomial ps = polynomial qs) :
    StratumSignReplay.identityCheck ps qs = true := by
  apply zeroCheck_complete
  rw [polynomial_add, polynomial_scale, equal]
  simp [PolynomialList.polynomial]

theorem specialize_eq_map (ps : Bivariate) (x : ℝ) :
    specialize x ps = (polynomial ps).map (Polynomial.eval₂RingHom (Rat.castHom ℝ) x) := by
  induction ps with
  | nil => simp [specialize, polynomial]
  | cons p ps ih =>
    simp [specialize, polynomial, PolynomialList.polynomial_eval, ih]

end ExactCIs.Unconditional.BivariateEncoding
