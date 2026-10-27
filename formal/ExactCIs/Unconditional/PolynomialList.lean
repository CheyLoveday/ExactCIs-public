/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCertificate

/-! # Mathematical polynomial interpretation of the executable coefficient lists -/
namespace ExactCIs.Unconditional.PolynomialList

open RootCertificate Polynomial

noncomputable def polynomial : Coefficients → Polynomial ℚ
  | [] => 0
  | c :: cs => C c + X * polynomial cs

theorem coefficient (cs : Coefficients) (i : ℕ) :
    (polynomial cs).coeff i = cs.getD i 0 := by
  induction cs generalizing i with
  | nil => simp [polynomial]
  | cons c cs ih => cases i <;> simp [polynomial, ih, coeff_X_mul]

theorem polynomial_add (as bs : Coefficients) :
    polynomial (add as bs) = polynomial as + polynomial bs := by
  induction as generalizing bs with
  | nil => simp [add, polynomial]
  | cons a as ih =>
    cases bs with
    | nil => simp [add, polynomial]
    | cons b bs => simp [add, polynomial, ih]; ring

theorem polynomial_scale (c : ℚ) (as : Coefficients) :
    polynomial (scale c as) = C c * polynomial as := by
  induction as with
  | nil => simp [scale, polynomial]
  | cons a as ih =>
    change polynomial ((c * a) :: scale c as) = _
    rw [polynomial, ih, polynomial, map_mul]
    ring

theorem polynomial_mul (as bs : Coefficients) :
    polynomial (mul as bs) = polynomial as * polynomial bs := by
  induction as with
  | nil => simp [mul, polynomial]
  | cons a as ih =>
    rw [mul, polynomial_add, polynomial_scale, polynomial, ih, polynomial]
    simp only [map_zero, zero_add]
    ring

theorem polynomial_power (as : Coefficients) (n : ℕ) :
    polynomial (power as n) = polynomial as ^ n := by
  induction n with
  | zero => simp [power, polynomial]
  | succ n ih => simp [power, polynomial_mul, ih, pow_succ, mul_comm]

theorem polynomial_derivative (cs : Coefficients) :
    polynomial (RootCertificate.derivative cs) = (polynomial cs).derivative := by
  induction cs with
  | nil => simp [RootCertificate.derivative, polynomial]
  | cons c cs ih =>
    simp [RootCertificate.derivative, polynomial, polynomial_add, ih, derivative_mul]

theorem polynomial_eval (cs : Coefficients) (x : ℝ) :
    (polynomial cs).eval₂ (Rat.castHom ℝ) x = RootCertificate.eval cs x := by
  induction cs with
  | nil => simp [polynomial, RootCertificate.eval]
  | cons c cs ih => simp [polynomial, RootCertificate.eval, ih]

theorem zero_iff (cs : Coefficients) : polynomial cs = 0 ↔ ∀ c ∈ cs, c = 0 := by
  induction cs with
  | nil => simp [polynomial]
  | cons c cs ih =>
    constructor
    · intro h
      have head : c = 0 := by
        have hc := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
        simpa [polynomial] using hc
      have tail : polynomial cs = 0 := by
        apply Polynomial.ext
        intro i
        have hc := congrArg (fun p : Polynomial ℚ => p.coeff (i + 1)) h
        simpa [polynomial, coeff_X_mul] using hc
      simpa [head] using ih.mp tail
    · intro h
      have head := h c (by simp)
      have tail := ih.mpr (fun a ha => h a (by simp [ha]))
      simp [polynomial, head, tail]

/-- The rational-list identity test is both sound and complete, with trailing zeros. -/
theorem identityCheck_iff (as bs : Coefficients) :
    identityCheck as bs = true ↔ polynomial as = polynomial bs := by
  rw [identityCheck, List.all_eq_true]
  simp only [beq_iff_eq]
  rw [← zero_iff, polynomial_add, polynomial_scale]
  simp only [map_neg, map_one, neg_one_mul, ← sub_eq_add_neg, sub_eq_zero]

theorem exists_coefficients (p : Polynomial ℚ) : ∃ cs : Coefficients, polynomial cs = p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    obtain ⟨as, ha⟩ := hp
    obtain ⟨bs, hb⟩ := hq
    exact ⟨add as bs, by rw [polynomial_add, ha, hb]⟩
  | monomial n c =>
    refine ⟨mul (power [0, 1] n) [c], ?_⟩
    simp only [polynomial_mul, polynomial_power, polynomial, map_zero, map_one,
      mul_zero, add_zero, mul_one, zero_add]
    rw [mul_comm, C_mul_X_pow_eq_monomial]

end ExactCIs.Unconditional.PolynomialList
