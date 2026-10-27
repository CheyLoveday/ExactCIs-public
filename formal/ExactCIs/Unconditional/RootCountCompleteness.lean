/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCountCertificate

/-! # Existence of finite checked root-count certificates for every nonzero input -/
namespace ExactCIs.Unconditional.RootCountCertificate

open RootCertificate PolynomialList SturmSequence SturmChainCertificate

theorem firstCheck_complete {s : Polynomial ℚ} {ps : List (Polynomial ℚ)}
    (prs : Remainders s s.derivative ps) {a : Coefficients} {tail : List Coefficients}
    (encoded : (a :: tail).map polynomial = ps) : firstCheck a tail = true := by
  cases tail with
  | nil => rfl
  | cons d tail =>
    apply (identityCheck_iff _ _).mpr
    rcases prs.shape with ⟨_, shape⟩ | ⟨rs, shape⟩
    · rw [shape] at encoded
      simp at encoded
    · rw [shape] at encoded
      simp only [List.map_cons, List.cons.injEq] at encoded
      rw [polynomial_derivative, encoded.1]
      exact encoded.2.1

/-- No resource or search assumption occurs in certificate existence. The
finite witness may be expensive; production budgets must still fail closed. -/
theorem exists_certificate (h : Coefficients) (nonzero : polynomial h ≠ 0) :
    ∃ c : Certificate, check h c = true := by
  obtain ⟨s, n, separable, exponent, divides, powerDivides⟩ :=
    exists_squarefree_representative (polynomial h) nonzero
  obtain ⟨ps, prs⟩ := exists_remainders s s.derivative separable
  obtain ⟨cs, encoded⟩ := exists_encoded_list ps
  obtain ⟨quotients, last, chain⟩ := chainCheck_complete prs cs encoded
  obtain ⟨rest, head⟩ := prs.head
  cases cs with
  | nil => rw [head] at encoded; simp at encoded
  | cons a tail =>
    have represented : polynomial a = s := by
      rw [head] at encoded
      exact (List.cons.inj encoded).1
    have first := firstCheck_complete prs encoded
    obtain ⟨quotient, quotientIdentity⟩ := divides
    obtain ⟨powerQuotient, powerIdentity⟩ := powerDivides
    obtain ⟨quo, quoIdentity⟩ := exists_coefficients quotient
    obtain ⟨pquo, pquoIdentity⟩ := exists_coefficients powerQuotient
    obtain ⟨bezoutLeft, bezoutRight, bezoutIdentity⟩ := separable
    obtain ⟨bl, blIdentity⟩ := exists_coefficients bezoutLeft
    obtain ⟨br, brIdentity⟩ := exists_coefficients bezoutRight
    have root : AlgebraicCertificate.rootSetCheck h a quo pquo n = true := by
      simp only [AlgebraicCertificate.rootSetCheck, Bool.and_eq_true, decide_eq_true_eq]
      refine ⟨⟨exponent, (identityCheck_iff _ _).mpr ?_⟩, (identityCheck_iff _ _).mpr ?_⟩
      · rw [polynomial_mul, represented, quoIdentity]
        exact quotientIdentity
      · rw [polynomial_power, polynomial_mul, represented, pquoIdentity]
        exact powerIdentity
    have bezout : bezoutCheck a bl br = true := by
      apply (identityCheck_iff _ _).mpr
      simpa only [polynomial_add, polynomial_mul, polynomial_derivative, represented,
        blIdentity, brIdentity, polynomial, map_one, mul_zero, add_zero] using bezoutIdentity
    exact ⟨⟨a, quo, pquo, n, bl, br, tail, quotients, last⟩,
      (check_iff _ _).mpr ⟨root, bezout, chain, first⟩⟩

end ExactCIs.Unconditional.RootCountCertificate
