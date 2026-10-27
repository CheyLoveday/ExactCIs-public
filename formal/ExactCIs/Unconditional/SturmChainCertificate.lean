/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.PolynomialList
import ExactCIs.Unconditional.SturmSequence

/-! # Executable signed-chain checking, including existence of checked witnesses -/
namespace ExactCIs.Unconditional.SturmChainCertificate

open RootCertificate PolynomialList SturmVariation SturmSequence

def chainCheck : List Coefficients → List Coefficients → ℚ → Bool
  | [p], [], c => identityCheck p [c] && decide (c ≠ 0)
  | [_, q], [], c => identityCheck q [c] && decide (c ≠ 0)
  | p :: q :: r :: ps, quotient :: qs, c =>
      identityCheck p (add (mul q quotient) (scale (-1) r)) &&
        chainCheck (q :: r :: ps) qs c
  | _, _, _ => false

theorem constant_chain {p : Coefficients} {c : ℚ}
    (identity : identityCheck p [c] = true) (hc : c ≠ 0) : Chain [eval p] := by
  refine ⟨continuous_eval p, ?_⟩
  intro x
  rw [identityCheck_sound identity x]
  simpa [eval] using (Rat.cast_ne_zero.mpr hc : (c : ℝ) ≠ 0)

theorem chainCheck_sound (ps qs : List Coefficients) (c : ℚ)
    (checked : chainCheck ps qs c = true) : Chain (ps.map eval) := by
  cases ps with
  | nil => simp [chainCheck] at checked
  | cons p ps =>
    cases ps with
    | nil =>
      cases qs with
      | nil =>
        have h : identityCheck p [c] = true ∧ decide (c ≠ 0) = true := by
          simpa only [chainCheck, Bool.and_eq_true] using checked
        exact constant_chain h.1 (of_decide_eq_true h.2)
      | cons _ _ => simp [chainCheck] at checked
    | cons q ps =>
      cases ps with
      | nil =>
        cases qs with
        | nil =>
          have h : identityCheck q [c] = true ∧ decide (c ≠ 0) = true := by
            simpa only [chainCheck, Bool.and_eq_true] using checked
          exact ⟨continuous_eval p, constant_chain h.1 (of_decide_eq_true h.2), trivial⟩
        | cons _ _ => simp [chainCheck] at checked
      | cons r ps =>
        cases qs with
        | nil => simp [chainCheck] at checked
        | cons quotient qs =>
          have h : identityCheck p (add (mul q quotient) (scale (-1) r)) = true ∧
              chainCheck (q :: r :: ps) qs c = true := by
            simpa only [chainCheck, Bool.and_eq_true] using checked
          have tail := chainCheck_sound (q :: r :: ps) qs c h.2
          refine ⟨continuous_eval p, tail, ?_⟩
          intro x hq
          have hr := tail.no_common_root hq
          have identity := identityCheck_sound h.1 x
          simp only [eval_add, eval_mul, eval_scale, Rat.cast_neg, Rat.cast_one,
            hq, zero_mul, zero_add, neg_one_mul] at identity
          rw [identity]
          nlinarith [sq_pos_of_ne_zero hr]
termination_by ps.length

/-- Every exact PRS witness can be encoded and accepted by the rational checker. -/
theorem chainCheck_complete {p q : Polynomial ℚ} {ps : List (Polynomial ℚ)}
    (prs : Remainders p q ps) :
    ∀ cs : List Coefficients, cs.map polynomial = ps →
      ∃ qs c, chainCheck cs qs c = true := by
  induction prs with
  | constant c hc =>
    intro cs encoded
    cases cs with
    | nil => simp at encoded
    | cons a cs =>
      have parts : polynomial a = Polynomial.C c ∧ cs = [] := by
        simpa using encoded
      obtain ⟨ha, rfl⟩ := parts
      refine ⟨[], c, ?_⟩
      have identity : identityCheck a [c] = true :=
        (identityCheck_iff _ _).mpr (by simpa [polynomial] using ha)
      simp [chainCheck, identity, hc]
  | @step p q r ps quotient identity next ih =>
    intro cs encoded
    cases cs with
    | nil => simp at encoded
    | cons a cs =>
      have parts : polynomial a = p ∧ cs.map polynomial = ps := by simpa using encoded
      obtain ⟨qs, c, checked⟩ := ih cs parts.2
      cases cs with
      | nil => simp [chainCheck] at checked
      | cons b cs =>
        cases cs with
        | nil =>
          cases qs with
          | nil => exact ⟨[], c, checked⟩
          | cons _ _ => simp [chainCheck] at checked
        | cons d cs =>
          have heads : polynomial b = q ∧ polynomial d = r := by
            rcases next.shape with ⟨_, ht⟩ | ⟨tail, ht⟩
            · rw [ht] at parts
              simp at parts
            · rw [ht] at parts
              simp only [List.map_cons, List.cons.injEq] at parts
              exact ⟨parts.2.1, parts.2.2.1⟩
          obtain ⟨quot, hquot⟩ := exists_coefficients quotient
          have checkedIdentity : identityCheck a (add (mul b quot) (scale (-1) d)) = true := by
            apply (identityCheck_iff _ _).mpr
            rw [polynomial_add, polynomial_mul, polynomial_scale, parts.1, heads.1, heads.2, hquot]
            simpa [sub_eq_add_neg] using identity
          exact ⟨quot :: qs, c, by
            simpa only [chainCheck, Bool.and_eq_true] using And.intro checkedIdentity checked⟩

theorem exists_encoded_list (ps : List (Polynomial ℚ)) :
    ∃ cs : List Coefficients, cs.map polynomial = ps := by
  induction ps with
  | nil => exact ⟨[], rfl⟩
  | cons p ps ih =>
    obtain ⟨a, ha⟩ := exists_coefficients p
    obtain ⟨cs, hcs⟩ := ih
    exact ⟨a :: cs, by simp [ha, hcs]⟩

end ExactCIs.Unconditional.SturmChainCertificate
