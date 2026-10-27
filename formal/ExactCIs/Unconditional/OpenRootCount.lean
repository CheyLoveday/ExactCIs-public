/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCountCertificate

/-! # Root counts at arbitrary real endpoints and the open-interval convention

The arithmetic chain remains rational data. Endpoint signs may subsequently be
replayed at rational values or exact selected algebraic embeddings.
-/
namespace ExactCIs.Unconditional.OpenRootCount

open RootCertificate PolynomialList SturmVariation SturmSequence SturmChainCertificate
open RootCountCertificate

/-- Every successful replay counts exactly all distinct roots in `(a,b]`. -/
theorem count_real_sound {h : Coefficients} {c : RootCountCertificate.Certificate}
    (checked : RootCountCertificate.check h c = true) {a b : ℝ} (order : a ≤ b) :
    SturmVariation.variationAt ((c.representative :: c.tail).map eval) a -
      SturmVariation.variationAt ((c.representative :: c.tail).map eval) b =
      {x : ℝ | a < x ∧ x ≤ b ∧ eval h x = 0}.ncard := by
  classical
  have checks : AlgebraicCertificate.rootSetCheck h c.representative c.quotient c.powerQuotient
      c.exponent = true ∧ bezoutCheck c.representative c.bezoutLeft c.bezoutRight = true ∧
      chainCheck (c.representative :: c.tail) c.quotients c.last = true ∧
      firstCheck c.representative c.tail = true := by
    simpa only [check, Bool.and_eq_true, and_assoc] using checked
  have rootSet := AlgebraicCertificate.rootSetCheck_sound checks.1
  have chain := chainCheck_sound _ _ _ checks.2.2.1
  have separable := bezoutCheck_sound checks.2.1
  cases ht : c.tail with
  | nil =>
    rw [ht] at chain
    change Continuous (eval c.representative) ∧ ∀ x, eval c.representative x ≠ 0 at chain
    have empty : {x : ℝ | a < x ∧ x ≤ b ∧ eval h x = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, hx⟩
      exact chain.2 x ((rootSet x).mp hx)
    simp [empty, SturmVariation.variationAt, variations, changesFrom]
  | cons d ps =>
    have first : identityCheck d (derivative c.representative) = true := by
      simpa only [ht, firstCheck] using checks.2.2.2
    have derivativeIdentity : eval d = (realPolynomial c.representative).derivative.eval := by
      calc
        eval d = eval (derivative c.representative) := funext (identityCheck_sound first)
        _ = (realPolynomial (derivative c.representative)).eval := (realPolynomial_eval _).symm
        _ = _ := congrArg (fun p : Polynomial ℝ => fun x => p.eval x)
          (realPolynomial_derivative _)
    have realChain : Chain ((realPolynomial c.representative).eval ::
        (realPolynomial c.representative).derivative.eval :: ps.map eval) := by
      simpa only [ht, List.map_cons, realPolynomial_eval, ← derivativeIdentity] using chain
    have nonzero : realPolynomial c.representative ≠ 0 := separable.map.ne_zero
    have result := SturmRootCount.count_roots_Ioc (realPolynomial c.representative)
      (ps.map eval) nonzero realChain order
    rw [realPolynomial_eval, ← derivativeIdentity] at result
    change variationAt ((c.representative :: d :: ps).map eval) a -
      variationAt ((c.representative :: d :: ps).map eval) b = _ at result
    have setIdentity : {x : ℝ | a < x ∧ x ≤ b ∧ eval h x = 0} =
        ↑((realPolynomial c.representative).roots.toFinset.filter
          (fun x => a < x ∧ x ≤ b)) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset,
        Polynomial.mem_roots nonzero, Polynomial.IsRoot, realPolynomial_eval_apply]
      rw [rootSet x]
      tauto
    rw [setIdentity, Set.ncard_coe_finset]
    simpa only [ht] using result

/-- The right endpoint contributes one distinct root, irrespective of multiplicity.
The left endpoint is already excluded by the Sturm convention. -/
theorem count_open_sound {h : Coefficients} {c : RootCountCertificate.Certificate}
    (checked : RootCountCertificate.check h c = true) {a b : ℝ} (order : a < b) :
    variationAt ((c.representative :: c.tail).map eval) a -
      variationAt ((c.representative :: c.tail).map eval) b -
        (if eval h b = 0 then 1 else 0) =
      {x : ℝ | a < x ∧ x < b ∧ eval h x = 0}.ncard := by
  classical
  rw [count_real_sound checked order.le]
  by_cases root : eval h b = 0
  · rw [if_pos root]
    have identity : {x : ℝ | a < x ∧ x < b ∧ eval h x = 0} =
        {x : ℝ | a < x ∧ x ≤ b ∧ eval h x = 0} \ {b} := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · intro hx; exact ⟨⟨hx.1, hx.2.1.le, hx.2.2⟩, hx.2.1.ne⟩
      · rintro ⟨hx, ne⟩; exact ⟨hx.1, lt_of_le_of_ne hx.2.1 ne, hx.2.2⟩
    have member : b ∈ {x : ℝ | a < x ∧ x ≤ b ∧ eval h x = 0} :=
      ⟨order, le_rfl, root⟩
    rw [identity, Set.ncard_sdiff_singleton_of_mem member]
  · rw [if_neg root, Nat.sub_zero]
    congr 1
    ext x
    constructor
    · rintro ⟨lower, upper, zero⟩
      refine ⟨lower, lt_of_le_of_ne upper ?_, zero⟩
      intro equality; exact root (equality ▸ zero)
    · rintro ⟨lower, upper, zero⟩; exact ⟨lower, upper.le, zero⟩

end ExactCIs.Unconditional.OpenRootCount
