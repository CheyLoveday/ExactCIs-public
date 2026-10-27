/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SturmChainCertificate
import ExactCIs.Unconditional.SturmRootCount
import ExactCIs.Unconditional.AlgebraicCertificate

/-! # Rational root-count certificates with checked squarefree transport -/
namespace ExactCIs.Unconditional.RootCountCertificate

open RootCertificate PolynomialList SturmVariation SturmSequence SturmChainCertificate

structure Certificate where
  representative : Coefficients
  quotient : Coefficients
  powerQuotient : Coefficients
  exponent : ℕ
  bezoutLeft : Coefficients
  bezoutRight : Coefficients
  tail : List Coefficients
  quotients : List Coefficients
  last : ℚ
  deriving Repr

def bezoutCheck (s a b : Coefficients) : Bool :=
  identityCheck (add (mul a s) (mul b (derivative s))) [1]

def firstCheck (s : Coefficients) : List Coefficients → Bool
  | [] => true
  | d :: _ => identityCheck d (derivative s)

def check (h : Coefficients) (c : Certificate) : Bool :=
  AlgebraicCertificate.rootSetCheck h c.representative c.quotient c.powerQuotient c.exponent &&
  bezoutCheck c.representative c.bezoutLeft c.bezoutRight &&
  chainCheck (c.representative :: c.tail) c.quotients c.last &&
  firstCheck c.representative c.tail

def rationalVariation (ps : List Coefficients) (q : ℚ) : ℕ :=
  variations (ps.map (fun p => SignType.sign (value p q)))

def count (c : Certificate) (a b : ℚ) : ℕ :=
  rationalVariation (c.representative :: c.tail) a -
    rationalVariation (c.representative :: c.tail) b

theorem check_iff (h : Coefficients) (c : Certificate) : check h c = true ↔
    AlgebraicCertificate.rootSetCheck h c.representative c.quotient c.powerQuotient
      c.exponent = true ∧ bezoutCheck c.representative c.bezoutLeft c.bezoutRight = true ∧
      chainCheck (c.representative :: c.tail) c.quotients c.last = true ∧
      firstCheck c.representative c.tail = true := by
  simp only [check, Bool.and_eq_true, and_assoc]

theorem bezoutCheck_sound {s a b : Coefficients} (checked : bezoutCheck s a b = true) :
    (polynomial s).Separable := by
  have identity := (identityCheck_iff _ _).mp checked
  refine ⟨polynomial a, polynomial b, ?_⟩
  simpa only [polynomial_add, polynomial_mul, polynomial_derivative, polynomial,
    map_one, mul_zero, add_zero] using identity

theorem sign_ratCast (q : ℚ) : SignType.sign (q : ℝ) = SignType.sign q := by
  rcases lt_trichotomy q 0 with h | h | h
  · rw [sign_neg h, sign_neg (by exact_mod_cast h : (q : ℝ) < 0)]
  · subst q; simp
  · rw [sign_pos h, sign_pos (by exact_mod_cast h : (0 : ℝ) < (q : ℝ))]

theorem variation_coercion (ps : List Coefficients) (q : ℚ) :
    variationAt (ps.map eval) (q : ℝ) = rationalVariation ps q := by
  unfold variationAt rationalVariation
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro p _
  change SignType.sign (eval p (q : ℝ)) = _
  rw [← value_coercion, sign_ratCast]

noncomputable def realPolynomial (cs : Coefficients) : Polynomial ℝ :=
  (polynomial cs).map (Rat.castHom ℝ)

theorem realPolynomial_eval (cs : Coefficients) : (realPolynomial cs).eval = eval cs := by
  funext x
  simpa only [realPolynomial, Polynomial.eval_map] using polynomial_eval cs x

theorem realPolynomial_eval_apply (cs : Coefficients) (x : ℝ) :
    (realPolynomial cs).eval x = eval cs x := congrFun (realPolynomial_eval cs) x

theorem realPolynomial_derivative (cs : Coefficients) :
    realPolynomial (derivative cs) = (realPolynomial cs).derivative := by
  simp only [realPolynomial, polynomial_derivative, Polynomial.derivative_map]

/-- Every successful replay counts exactly all distinct roots in `(a,b]`. -/
theorem count_sound {h : Coefficients} {c : Certificate}
    (checked : check h c = true) {a b : ℚ} (order : a ≤ b) :
    count c a b = {x : ℝ | (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0}.ncard := by
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
    have empty : {x : ℝ | (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0} = ∅ := by
      ext x
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, hx⟩
      exact chain.2 x ((rootSet x).mp hx)
    simp [empty, count, ht, rationalVariation, variations, changesFrom]
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
      (ps.map eval) nonzero realChain (by exact_mod_cast order : (a : ℝ) ≤ (b : ℝ))
    rw [realPolynomial_eval, ← derivativeIdentity] at result
    change variationAt ((c.representative :: d :: ps).map eval) (a : ℝ) -
      variationAt ((c.representative :: d :: ps).map eval) (b : ℝ) = _ at result
    rw [variation_coercion, variation_coercion] at result
    have setIdentity : {x : ℝ | (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0} =
        ↑((realPolynomial c.representative).roots.toFinset.filter
          (fun x => (a : ℝ) < x ∧ x ≤ (b : ℝ))) := by
      ext x
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset,
        Polynomial.mem_roots nonzero, Polynomial.IsRoot, realPolynomial_eval_apply]
      rw [rootSet x]
      tauto
    rw [setIdentity, Set.ncard_coe_finset]
    simpa only [count, ht] using result

theorem roots_finite {h : Coefficients} {c : Certificate}
    (checked : check h c = true) : {x : ℝ | eval h x = 0}.Finite := by
  have checks := (check_iff h c).mp checked
  have rootSet := AlgebraicCertificate.rootSetCheck_sound checks.1
  have nonzero : realPolynomial c.representative ≠ 0 :=
    (bezoutCheck_sound checks.2.1).map.ne_zero
  have finite := Polynomial.finite_setOfPred_isRoot nonzero
  simpa only [Polynomial.IsRoot, realPolynomial_eval_apply, ← rootSet] using finite

theorem count_positive_iff {h : Coefficients} {c : Certificate}
    (checked : check h c = true) {a b : ℚ} (order : a ≤ b) :
    0 < count c a b ↔ ∃ x : ℝ, (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0 := by
  have finite : {x : ℝ | (a : ℝ) < x ∧ x ≤ (b : ℝ) ∧ eval h x = 0}.Finite :=
    (roots_finite checked).subset (fun _ hx => hx.2.2)
  rw [count_sound checked order, Set.ncard_pos finite]
  rfl

end ExactCIs.Unconditional.RootCountCertificate
