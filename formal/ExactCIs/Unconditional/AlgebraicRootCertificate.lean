/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicSpecialization
import ExactCIs.Unconditional.SturmRootCount

/-! # Signed root certificates specialized at one selected real effect

All identities are exact coefficient-wise rational checks modulo the definer.
The selected root and every inverse refer to the same real embedding. Checked
inverse realization supplies polynomial coefficients for rational functions.
This is sound replay, not a certificate-search or Python-execution theorem.
-/
namespace ExactCIs.Unconditional.AlgebraicRootCertificate

open RootCertificate AlgebraicSpecialization SturmVariation Polynomial

/-- Each terminal constant has an exact inverse modulo the definer. -/
def chainCheck (d last inverse quotient : Coefficients) :
    List Bivariate → List Bivariate → List Bivariate → Bool
  | [p], [], [w] => AlgebraicSpecialization.identityCheck d p [last] w &&
      AlgebraicCertificate.inverseCheck d last inverse quotient
  | [_, p], [], [w] => AlgebraicSpecialization.identityCheck d p [last] w &&
      AlgebraicCertificate.inverseCheck d last inverse quotient
  | p :: q :: r :: ps, quot :: qs, w :: ws =>
      AlgebraicSpecialization.identityCheck d p
        (AlgebraicSpecialization.add (AlgebraicSpecialization.mul q quot)
          (AlgebraicSpecialization.scale [-1] r)) w &&
      chainCheck d last inverse quotient (q :: r :: ps) qs ws
  | _, _, _ => false

theorem terminal_chain {d last inverse quotient : Coefficients} {p w : Bivariate}
    (identity : AlgebraicSpecialization.identityCheck d p [last] w = true)
    (guard : AlgebraicCertificate.inverseCheck d last inverse quotient = true)
    {x : ℝ} (root : RootCertificate.eval d x = 0) :
    Chain [(specialize x p).eval] := by
  have hp := AlgebraicSpecialization.identityCheck_sound identity root
  have hn := (AlgebraicCertificate.inverseCheck_sound guard root).1
  refine ⟨(specialize x p).continuous, ?_⟩
  intro q
  rw [hp]
  simpa [specialize] using hn

theorem chainCheck_sound (d last inverse quotient : Coefficients)
    (ps qs ws : List Bivariate)
    (checked : chainCheck d last inverse quotient ps qs ws = true)
    {x : ℝ} (root : RootCertificate.eval d x = 0) :
    Chain (ps.map fun p => (specialize x p).eval) := by
  cases ps with
  | nil => simp [chainCheck] at checked
  | cons p ps =>
    cases ps with
    | nil =>
      cases qs with
      | cons _ _ => simp [chainCheck] at checked
      | nil =>
        cases ws with
        | nil => simp [chainCheck] at checked
        | cons w ws =>
          cases ws with
          | cons _ _ => simp [chainCheck] at checked
          | nil =>
            simp only [chainCheck, Bool.and_eq_true] at checked
            exact terminal_chain checked.1 checked.2 root
    | cons q ps =>
      cases ps with
      | nil =>
        cases qs with
        | cons _ _ => simp [chainCheck] at checked
        | nil =>
          cases ws with
          | nil => simp [chainCheck] at checked
          | cons w ws =>
            cases ws with
            | cons _ _ => simp [chainCheck] at checked
            | nil =>
              simp only [chainCheck, Bool.and_eq_true] at checked
              exact ⟨(specialize x p).continuous,
                terminal_chain checked.1 checked.2 root, trivial⟩
      | cons r ps =>
        cases qs with
        | nil => simp [chainCheck] at checked
        | cons quot qs =>
          cases ws with
          | nil => simp [chainCheck] at checked
          | cons w ws =>
            have h : AlgebraicSpecialization.identityCheck d p
                (AlgebraicSpecialization.add (AlgebraicSpecialization.mul q quot)
                  (AlgebraicSpecialization.scale [-1] r)) w = true ∧
                chainCheck d last inverse quotient (q :: r :: ps) qs ws = true := by
              simpa only [chainCheck, Bool.and_eq_true] using checked
            have tail := chainCheck_sound d last inverse quotient (q :: r :: ps) qs ws h.2 root
            refine ⟨(specialize x p).continuous, tail, ?_⟩
            intro z hz
            have hr := tail.no_common_root hz
            have he := congrArg (fun p : Polynomial ℝ => p.eval z)
              (AlgebraicSpecialization.identityCheck_sound h.1 root)
            simp only [specialize_add, specialize_mul, specialize_scale, Polynomial.eval_add,
              Polynomial.eval_mul, Polynomial.eval_C, RootCertificate.eval, Rat.cast_neg,
              Rat.cast_one, mul_zero, add_zero, neg_one_mul, hz, zero_mul, zero_add] at he
            change (specialize x p).eval z * (specialize x r).eval z < 0
            change (specialize x r).eval z ≠ 0 at hr
            rw [he]
            nlinarith [sq_pos_of_ne_zero hr]
termination_by ps.length

structure Certificate where
  representative : Bivariate
  quotient : Bivariate
  powerQuotient : Bivariate
  exponent : ℕ
  rootWitness : Bivariate
  powerWitness : Bivariate
  bezoutLeft : Bivariate
  bezoutRight : Bivariate
  bezoutWitness : Bivariate
  tail : List Bivariate
  quotients : List Bivariate
  witnesses : List Bivariate
  last : Coefficients
  lastInverse : Coefficients
  lastQuotient : Coefficients
  derivativeWitness : Bivariate
  deriving Repr

def firstCheck (d : Coefficients) (c : Certificate) : Bool :=
  match c.tail with
  | [] => true
  | p :: _ => AlgebraicSpecialization.identityCheck d p
      (AlgebraicSpecialization.derivative c.representative) c.derivativeWitness

def check (d : Coefficients) (h : Bivariate) (c : Certificate) : Bool :=
  decide (0 < c.exponent) &&
  AlgebraicSpecialization.identityCheck d h
    (AlgebraicSpecialization.mul c.representative c.quotient) c.rootWitness &&
  AlgebraicSpecialization.identityCheck d
    (AlgebraicSpecialization.power c.representative c.exponent)
    (AlgebraicSpecialization.mul h c.powerQuotient) c.powerWitness &&
  AlgebraicSpecialization.identityCheck d
    (AlgebraicSpecialization.add (AlgebraicSpecialization.mul c.bezoutLeft c.representative)
      (AlgebraicSpecialization.mul c.bezoutRight
        (AlgebraicSpecialization.derivative c.representative))) [[1]] c.bezoutWitness &&
  chainCheck d c.last c.lastInverse c.lastQuotient
    (c.representative :: c.tail) c.quotients c.witnesses && firstCheck d c

/-- Semantic facts are derived from checked modular identities, not assumed. -/
theorem checked_facts {d : Coefficients} {h : Bivariate} {c : Certificate}
    (checked : check d h c = true) {x : ℝ} (root : RootCertificate.eval d x = 0) :
    (∀ q : ℝ, (specialize x h).eval q = 0 ↔ (specialize x c.representative).eval q = 0) ∧
    (specialize x c.representative).Separable ∧
    Chain ((c.representative :: c.tail).map fun p => (specialize x p).eval) ∧
    firstCheck d c = true := by
  simp only [check, Bool.and_eq_true] at checked
  have first := AlgebraicSpecialization.identityCheck_sound checked.1.1.1.1.2 root
  have second := AlgebraicSpecialization.identityCheck_sound checked.1.1.1.2 root
  have bezout := AlgebraicSpecialization.identityCheck_sound checked.1.1.2 root
  simp only [specialize_mul, specialize_power] at first second
  refine ⟨?_, ?_, chainCheck_sound _ _ _ _ _ _ _ checked.1.2 root, checked.2⟩
  · intro q
    have hf := congrArg (fun p : Polynomial ℝ => p.eval q) first
    have hs := congrArg (fun p : Polynomial ℝ => p.eval q) second
    simp only [Polynomial.eval_mul, Polynomial.eval_pow] at hf hs
    constructor
    · intro zero
      rw [zero, zero_mul] at hs
      exact eq_zero_of_pow_eq_zero hs
    · intro zero
      rw [hf, zero, zero_mul]
  · refine ⟨specialize x c.bezoutLeft, specialize x c.bezoutRight, ?_⟩
    simpa [specialize_add, specialize_mul, specialize_derivative, specialize,
      RootCertificate.eval] using bezout

noncomputable def count (x : ℝ) (c : Certificate) (a b : ℝ) : ℕ :=
  variationAt ((c.representative :: c.tail).map fun p => (specialize x p).eval) a -
    variationAt ((c.representative :: c.tail).map fun p => (specialize x p).eval) b

/-- Distinct roots are counted with exact `(a,b]` ownership after specialization. -/
theorem count_sound {d : Coefficients} {h : Bivariate} {c : Certificate}
    (checked : check d h c = true) {x : ℝ} (root : RootCertificate.eval d x = 0)
    {a b : ℝ} (ordered : a ≤ b) :
    count x c a b = {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0}.ncard := by
  classical
  obtain ⟨roots, separable, chain, first⟩ := checked_facts checked root
  cases ht : c.tail with
  | nil =>
    rw [ht] at chain
    change Continuous (specialize x c.representative).eval ∧
      ∀ q, (specialize x c.representative).eval q ≠ 0 at chain
    have empty : {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0} = ∅ := by
      ext q
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, _, hq⟩
      exact chain.2 q ((roots q).mp hq)
    simp [empty, count, ht, variationAt, variations, changesFrom]
  | cons p ps =>
    have derivative : specialize x p = (specialize x c.representative).derivative := by
      have hi := AlgebraicSpecialization.identityCheck_sound
        (show AlgebraicSpecialization.identityCheck d p
          (AlgebraicSpecialization.derivative c.representative) c.derivativeWitness = true by
          simpa only [firstCheck, ht] using first) root
      simpa only [specialize_derivative] using hi
    have realChain : Chain ((specialize x c.representative).eval ::
        (specialize x c.representative).derivative.eval ::
        ps.map fun p => (specialize x p).eval) := by
      simpa only [ht, List.map_cons, derivative] using chain
    have result := SturmRootCount.count_roots_Ioc (specialize x c.representative)
      (ps.map fun p => (specialize x p).eval) separable.ne_zero realChain ordered
    have eq : {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0} =
        ↑((specialize x c.representative).roots.toFinset.filter (fun q => a < q ∧ q ≤ b)) := by
      ext q
      simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_filter, Multiset.mem_toFinset,
        Polynomial.mem_roots separable.ne_zero, Polynomial.IsRoot]
      rw [roots q]
      tauto
    rw [eq, Set.ncard_coe_finset]
    simpa only [count, ht, List.map_cons, derivative] using result

/-- The original signed polynomial decides acceptance; a squarefree
representative contributes only its root set. -/
theorem negative_left_acceptance {d : Coefficients} {h : Bivariate} {c : Certificate}
    (checked : check d h c = true) {x : ℝ} (root : RootCertificate.eval d x = 0)
    {a b : ℝ} (ordered : a ≤ b) (negative : (specialize x h).eval a < 0) :
    (∃ q ∈ Set.Icc a b, 0 ≤ (specialize x h).eval q) ↔ 0 < count x c a b := by
  have facts := checked_facts checked root
  have finite : {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0}.Finite := by
    apply (Polynomial.finite_setOfPred_isRoot facts.2.1.ne_zero).subset
    intro q hq
    exact (facts.1 q).mp hq.2.2
  rw [count_sound checked root ordered, Set.ncard_pos finite]
  constructor
  · rintro ⟨q, hq, nonnegative⟩
    obtain ⟨z, hz, zero⟩ := intermediate_value_Icc hq.1
      (specialize x h).continuous.continuousOn
      (show (0 : ℝ) ∈ Set.Icc ((specialize x h).eval a) ((specialize x h).eval q)
        from ⟨negative.le, nonnegative⟩)
    refine ⟨z, lt_of_le_of_ne hz.1 ?_, hz.2.trans hq.2, zero⟩
    intro eq
    rw [eq] at negative
    linarith
  · rintro ⟨q, left, right, zero⟩
    exact ⟨q, ⟨left.le, right⟩, by rw [zero]⟩

end ExactCIs.Unconditional.AlgebraicRootCertificate
