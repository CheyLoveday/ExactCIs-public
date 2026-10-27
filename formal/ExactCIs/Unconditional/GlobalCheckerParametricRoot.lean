/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.StratumSignReplay
import ExactCIs.Unconditional.GlobalCheckerOpenSign

/-! # Guarded polynomial Sturm certificates on a whole effect cell

Cleared denominators appear in scaled recurrences. Each scale must be
strictly positive throughout the open cell. Squarefree and Bezout transport use
nonzero effect factors, so no generic-degree or irreducibility assumption is
silently specialized at an exceptional effect.
-/
namespace ExactCIs.Unconditional.GlobalCheckerParametricRoot

open RootCertificate AlgebraicSpecialization SturmVariation Polynomial GlobalCheckerPoint

/-- The frozen payload uses one positive scale in each signed PRS step. -/
structure Step where
  quotient : Bivariate
  scale : Coefficients
  guard : GlobalCheckerOpenSign.Witness

def stepCheck (l u : Point) (p q r : Bivariate) (s : Step) : Bool :=
  StratumSignReplay.identityCheck (AlgebraicSpecialization.scale s.scale p)
    (add (mul q s.quotient) (AlgebraicSpecialization.scale [-1] r)) &&
  decide (s.guard.sign = 1) && GlobalCheckerOpenSign.check s.scale l u s.guard

theorem stepCheck_sound {l u : Point} {p q r : Bivariate} {s : Step}
    (checked : stepCheck l u p q r s = true) {x : ℝ}
    (inside : x ∈ Set.Ioo l.value u.value) {z : ℝ}
    (zero : (specialize x q).eval z = 0) (nonzero : (specialize x r).eval z ≠ 0) :
    (specialize x p).eval z * (specialize x r).eval z < 0 := by
  have parts : StratumSignReplay.identityCheck (AlgebraicSpecialization.scale s.scale p)
      (add (mul q s.quotient) (AlgebraicSpecialization.scale [-1] r)) = true ∧
      s.guard.sign = 1 ∧ GlobalCheckerOpenSign.check s.scale l u s.guard = true := by
    simpa only [stepCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  have positive := GlobalCheckerOpenSign.check_sound parts.2.2 inside
  rw [parts.2.1, sign_eq_one_iff] at positive
  have identity := congrArg (fun p : Polynomial ℝ => p.eval z)
    (StratumSignReplay.identityCheck_sound parts.1 x)
  simp only [specialize_scale, specialize_add, specialize_mul, Polynomial.eval_mul,
    Polynomial.eval_add, Polynomial.eval_C, RootCertificate.eval, Rat.cast_neg,
    Rat.cast_one, mul_zero, add_zero, neg_one_mul, zero, zero_mul, zero_add] at identity
  have hp : (specialize x p).eval z = -(specialize x r).eval z / eval s.scale x := by
    apply (eq_div_iff positive.ne').mpr
    simpa only [mul_comm] using identity
  rw [hp]
  have square := sq_pos_of_ne_zero nonzero
  have divide := div_pos square positive
  nlinarith [show (-(specialize x r).eval z / eval s.scale x) *
      (specialize x r).eval z = -((specialize x r).eval z ^ 2 / eval s.scale x) by ring]

def chainCheck (l u : Point) (last : Coefficients) (guard : GlobalCheckerOpenSign.Witness) :
    List Bivariate → List Step → Bool
  | [p], [] => StratumSignReplay.identityCheck p [last] &&
      GlobalCheckerOpenSign.nonzeroCheck last l u guard
  | [_, p], [] => StratumSignReplay.identityCheck p [last] &&
      GlobalCheckerOpenSign.nonzeroCheck last l u guard
  | p :: q :: r :: ps, s :: ss => stepCheck l u p q r s &&
      chainCheck l u last guard (q :: r :: ps) ss
  | _, _ => false

theorem terminal_chain {l u : Point} {last : Coefficients}
    {guard : GlobalCheckerOpenSign.Witness} {p : Bivariate}
    (identity : StratumSignReplay.identityCheck p [last] = true)
    (checked : GlobalCheckerOpenSign.nonzeroCheck last l u guard = true)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) : Chain [(specialize x p).eval] := by
  have hp := StratumSignReplay.identityCheck_sound identity x
  have hn := GlobalCheckerOpenSign.nonzeroCheck_sound checked inside
  refine ⟨(specialize x p).continuous, ?_⟩
  intro z
  rw [hp]
  simpa [specialize] using hn

theorem chainCheck_sound (l u : Point) (last : Coefficients)
    (guard : GlobalCheckerOpenSign.Witness) (ps : List Bivariate) (ss : List Step)
    (checked : chainCheck l u last guard ps ss = true)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) :
    Chain (ps.map fun p => (specialize x p).eval) := by
  cases ps with
  | nil => simp [chainCheck] at checked
  | cons p ps =>
    cases ps with
    | nil =>
      cases ss with
      | cons _ _ => simp [chainCheck] at checked
      | nil =>
        simp only [chainCheck, Bool.and_eq_true] at checked
        exact terminal_chain checked.1 checked.2 inside
    | cons q ps =>
      cases ps with
      | nil =>
        cases ss with
        | cons _ _ => simp [chainCheck] at checked
        | nil =>
          simp only [chainCheck, Bool.and_eq_true] at checked
          exact ⟨(specialize x p).continuous, terminal_chain checked.1 checked.2 inside, trivial⟩
      | cons r ps =>
        cases ss with
        | nil => simp [chainCheck] at checked
        | cons s ss =>
          have h : stepCheck l u p q r s = true ∧
              chainCheck l u last guard (q :: r :: ps) ss = true := by
            simpa only [chainCheck, Bool.and_eq_true] using checked
          have tail := chainCheck_sound l u last guard (q :: r :: ps) ss h.2 inside
          refine ⟨(specialize x p).continuous, tail, ?_⟩
          intro z hz
          exact stepCheck_sound h.1 inside hz (tail.no_common_root hz)
termination_by ps.length

structure Certificate where
  representative : Bivariate
  quotient : Bivariate
  powerQuotient : Bivariate
  exponent : ℕ
  rootScale : Coefficients
  powerScale : Coefficients
  rootGuard : GlobalCheckerOpenSign.Witness
  powerGuard : GlobalCheckerOpenSign.Witness
  bezoutLeft : Bivariate
  bezoutRight : Bivariate
  bezoutScale : Coefficients
  bezoutGuard : GlobalCheckerOpenSign.Witness
  tail : List Bivariate
  steps : List Step
  last : Coefficients
  lastGuard : GlobalCheckerOpenSign.Witness

def firstCheck (c : Certificate) : Bool :=
  match c.tail with
  | [] => true
  | p :: _ => StratumSignReplay.identityCheck p (derivative c.representative)

def check (l u : Point) (h : Bivariate) (c : Certificate) : Bool :=
  decide (0 < c.exponent) &&
  GlobalCheckerOpenSign.nonzeroCheck c.rootScale l u c.rootGuard &&
  GlobalCheckerOpenSign.nonzeroCheck c.powerScale l u c.powerGuard &&
  GlobalCheckerOpenSign.nonzeroCheck c.bezoutScale l u c.bezoutGuard &&
  StratumSignReplay.identityCheck (scale c.rootScale h) (mul c.representative c.quotient) &&
  StratumSignReplay.identityCheck (scale c.powerScale (power c.representative c.exponent))
    (mul h c.powerQuotient) &&
  StratumSignReplay.identityCheck
    (add (mul c.bezoutLeft c.representative) (mul c.bezoutRight (derivative c.representative)))
    [c.bezoutScale] &&
  chainCheck l u c.last c.lastGuard (c.representative :: c.tail) c.steps && firstCheck c

theorem checked_facts {l u : Point} {h : Bivariate} {c : Certificate}
    (checked : check l u h c = true) {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) :
    (∀ q : ℝ, (specialize x h).eval q = 0 ↔ (specialize x c.representative).eval q = 0) ∧
    (specialize x c.representative).Separable ∧
    Chain ((c.representative :: c.tail).map fun p => (specialize x p).eval) ∧
    firstCheck c = true := by
  simp only [check, Bool.and_eq_true] at checked
  have rootNonzero := GlobalCheckerOpenSign.nonzeroCheck_sound checked.1.1.1.1.1.1.1.2 inside
  have powerNonzero := GlobalCheckerOpenSign.nonzeroCheck_sound checked.1.1.1.1.1.1.2 inside
  have bezoutNonzero := GlobalCheckerOpenSign.nonzeroCheck_sound checked.1.1.1.1.1.2 inside
  have first := StratumSignReplay.identityCheck_sound checked.1.1.1.1.2 x
  have second := StratumSignReplay.identityCheck_sound checked.1.1.1.2 x
  have bezout := StratumSignReplay.identityCheck_sound checked.1.1.2 x
  simp only [specialize_scale, specialize_mul, specialize_power] at first second
  refine ⟨?_, ?_, chainCheck_sound _ _ _ _ _ _ checked.1.2 inside, checked.2⟩
  · intro q
    have hf := congrArg (fun p : Polynomial ℝ => p.eval q) first
    have hs := congrArg (fun p : Polynomial ℝ => p.eval q) second
    simp only [Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C] at hf hs
    constructor
    · intro zero
      rw [zero, zero_mul] at hs
      exact eq_zero_of_pow_eq_zero ((mul_eq_zero.mp hs).resolve_left powerNonzero)
    · intro zero
      rw [zero, zero_mul] at hf
      exact (mul_eq_zero.mp hf).resolve_left rootNonzero
  · have he : specialize x c.bezoutLeft * specialize x c.representative +
        specialize x c.bezoutRight * (specialize x c.representative).derivative =
        C (eval c.bezoutScale x) := by
      simpa [specialize_add, specialize_mul, specialize_derivative, specialize] using bezout
    refine ⟨C ((eval c.bezoutScale x)⁻¹) * specialize x c.bezoutLeft,
      C ((eval c.bezoutScale x)⁻¹) * specialize x c.bezoutRight, ?_⟩
    calc
      _ = C ((eval c.bezoutScale x)⁻¹) *
          (specialize x c.bezoutLeft * specialize x c.representative +
          specialize x c.bezoutRight * (specialize x c.representative).derivative) := by ring
      _ = 1 := by rw [he, ← map_mul]; simp [bezoutNonzero]

noncomputable def count (x : ℝ) (c : Certificate) (a b : ℝ) : ℕ :=
  variationAt ((c.representative :: c.tail).map fun p => (specialize x p).eval) a -
    variationAt ((c.representative :: c.tail).map fun p => (specialize x p).eval) b

/-- Distinct roots are counted with exact `(a,b]` ownership after specialization. -/
theorem count_sound {l u : Point} {h : Bivariate} {c : Certificate}
    (checked : check l u h c = true) {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value)
    {a b : ℝ} (ordered : a ≤ b) :
    count x c a b = {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0}.ncard := by
  classical
  obtain ⟨roots, separable, chain, first⟩ := checked_facts checked inside
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
      have hi := StratumSignReplay.identityCheck_sound
        (show StratumSignReplay.identityCheck p
          (AlgebraicSpecialization.derivative c.representative) = true by
          simpa only [firstCheck, ht] using first) x
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
theorem negative_left_acceptance {l u : Point} {h : Bivariate} {c : Certificate}
    (checked : check l u h c = true) {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value)
    {a b : ℝ} (ordered : a ≤ b) (negative : (specialize x h).eval a < 0) :
    (∃ q ∈ Set.Icc a b, 0 ≤ (specialize x h).eval q) ↔ 0 < count x c a b := by
  have facts := checked_facts checked inside
  have finite : {q : ℝ | a < q ∧ q ≤ b ∧ (specialize x h).eval q = 0}.Finite := by
    apply (Polynomial.finite_setOfPred_isRoot facts.2.1.ne_zero).subset
    intro q hq
    exact (facts.1 q).mp hq.2.2
  rw [count_sound checked inside ordered, Set.ncard_pos finite]
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


end ExactCIs.Unconditional.GlobalCheckerParametricRoot
