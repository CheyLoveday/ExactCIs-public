/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerOrder
import ExactCIs.Unconditional.CompactPolynomial
import ExactCIs.Unconditional.RootSignCertificate
import ExactCIs.Unconditional.BoschlooEndpoints

/-! # Actual compact rational/algebraic singleton decisions

Every point owns its inclusive comparison mask. Algebraic decisions use the
checked selected root and the actual transformed threshold polynomial; no
neighbouring open-cell mask is reused.
-/
namespace ExactCIs.Unconditional.GlobalCheckerPointDecision

open RootCertificate AlgebraicSpecialization ProductBinomial BoschlooOrdering
open GlobalCheckerPoint EffectCoordinate SturmVariation

def index {n1 n0 : ℕ} (o : Outcome n1 n0) : ℕ := o.1.val * (n0 + 1) + o.2.val

def witness {n1 n0 : ℕ} (ordering : List SignWitness) (o : Outcome n1 n0) : SignWitness :=
  ordering[index o]?.getD .rational

def orderingSign {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ordering : List SignWitness) (o : Outcome n1 n0) : SignType :=
  (GlobalCheckerPoint.sign (CompactPolynomial.comparison dir o observed)
    p (witness ordering o)).getD 0

def certifiedMask {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ordering : List SignWitness) : Finset (Outcome n1 n0) :=
  Finset.univ.filter fun o => orderingSign dir observed p ordering o ≠ 1

def orderingCheck {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ordering : List SignWitness) : Bool :=
  decide (ordering.length = (n1 + 1) * (n0 + 1)) &&
    decide (∀ o : Outcome n1 n0, (GlobalCheckerPoint.sign
      (CompactPolynomial.comparison dir o observed) p (witness ordering o)).isSome = true)

theorem ordering_sound {n1 n0 : ℕ} {dir : Direction} {observed : Outcome n1 n0}
    {p : Point} {ordering : List SignWitness}
    (checked : orderingCheck dir observed p ordering = true)
    (domain : p.value ∈ Set.Ioo (0 : ℝ) 1) :
    certifiedMask dir observed p ordering = mask dir (beta p.value) observed := by
  classical
  ext o
  have checks := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2
  have hs := sign_getD_sound (checks o)
  rw [CompactPolynomial.comparison_sign dir o observed domain] at hs
  simp only [certifiedMask, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ParametricPolynomial.mask_iff
    (show 0 < beta p.value from div_pos domain.1 (sub_pos.mpr domain.2))]
  change (GlobalCheckerPoint.sign (CompactPolynomial.comparison dir o observed)
    p (witness ordering o)).getD 0 ≠ 1 ↔
    eval (ParametricPolynomial.comparison dir o observed) (beta p.value) ≤ 0
  rw [← hs]
  simp only [ne_eq, sign_eq_one_iff, not_lt]

def specializeRational (x : ℚ) (p : Bivariate) : Coefficients :=
  p.map (fun c => RootCertificate.value c x)

theorem specializeRational_eval (x : ℚ) (p : Bivariate) (q : ℝ) :
    eval (specializeRational x p) q = (specialize (x : ℝ) p).eval q := by
  induction p with
  | nil => simp [specializeRational, eval, specialize]
  | cons c cs ih =>
    simp only [specializeRational, List.map_cons, eval, specialize,
      Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X,
      value_coercion]
    simpa only [specializeRational] using congrArg (fun y => eval c (x : ℝ) + q * y) ih

structure AlgebraicBranch where
  original : SignWitness
  root : AlgebraicRootCertificate.Certificate
  left : List SignWitness
  right : List SignWitness

def algebraicCheck (a : SelectedRoot.Root) (h : Bivariate) (c : AlgebraicBranch) : Option Bool := do
  if a.check && AlgebraicRootCertificate.check a.definer h c.root then
    if GlobalCheckerPoint.sign (AlgebraicSignReplay.atRational h 0)
        (.algebraic a) c.original = some (-1) then
      let left ← GlobalCheckerPoint.signs (.algebraic a)
        ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 0)
        c.left
      let right ← GlobalCheckerPoint.signs (.algebraic a)
        ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 1)
        c.right
      pure (decide (0 < variations left - variations right))
    else none
  else none

theorem algebraicCheck_sound {a : SelectedRoot.Root} {h : Bivariate}
    {c : AlgebraicBranch} {answer : Bool} (checked : algebraicCheck a h c = some answer) :
    answer = true ↔ ∃ q ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (specialize (Point.algebraic a).value h).eval q := by
  unfold algebraicCheck at checked
  split at checked
  · rename_i guards
    have parts := Bool.and_eq_true_iff.mp guards
    have selected := RootEventOrder.value_means parts.1
    split at checked
    · rename_i original
      have hs := (GlobalCheckerPoint.sign_sound original).2
      rw [AlgebraicSignReplay.atRational_sound, Rat.cast_zero, sign_eq_neg_one_iff] at hs
      have equiv := AlgebraicRootCertificate.negative_left_acceptance parts.2 selected.2
        (by norm_num : (0 : ℝ) ≤ 1) hs
      cases hl : GlobalCheckerPoint.signs (.algebraic a)
          ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 0)
          c.left with
      | none => simp only [List.map_cons] at hl; simp [hl] at checked
      | some ls =>
        cases hr : GlobalCheckerPoint.signs (.algebraic a)
            ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 1)
            c.right with
        | none => simp only [List.map_cons] at hl hr; simp [hl, hr] at checked
        | some rs =>
          have ha : decide (0 < variations ls - variations rs) = answer := by
            simp only [List.map_cons] at hl hr
            simpa [hl, hr] using checked
          have left := specialized_signs hl
          have right := specialized_signs hr
          simp only [Point.value, Rat.cast_zero] at left
          simp only [Point.value, Rat.cast_one] at right
          rw [← ha, decide_eq_true_eq]
          simpa only [AlgebraicRootCertificate.count, variationAt, List.map_map,
            Function.comp_def, left, right, Point.value] using equiv.symm
    · contradiction
  · contradiction

inductive Branch where
  | fullMask
  | zeroLevel
  | rationalRoot (certificate : RootCountCertificate.Certificate)
  | algebraicRoot (certificate : AlgebraicBranch)

structure Certificate where
  ordering : List SignWitness
  branch : Branch

def check {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0) (r : ℚ)
    (p : Point) (c : Certificate) : Option Bool :=
  if GlobalCheckerOrder.interiorCheck p && orderingCheck dir observed p c.ordering then
    let m := certifiedMask dir observed p c.ordering
    let h := CompactPolynomial.objective m r
    match c.branch with
    | .fullMask => if m = Finset.univ then some (decide (r ≤ 1)) else none
    | .zeroLevel => if r = 0 then some true else none
    | .rationalRoot root => match p with
      | .algebraic _ => none
      | .rational x =>
        let hs := specializeRational x h
        if 0 < r ∧ m ≠ Finset.univ ∧ RootCertificate.value hs 0 < 0 ∧
            RootCertificate.value hs 1 < 0 then RootSignCertificate.check hs 0 1 root else none
    | .algebraicRoot branch => match p with
      | .rational _ => none
      | .algebraic a => if 0 < r ∧ m ≠ Finset.univ then algebraicCheck a h branch else none
  else none

theorem check_sound {n1 n0 : ℕ} {dir : Direction} {observed : Outcome n1 n0}
    {r : ℚ} {p : Point} {c : Certificate} {answer : Bool}
    (checked : check dir observed r p c = some answer) :
    p.value ∈ Set.Ioo (0 : ℝ) 1 ∧
      (answer = true ↔ (r : ℝ) ≤ BoschlooValidity.value dir (beta p.value) observed) := by
  unfold check at checked
  split at checked
  · rename_i guards
    have parts := Bool.and_eq_true_iff.mp guards
    have domain := (GlobalCheckerOrder.interiorCheck_sound parts.1).2
    have positive : 0 < beta p.value := div_pos domain.1 (sub_pos.mpr domain.2)
    have hm := ordering_sound parts.2 domain
    refine ⟨domain, ?_⟩
    cases branch_eq : c.branch with
    | fullMask =>
      simp only [branch_eq] at checked
      split at checked
      · rename_i full
        have ha := Option.some.inj checked
        rw [BoschlooValidity.value, ← hm, full, NuisanceSupremum.full positive, ← ha]
        simp only [decide_eq_true_eq]
        exact_mod_cast Iff.rfl
      · contradiction
    | zeroLevel =>
      simp only [branch_eq] at checked
      split at checked
      · rename_i zero
        have ha : answer = true := (Option.some.inj checked).symm
        simp only [ha, zero, Rat.cast_zero, true_iff]
        exact (BoschlooValidity.mem_Icc positive dir observed).1
      · contradiction
    | rationalRoot root =>
      simp only [branch_eq] at checked
      cases p with
      | algebraic _ => contradiction
      | rational x =>
        dsimp only at checked
        split at checked
        · have equiv := (RootSignCertificate.checkerSound checked).2
          simp only [RootSignCertificate.Accepted, Rat.cast_zero, Rat.cast_one,
            specializeRational_eval] at equiv
          change (x : ℝ) ∈ Set.Ioo (0 : ℝ) 1 at domain
          rw [CompactPolynomial.reconstructed_objective_accept_iff _ _ domain] at equiv
          simpa only [hm, BoschlooValidity.value, Point.value] using equiv
        · contradiction
    | algebraicRoot branch =>
      simp only [branch_eq] at checked
      cases p with
      | rational _ => contradiction
      | algebraic a =>
        dsimp only at checked
        split at checked
        · have equiv := algebraicCheck_sound checked
          rw [CompactPolynomial.reconstructed_objective_accept_iff _ _ domain] at equiv
          simpa only [hm, BoschlooValidity.value] using equiv
        · contradiction
  · contradiction

end ExactCIs.Unconditional.GlobalCheckerPointDecision
