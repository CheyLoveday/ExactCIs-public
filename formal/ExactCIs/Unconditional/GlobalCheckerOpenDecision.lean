/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerParametricRoot
import ExactCIs.Unconditional.CompactPolynomial
import ExactCIs.Unconditional.BoschlooValidity

/-! # Actual Boschloo decisions on entire compact open cells

Ordering packets are finite lists in fixed first-count/second-count order.
The checker reconstructs both comparisons and the original signed objective.
A successful decision applies to every real effect in the open cell, including
an effect-dependent nuisance witness for acceptance. No mask is supplied.
-/
namespace ExactCIs.Unconditional.GlobalCheckerOpenDecision

open RootCertificate AlgebraicSpecialization ProductBinomial BoschlooOrdering
open GlobalCheckerPoint GlobalCheckerOpenSign EffectCoordinate

def index {n1 n0 : ℕ} (o : Outcome n1 n0) : ℕ := o.1.val * (n0 + 1) + o.2.val

def orderingWitness {n1 n0 : ℕ} (ordering : List Witness) (o : Outcome n1 n0) : Witness :=
  ordering[index o]?.getD .identityZero

def certifiedMask (n1 n0 : ℕ) (ordering : List Witness) : Finset (Outcome n1 n0) :=
  Finset.univ.filter fun o => (orderingWitness ordering o).sign ≠ 1

def orderingCheck {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0)
    (l u : Point) (ordering : List Witness) : Bool :=
  decide (ordering.length = (n1 + 1) * (n0 + 1)) &&
    decide (∀ o : Outcome n1 n0, GlobalCheckerOpenSign.check
      (CompactPolynomial.comparison dir o observed) l u (orderingWitness ordering o) = true)

theorem ordering_sound {n1 n0 : ℕ} {dir : Direction} {observed : Outcome n1 n0}
    {l u : Point} {ordering : List Witness}
    (checked : orderingCheck dir observed l u ordering = true)
    {x : ℝ} (domain : x ∈ Set.Ioo (0 : ℝ) 1) (inside : x ∈ Set.Ioo l.value u.value) :
    certifiedMask n1 n0 ordering = mask dir (beta x) observed := by
  classical
  ext o
  have checks := of_decide_eq_true (Bool.and_eq_true_iff.mp checked).2
  have hs := GlobalCheckerOpenSign.check_sound (checks o) inside
  rw [CompactPolynomial.comparison_sign dir o observed domain] at hs
  simp only [certifiedMask, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [ParametricPolynomial.mask_iff
    (show 0 < beta x from div_pos domain.1 (sub_pos.mpr domain.2)), ← hs]
  simp only [ne_eq, sign_eq_one_iff, not_lt]

theorem count_sound {l u : Point} {h : Bivariate} {c : GlobalCheckerParametricRoot.Certificate}
    (checked : GlobalCheckerParametricRoot.check l u h c = true)
    {left right : List Witness}
    (left_checked : signsCheck l u 0 (c.representative :: c.tail) left = true)
    (right_checked : signsCheck l u 1 (c.representative :: c.tail) right = true)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) :
    nuisanceCount left right = {q : ℝ | 0 < q ∧ q ≤ 1 ∧ (specialize x h).eval q = 0}.ncard := by
  have hl := signsCheck_sound left_checked inside
  have hr := signsCheck_sound right_checked inside
  simp only [Rat.cast_zero] at hl
  simp only [Rat.cast_one] at hr
  have result := GlobalCheckerParametricRoot.count_sound checked inside (by norm_num : (0 : ℝ) ≤ 1)
  simpa only [nuisanceCount, GlobalCheckerParametricRoot.count, SturmVariation.variationAt,
    List.map_map, Function.comp_def, Rat.cast_zero, Rat.cast_one, hl, hr] using result

/-- The same replayed integer counts all nuisance roots at every effect in the
cell, including repeated roots of the original threshold. -/
theorem root_count_constant {l u : Point} {h : Bivariate}
    {c : GlobalCheckerParametricRoot.Certificate}
    (checked : GlobalCheckerParametricRoot.check l u h c = true)
    {left right : List Witness}
    (left_checked : signsCheck l u 0 (c.representative :: c.tail) left = true)
    (right_checked : signsCheck l u 1 (c.representative :: c.tail) right = true)
    {x y : ℝ} (hx : x ∈ Set.Ioo l.value u.value) (hy : y ∈ Set.Ioo l.value u.value) :
    {q : ℝ | 0 < q ∧ q ≤ 1 ∧ (specialize x h).eval q = 0}.ncard =
      {q : ℝ | 0 < q ∧ q ≤ 1 ∧ (specialize y h).eval q = 0}.ncard := by
  rw [← count_sound checked left_checked right_checked hx,
    ← count_sound checked left_checked right_checked hy]

theorem acceptance_iff {l u : Point} {h : Bivariate} {c : GlobalCheckerParametricRoot.Certificate}
    (checked : GlobalCheckerParametricRoot.check l u h c = true)
    {left right : List Witness} {original : Witness}
    (left_checked : signsCheck l u 0 (c.representative :: c.tail) left = true)
    (right_checked : signsCheck l u 1 (c.representative :: c.tail) right = true)
    (original_checked : GlobalCheckerOpenSign.check
      (AlgebraicSignReplay.atRational h 0) l u original = true)
    (negative : original.sign = -1)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (specialize x h).eval q) ↔ 0 < nuisanceCount left right := by
  have hs := GlobalCheckerOpenSign.check_sound original_checked inside
  rw [AlgebraicSignReplay.atRational_sound, Rat.cast_zero, negative, sign_eq_neg_one_iff] at hs
  have hl := signsCheck_sound left_checked inside
  have hr := signsCheck_sound right_checked inside
  simp only [Rat.cast_zero] at hl
  simp only [Rat.cast_one] at hr
  have result := GlobalCheckerParametricRoot.negative_left_acceptance checked inside
    (by norm_num : (0 : ℝ) ≤ 1) hs
  simpa only [nuisanceCount, GlobalCheckerParametricRoot.count, SturmVariation.variationAt,
    List.map_map, Function.comp_def, Rat.cast_zero, Rat.cast_one, hl, hr] using result

structure RootBranch where
  originalLeft : Witness
  originalRight : Witness
  root : GlobalCheckerParametricRoot.Certificate
  left : List Witness
  right : List Witness

inductive Branch where
  | fullMask
  | zeroLevel
  | interiorRoot (certificate : RootBranch)

structure Certificate where
  ordering : List Witness
  branch : Branch

def domainCheck (l u : Point) : Bool :=
  l.check && u.check && decide (0 ≤ l.lower ∧ u.upper ≤ 1)

theorem domainCheck_sound {l u : Point} (checked : domainCheck l u = true)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) : x ∈ Set.Ioo (0 : ℝ) 1 := by
  have parts : l.check = true ∧ u.check = true ∧ 0 ≤ l.lower ∧ u.upper ≤ 1 := by
    simpa only [domainCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  exact ⟨((by exact_mod_cast parts.2.2.1 : (0 : ℝ) ≤ l.lower).trans
      (point_bounds parts.1).1).trans_lt inside.1,
    inside.2.trans_le ((point_bounds parts.2.1).2.trans
      (by exact_mod_cast parts.2.2.2))⟩

def check {n1 n0 : ℕ} (dir : Direction) (observed : Outcome n1 n0) (r : ℚ)
    (l u : Point) (c : Certificate) : Option Bool :=
  if domainCheck l u && orderingCheck dir observed l u c.ordering then
    let m := certifiedMask n1 n0 c.ordering
    match c.branch with
    | .fullMask => if m = Finset.univ then some (decide (r ≤ 1)) else none
    | .zeroLevel => if r = 0 then some true else none
    | .interiorRoot branch =>
      let h := CompactPolynomial.objective m r
      if 0 < r ∧ m ≠ Finset.univ ∧
          GlobalCheckerOpenSign.check (AlgebraicSignReplay.atRational h 0)
            l u branch.originalLeft = true ∧ branch.originalLeft.sign = -1 ∧
          GlobalCheckerOpenSign.check (AlgebraicSignReplay.atRational h 1)
            l u branch.originalRight = true ∧ branch.originalRight.sign = -1 ∧
          GlobalCheckerParametricRoot.check l u h branch.root = true ∧
          signsCheck l u 0 (branch.root.representative :: branch.root.tail) branch.left = true ∧
          signsCheck l u 1 (branch.root.representative :: branch.root.tail) branch.right = true
      then some (decide (0 < nuisanceCount branch.left branch.right)) else none
  else none

theorem check_sound {n1 n0 : ℕ} {dir : Direction} {observed : Outcome n1 n0}
    {r : ℚ} {l u : Point} {c : Certificate} {answer : Bool}
    (checked : check dir observed r l u c = some answer)
    {x : ℝ} (inside : x ∈ Set.Ioo l.value u.value) :
    x ∈ Set.Ioo (0 : ℝ) 1 ∧
      (answer = true ↔ (r : ℝ) ≤ BoschlooValidity.value dir (beta x) observed) := by
  unfold check at checked
  split at checked
  · rename_i guards
    have parts := Bool.and_eq_true_iff.mp guards
    have domain := domainCheck_sound parts.1 inside
    have positive : 0 < beta x := div_pos domain.1 (sub_pos.mpr domain.2)
    have hm := ordering_sound parts.2 domain inside
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
    | interiorRoot branch =>
      simp only [branch_eq] at checked
      split at checked
      · rename_i checks
        have equiv := acceptance_iff checks.2.2.2.2.2.2.1
          checks.2.2.2.2.2.2.2.1 checks.2.2.2.2.2.2.2.2
          checks.2.2.1 checks.2.2.2.1 inside
        rw [CompactPolynomial.reconstructed_objective_accept_iff _ _ domain] at equiv
        have ha := Option.some.inj checked
        rw [← ha, decide_eq_true_eq]
        simpa only [hm, BoschlooValidity.value] using equiv.symm
      · contradiction
  · contradiction

/-- The observed Fisher tail really is below one in the nontrivial branch;
this is derived from the checked actual mask, not a supplied claim. -/
theorem observed_tail_below_one {n1 n0 : ℕ} {dir : Direction}
    {observed : Outcome n1 n0} {l u : Point} {ordering : List Witness}
    (checked : orderingCheck dir observed l u ordering = true)
    (nonfull : certifiedMask n1 n0 ordering ≠ Finset.univ) {x : ℝ}
    (domain : x ∈ Set.Ioo (0 : ℝ) 1) (inside : x ∈ Set.Ioo l.value u.value) :
    statistic dir (beta x) observed < 1 := by
  have positive : 0 < beta x := div_pos domain.1 (sub_pos.mpr domain.2)
  apply lt_of_le_of_ne (statistic_mem_Icc positive dir observed).2
  intro one
  exact nonfull ((ordering_sound checked domain inside).trans
    (full_mask_of_one positive dir observed one))

end ExactCIs.Unconditional.GlobalCheckerOpenDecision
