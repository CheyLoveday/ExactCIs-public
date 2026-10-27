/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SelectedRoot

/-! # Complete typed comparison certificates for selected algebraic roots

Strict order uses disjoint checked refinements. Equality uses one checked common
root inside both original isolators and exact divisibility identities. Input
definers may be reducible, repeated and different. Witness existence is classical;
canonical bytes, deterministic generation and work limits remain outside scope.
-/
namespace ExactCIs.Unconditional.RootComparison

open SelectedRoot RootCertificate

inductive Certificate where
  | less (left right : Refinement)
  | equal (common : Root) (leftQuotient rightQuotient : Coefficients)
  | greater (left right : Refinement)
  deriving Repr

def separated (a b : Root) (left right : Refinement) : Bool :=
  left.check a && right.check b && decide (left.upper ≤ right.lower)

def commonCheck (a b common : Root) (qa qb : Coefficients) : Bool :=
  common.check &&
  decide (a.lower < common.lower ∧ common.upper < a.upper ∧
    b.lower < common.lower ∧ common.upper < b.upper) &&
  AlgebraicCertificate.zeroCheck a.definer common.definer qa &&
  AlgebraicCertificate.zeroCheck b.definer common.definer qb

def check (a b : Root) (c : Certificate) : Option Ordering :=
  if a.check && b.check then
    match c with
    | .less left right => if separated a b left right then some .lt else none
    | .equal common qa qb => if commonCheck a b common qa qb then some .eq else none
    | .greater left right => if separated b a right left then some .gt else none
  else none

def Relation : Ordering → ℝ → ℝ → Prop
  | .lt, x, y => x < y
  | .eq, x, y => x = y
  | .gt, x, y => y < x

theorem separated_sound {a b : Root} {left right : Refinement}
    (base_a : a.check = true) (base_b : b.check = true)
    (checked : separated a b left right = true) {x y : ℝ}
    (hx : a.Means x) (hy : b.Means y) : x < y := by
  have parts : left.check a = true ∧ right.check b = true ∧ left.upper ≤ right.lower := by
    simpa only [separated, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  have lx := refinement_preserves base_a parts.1 hx
  have ry := refinement_preserves base_b parts.2.1 hy
  exact (lx.1.2.trans_le (by exact_mod_cast parts.2.2)).trans ry.1.1

theorem common_sound {a b common : Root} {qa qb : Coefficients}
    (base_a : a.check = true) (base_b : b.check = true)
    (checked : commonCheck a b common qa qb = true) {x y : ℝ}
    (hx : a.Means x) (hy : b.Means y) : x = y := by
  have parts : common.check = true ∧
      (a.lower < common.lower ∧ common.upper < a.upper ∧
        b.lower < common.lower ∧ common.upper < b.upper) ∧
      AlgebraicCertificate.zeroCheck a.definer common.definer qa = true ∧
      AlgebraicCertificate.zeroCheck b.definer common.definer qb = true := by
    simpa only [commonCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  obtain ⟨z, hz, _⟩ := unique parts.1
  have az : a.Means z :=
    ⟨⟨(by exact_mod_cast parts.2.1.1 : (a.lower : ℝ) < common.lower).trans hz.1.1,
      hz.1.2.trans (by exact_mod_cast parts.2.1.2.1 : (common.upper : ℝ) < a.upper)⟩,
      AlgebraicCertificate.zeroCheck_sound parts.2.2.1 hz.2⟩
  have bz : b.Means z :=
    ⟨⟨(by exact_mod_cast parts.2.1.2.2.1 : (b.lower : ℝ) < common.lower).trans hz.1.1,
      hz.1.2.trans (by exact_mod_cast parts.2.1.2.2.2 : (common.upper : ℝ) < b.upper)⟩,
      AlgebraicCertificate.zeroCheck_sound parts.2.2.2 hz.2⟩
  exact (same_value base_a hx az).trans (same_value base_b hy bz).symm

theorem check_sound {a b : Root} {c : Certificate} {answer : Ordering}
    (checked : check a b c = some answer) {x y : ℝ}
    (hx : a.Means x) (hy : b.Means y) :
    a.check = true ∧ b.check = true ∧ Relation answer x y := by
  unfold check at checked
  by_cases valid : (a.check && b.check) = true
  · rw [if_pos valid] at checked
    have bases : a.check = true ∧ b.check = true := by
      simpa only [Bool.and_eq_true] using valid
    refine ⟨bases.1, bases.2, ?_⟩
    cases c with
    | less left right =>
      change (if separated a b left right then some .lt else none) = some answer at checked
      split at checked
      · have same := Option.some.inj checked
        subst answer
        exact separated_sound bases.1 bases.2 (by assumption) hx hy
      · contradiction
    | equal common qa qb =>
      change (if commonCheck a b common qa qb then some .eq else none) = some answer at checked
      split at checked
      · have same := Option.some.inj checked
        subst answer
        exact common_sound bases.1 bases.2 (by assumption) hx hy
      · contradiction
    | greater left right =>
      change (if separated b a right left then some .gt else none) = some answer at checked
      split at checked
      · have same := Option.some.inj checked
        subst answer
        exact separated_sound bases.2 bases.1 (by assumption) hy hx
      · contradiction
  · simp only [if_neg valid, reduceCtorEq] at checked

theorem exists_separated {a b : Root} (base_a : a.check = true) (base_b : b.check = true)
    {x y : ℝ} (hx : a.Means x) (hy : b.Means y) (order : x < y) :
    ∃ left right : Refinement, separated a b left right = true := by
  let mid := (x + y) / 2
  obtain ⟨left, hl, lx, ls⟩ := exists_refinement_within base_a hx
    isOpen_Iio (show x < mid by dsimp [mid]; linarith)
  obtain ⟨right, hr, ry, rs⟩ := exists_refinement_within base_b hy
    isOpen_Ioi (show mid < y by dsimp [mid]; linarith)
  have lmid := ls (show (left.upper : ℝ) ∈ Set.Icc (left.lower : ℝ) left.upper from
    ⟨(lx.1.1.trans lx.1.2).le, le_rfl⟩)
  have rmid := rs (show (right.lower : ℝ) ∈ Set.Icc (right.lower : ℝ) right.upper from
    ⟨le_rfl, (ry.1.1.trans ry.1.2).le⟩)
  have apart : left.upper ≤ right.lower := by
    exact_mod_cast ((show (left.upper : ℝ) < mid from lmid).trans
      (show mid < (right.lower : ℝ) from rmid)).le
  exact ⟨left, right, by simp only [separated, hl, hr, decide_eq_true apart, Bool.and_self]⟩

theorem exists_common {a b : Root} (base_a : a.check = true)
    {x : ℝ} (hx : a.Means x) (hy : b.Means x) :
    ∃ common : Root, ∃ qa qb : Coefficients, commonCheck a b common qa qb = true := by
  have algebraic := integral base_a hx
  obtain ⟨l, u, c, hc, bounds, subset⟩ := AlgebraicEmbedding.exists_checked_isolator_within
    (AlgebraicGeneration.definer x) (AlgebraicGeneration.definer_ne_zero algebraic)
    (AlgebraicGeneration.definer_root x) (isOpen_Ioo.inter isOpen_Ioo) ⟨hx.1, hy.1⟩
  obtain ⟨qa, hqa⟩ := AlgebraicGeneration.zero_check_complete a.definer hx.2
  obtain ⟨qb, hqb⟩ := AlgebraicGeneration.zero_check_complete b.definer hy.2
  have left := subset (show (l : ℝ) ∈ Set.Icc (l : ℝ) u from
    ⟨le_rfl, (bounds.1.trans bounds.2).le⟩)
  have right := subset (show (u : ℝ) ∈ Set.Icc (l : ℝ) u from
    ⟨(bounds.1.trans bounds.2).le, le_rfl⟩)
  have inclusion : a.lower < l ∧ u < a.upper ∧ b.lower < l ∧ u < b.upper :=
    ⟨by exact_mod_cast left.1.1, by exact_mod_cast right.1.2,
      by exact_mod_cast left.2.1, by exact_mod_cast right.2.2⟩
  refine ⟨⟨AlgebraicGeneration.definer x, l, u, c⟩, qa, qb, ?_⟩
  simp only [commonCheck, Root.check, hc, hqa, hqb, decide_eq_true inclusion, Bool.and_self]

theorem exists_certificate {a b : Root} (base_a : a.check = true) (base_b : b.check = true)
    {x y : ℝ} (hx : a.Means x) (hy : b.Means y) :
    ∃ c : Certificate, ∃ answer : Ordering,
      check a b c = some answer ∧ Relation answer x y := by
  rcases lt_trichotomy x y with order | equal | order
  · obtain ⟨left, right, separated⟩ := exists_separated base_a base_b hx hy order
    exact ⟨.less left right, .lt, by simp only [check, base_a, base_b, Bool.and_self,
      ↓reduceIte, separated], order⟩
  · subst y
    obtain ⟨common, qa, qb, together⟩ := exists_common base_a hx hy
    exact ⟨.equal common qa qb, .eq, by simp only [check, base_a, base_b, Bool.and_self,
      ↓reduceIte, together], rfl⟩
  · obtain ⟨right, left, separated⟩ := exists_separated base_b base_a hy hx order
    exact ⟨.greater left right, .gt, by simp only [check, base_a, base_b, Bool.and_self,
      ↓reduceIte, separated], order⟩

theorem answers_consistent {a b : Root} {c d : Certificate} {first second : Ordering}
    (hc : check a b c = some first) (hd : check a b d = some second) : first = second := by
  have base_a : a.check = true := by
    by_contra invalid
    simp [check, invalid] at hc
  have base_b : b.check = true := by
    by_contra invalid
    simp [check, invalid] at hc
  obtain ⟨x, hx, _⟩ := unique base_a
  obtain ⟨y, hy, _⟩ := unique base_b
  have hfirst := (check_sound hc hx hy).2.2
  have hsecond := (check_sound hd hx hy).2.2
  cases first <;> cases second <;> first
    | rfl
    | (simp only [Relation] at hfirst hsecond; exfalso; linarith)

end ExactCIs.Unconditional.RootComparison
