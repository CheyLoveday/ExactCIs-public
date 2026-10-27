/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerPoint

/-! # Checked mixed rational/algebraic order for the global partition

Adjacent comparisons prove strict order of the actual selected values. Disjoint
isolators give a direct comparison; overlapping algebraic isolators require the
existing exact comparison certificate. Equal values cannot become two owners.
-/
namespace ExactCIs.Unconditional.GlobalCheckerOrder

open GlobalCheckerPoint

inductive Witness where
  | direct
  | algebraic (certificate : RootComparison.Certificate)

def lessCheck (a b : Point) (w : Witness) : Bool :=
  a.check && b.check && match a, b, w with
  | .rational x, .rational y, .direct => decide (x < y)
  | .rational x, .algebraic y, .direct => decide (x ≤ y.lower)
  | .algebraic x, .rational y, .direct => decide (x.upper ≤ y)
  | .algebraic x, .algebraic y, .direct => decide (x.upper ≤ y.lower)
  | .algebraic x, .algebraic y, .algebraic c =>
      decide (RootComparison.check x y c = some .lt)
  | _, _, _ => false

theorem lessCheck_sound {a b : Point} {w : Witness}
    (checked : lessCheck a b w = true) : a.value < b.value := by
  cases w with
  | direct =>
    cases a <;> cases b <;>
      simp only [lessCheck, Point.check, Bool.and_eq_true, decide_eq_true_eq,
        true_and, and_true] at checked <;> simp only [Point.value]
    case rational.rational x y => exact_mod_cast checked
    case rational.algebraic x y =>
      exact (by exact_mod_cast checked.2 : (x : ℝ) ≤ y.lower).trans_lt
        (RootEventOrder.value_means checked.1).1.1
    case algebraic.rational x y =>
      exact (RootEventOrder.value_means checked.1).1.2.trans_le
        (by exact_mod_cast checked.2)
    case algebraic.algebraic x y =>
      exact ((RootEventOrder.value_means checked.1.1).1.2.trans_le
        (by exact_mod_cast checked.2)).trans (RootEventOrder.value_means checked.1.2).1.1
  | algebraic c =>
    cases a <;> cases b <;>
      simp only [lessCheck, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true,
        and_false] at checked
    case algebraic.algebraic x y =>
      exact (RootComparison.check_sound checked.2
        (RootEventOrder.value_means checked.1.1)
        (RootEventOrder.value_means checked.1.2)).2.2

def interiorCheck (p : Point) : Bool := p.check && match p with
  | .rational q => decide (0 < q ∧ q < 1)
  | .algebraic a => decide (0 ≤ a.lower ∧ a.upper ≤ 1)

theorem interiorCheck_sound {p : Point} (checked : interiorCheck p = true) :
    p.check = true ∧ p.value ∈ Set.Ioo (0 : ℝ) 1 := by
  have parts := Bool.and_eq_true_iff.mp checked
  refine ⟨parts.1, ?_⟩
  cases p with
  | rational q =>
    change (0 : ℝ) < (q : ℝ) ∧ (q : ℝ) < 1
    exact_mod_cast (of_decide_eq_true parts.2)
  | algebraic a =>
    have bounds := of_decide_eq_true parts.2
    have selected := RootEventOrder.value_means parts.1
    exact ⟨(by exact_mod_cast bounds.1 : (0 : ℝ) ≤ a.lower).trans_lt selected.1.1,
      selected.1.2.trans_le (by exact_mod_cast bounds.2)⟩

def check : List Point → List Witness → Bool
  | [], [] => true
  | [_], [] => true
  | a :: b :: ps, w :: ws => lessCheck a b w && check (b :: ps) ws
  | _, _ => false

theorem check_sound {ps : List Point} {ws : List Witness} (checked : check ps ws = true) :
    ps.Pairwise (fun a b => a.value < b.value) := by
  match ps, ws with
  | [], [] => simp
  | [_], [] => exact List.pairwise_singleton _ _
  | a :: b :: ps, w :: ws =>
    have parts := Bool.and_eq_true_iff.mp checked
    have head := lessCheck_sound parts.1
    have tail := check_sound parts.2
    apply List.pairwise_cons.mpr
    refine ⟨?_, tail⟩
    intro y hy
    rcases List.mem_cons.mp hy with rfl | hy
    · exact head
    · exact head.trans ((List.pairwise_cons.mp tail).1 y hy)
  | [], _ :: _ => simp [check] at checked
  | [_], _ :: _ => simp [check] at checked
  | _ :: _ :: _, [] => simp [check] at checked
termination_by ps.length

theorem values_distinct {ps : List Point} {ws : List Witness}
    (checked : check ps ws = true) : (ps.map Point.value).Nodup := by
  have ordered : (ps.map Point.value).Pairwise (· < ·) := by
    simpa only [List.pairwise_map] using check_sound checked
  exact ordered.sortedLT.nodup

end ExactCIs.Unconditional.GlobalCheckerOrder
