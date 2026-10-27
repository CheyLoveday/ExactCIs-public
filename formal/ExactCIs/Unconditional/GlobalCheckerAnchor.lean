/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerEnclosure

/-! # Accepted anchors resolved against their actual owning leaf

An anchor identifies a checked accepted singleton or an interior rational sample
of a checked accepted open leaf. Indices outside the corresponding array, samples
on a boundary, and anchors in outer-only or rejected leaves are refused.
-/
namespace ExactCIs.Unconditional.GlobalCheckerAnchor

open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition
open GlobalCheckerEnclosure EffectCoordinate

inductive Anchor where
  | rational (value : ℚ) (openCell : ℕ)
  | point (index : ℕ)

def resolveFrom : Point → Chain → Anchor → Option Point
  | l, .last gap, .rational q 0 =>
      if gap.state.inner && sampleCheck l (.rational 1) q then some (.rational q) else none
  | _, .last _, _ => none
  | l, .next p gap _ _, .rational q 0 =>
      if gap.state.inner && sampleCheck l p q then some (.rational q) else none
  | _, .next p _ _ rest, .rational q (i + 1) => resolveFrom p rest (.rational q i)
  | _, .next p _ single _, .point 0 => if single.state.inner then some p else none
  | _, .next p _ _ rest, .point (i + 1) => resolveFrom p rest (.point i)

theorem sample_anchor {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {l u : Point} {leaf : OpenLeaf} {q : ℚ}
    (leaves : openCheck observed r l u leaf = true) (sample : sampleCheck l u q = true) :
    ∃ s : Compact, (s : ℝ) = (q : ℝ) ∧ (s : ℝ) ∈ Set.Ioo l.value u.value := by
  have inside := sampleCheck_sound sample
  have domain := GlobalCheckerOpenDecision.domainCheck_sound
    (Bool.and_eq_true_iff.mp leaves).1 inside
  exact ⟨⟨q, domain.1.le, domain.2.le⟩, rfl, inside⟩

theorem resolveFrom_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {l : Point} {chain : Chain} {anchor : Anchor} {p : Point}
    (leaves : checkFrom observed r l chain = true)
    (resolved : resolveFrom l chain anchor = some p) :
    p.check = true ∧ ∃ s ∈ selectedFrom State.inner l chain, (s : ℝ) = p.value := by
  induction chain generalizing l anchor p with
  | last gap =>
    cases anchor with
    | point i => simp [resolveFrom] at resolved
    | rational q i =>
      cases i with
      | succ i => simp [resolveFrom] at resolved
      | zero =>
        simp only [resolveFrom] at resolved
        split at resolved
        · rename_i h
          have parts := Bool.and_eq_true_iff.mp h
          cases Option.some.inj resolved
          obtain ⟨s, hs, inside⟩ := sample_anchor leaves parts.2
          refine ⟨rfl, s, ?_, ?_⟩
          · exact ⟨parts.1, by simpa only
              [Point.value, Rat.cast_one, Set.mem_Ioo, Set.mem_ofPred_eq] using inside⟩
          · simpa only [Point.value] using hs
        · contradiction
  | next point gap single rest ih =>
    have lc : openCheck observed r l point gap = true ∧
        pointCheck observed r point single = true ∧ checkFrom observed r point rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, and_assoc] using leaves
    cases anchor with
    | point i =>
      cases i with
      | zero =>
        simp only [resolveFrom] at resolved
        split at resolved
        · rename_i kept
          cases Option.some.inj resolved
          have domain := GlobalCheckerOrder.interiorCheck_sound
            (Bool.and_eq_true_iff.mp lc.2.1).1
          let s : Compact := ⟨point.value, domain.2.1.le, domain.2.2.le⟩
          exact ⟨domain.1, s, Or.inl (Or.inr ⟨kept, rfl⟩), rfl⟩
        · contradiction
      | succ i =>
        obtain ⟨hp, s, hs, same⟩ := ih lc.2.2 resolved
        exact ⟨hp, s, Or.inr hs, same⟩
    | rational q i =>
      cases i with
      | zero =>
        simp only [resolveFrom] at resolved
        split at resolved
        · rename_i h
          have parts := Bool.and_eq_true_iff.mp h
          cases Option.some.inj resolved
          obtain ⟨s, hs, inside⟩ := sample_anchor lc.1 parts.2
          exact ⟨rfl, s, Or.inl (Or.inl ⟨parts.1, inside⟩), hs⟩
        · contradiction
      | succ i =>
        obtain ⟨hp, s, hs, same⟩ := ih lc.2.2 resolved
        exact ⟨hp, s, Or.inr hs, same⟩

def resolve (chain : Chain) (anchor : Anchor) : Option Point :=
  resolveFrom (.rational 0) chain anchor

theorem resolve_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness} {anchor : Anchor} {p : Point}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (resolved : resolve chain anchor = some p) :
    p.check = true ∧ ∃ s ∈ acceptedCells observed r chain, (s : ℝ) = p.value := by
  obtain ⟨hp, s, hs, same⟩ := resolveFrom_sound (Bool.and_eq_true_iff.mp leaves).2 resolved
  exact ⟨hp, s, Or.inr hs, same⟩

theorem enclosed_anchor {n1 n0 : ℕ} {observed : Outcome n1 n0} {r lo hi : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness} {anchor : Anchor} {p : Point}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (resolved : resolve chain anchor = some p) (bounds : lo ≤ p.lower ∧ p.upper ≤ hi) :
    ∃ s ∈ acceptedCells observed r chain, (s : ℝ) ∈ Set.Icc (lo : ℝ) hi := by
  obtain ⟨hp, s, hs, same⟩ := resolve_sound leaves resolved
  refine ⟨s, hs, ?_⟩
  rw [same]
  exact ⟨(by exact_mod_cast bounds.1 : (lo : ℝ) ≤ p.lower).trans (point_bounds hp).1,
    (point_bounds hp).2.trans (by exact_mod_cast bounds.2)⟩

end ExactCIs.Unconditional.GlobalCheckerAnchor
