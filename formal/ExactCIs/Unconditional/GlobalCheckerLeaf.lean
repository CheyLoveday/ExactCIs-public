/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerOpenDecision
import ExactCIs.Unconditional.GlobalCheckerPointDecision
import ExactCIs.Unconditional.CellEnclosure

/-! # Data-only leaf states and actual two-sided enclosure guarantees

Each accepted leaf checks both directions. A rejected leaf checks one fixed
direction, and an enclosure leaf makes no decision. Unused packets must be
absent. There is no unresolved constructor in a successful partition.
-/
namespace ExactCIs.Unconditional.GlobalCheckerLeaf

open ProductBinomial BoschlooOrdering GlobalCheckerPoint EffectCoordinate

inductive State where
  | accepted | rejectedGreater | rejectedLess | boundary
  deriving DecidableEq

def State.inner : State → Bool
  | .accepted => true
  | _ => false

def State.outer : State → Bool
  | .rejectedGreater | .rejectedLess => false
  | _ => true

structure Leaf (C : Type) where
  state : State
  greater : Option C
  less : Option C

def check {C : Type} (f : Direction → C → Option Bool) (leaf : Leaf C) : Bool :=
  match leaf.state, leaf.greater, leaf.less with
  | .accepted, some g, some l => decide (f .greater g = some true ∧ f .less l = some true)
  | .rejectedGreater, some g, none => decide (f .greater g = some false)
  | .rejectedLess, none, some l => decide (f .less l = some false)
  | .boundary, none, none => true
  | _, _, _ => false

def Sound (state : State) (accepted : Prop) : Prop :=
  (state.inner = true → accepted) ∧ (accepted → state.outer = true)

theorem check_sound {C : Type} {f : Direction → C → Option Bool}
    {leaf : Leaf C} {P : Direction → Prop}
    (decisions : ∀ d c b, f d c = some b → (b = true ↔ P d))
    (checked : check f leaf = true) : Sound leaf.state (P .greater ∧ P .less) := by
  rcases leaf with ⟨state, g, l⟩
  cases state <;> cases g <;> cases l <;>
    simp only [check, decide_eq_true_eq, Bool.false_eq_true] at checked
  case accepted.some.some g l =>
    exact ⟨fun _ => ⟨(decisions _ _ _ checked.1).mp rfl,
      (decisions _ _ _ checked.2).mp rfl⟩, fun _ => rfl⟩
  case rejectedGreater.some.none g =>
    refine ⟨by simp [State.inner], ?_⟩
    intro accepted
    exact False.elim (Bool.false_ne_true ((decisions _ _ _ checked).mpr accepted.1))
  case rejectedLess.none.some l =>
    refine ⟨by simp [State.inner], ?_⟩
    intro accepted
    exact False.elim (Bool.false_ne_true ((decisions _ _ _ checked).mpr accepted.2))
  case boundary.none.none => exact ⟨by simp [State.inner], fun _ => rfl⟩

abbrev OpenLeaf := Leaf GlobalCheckerOpenDecision.Certificate
abbrev PointLeaf := Leaf GlobalCheckerPointDecision.Certificate

def openCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (l u : Point) (leaf : OpenLeaf) : Bool :=
  GlobalCheckerOpenDecision.domainCheck l u &&
    check (fun d => GlobalCheckerOpenDecision.check d observed r l u) leaf

def pointCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (p : Point) (leaf : PointLeaf) : Bool :=
  GlobalCheckerOrder.interiorCheck p &&
    check (fun d => GlobalCheckerPointDecision.check d observed r p) leaf

theorem openCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {l u : Point} {leaf : OpenLeaf} (checked : openCheck observed r l u leaf = true)
    (s : Compact) (inside : (s : ℝ) ∈ Set.Ioo l.value u.value) :
    Sound leaf.state (s ∈ CellEnclosure.actual observed r) := by
  have parts := Bool.and_eq_true_iff.mp checked
  have domain := GlobalCheckerOpenDecision.domainCheck_sound parts.1 inside
  have result : Sound leaf.state (BoschlooValidity.Accepted (beta s) r observed) :=
    check_sound (P := fun d => (r : ℝ) ≤ BoschlooValidity.value d (beta s) observed)
      (fun d c b hc => (GlobalCheckerOpenDecision.check_sound
        (dir := d) (c := c) (answer := b) hc inside).2) parts.2
  have equivalent := CellEnclosure.actual_finite observed r s domain
  exact ⟨fun h => equivalent.mpr (result.1 h), fun h => result.2 (equivalent.mp h)⟩

theorem pointCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {p : Point} {leaf : PointLeaf} (checked : pointCheck observed r p leaf = true)
    (s : Compact) (same : (s : ℝ) = p.value) :
    Sound leaf.state (s ∈ CellEnclosure.actual observed r) := by
  have parts := Bool.and_eq_true_iff.mp checked
  have domain := (GlobalCheckerOrder.interiorCheck_sound parts.1).2
  have result : Sound leaf.state (BoschlooValidity.Accepted (beta p.value) r observed) :=
    check_sound (P := fun d => (r : ℝ) ≤ BoschlooValidity.value d (beta p.value) observed)
      (fun d c b hc => (GlobalCheckerPointDecision.check_sound
        (dir := d) (c := c) (answer := b) hc).2) parts.2
  rw [← same] at domain result
  have equivalent := CellEnclosure.actual_finite observed r s domain
  exact ⟨fun h => equivalent.mpr (result.1 h), fun h => result.2 (equivalent.mp h)⟩

end ExactCIs.Unconditional.GlobalCheckerLeaf
