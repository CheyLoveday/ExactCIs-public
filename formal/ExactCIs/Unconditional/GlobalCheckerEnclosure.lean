/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerPartition

/-! # Constructed unions of accepted and outer leaves

These are the actual unions of the checked leaf cells. Structural singleton
membership is computed, and open-cell closures are conservatively enclosed by
the rational bounds of their selected endpoints. No producer set is accepted.
-/
namespace ExactCIs.Unconditional.GlobalCheckerEnclosure

open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition EffectCoordinate

noncomputable def chosen (f : State → Bool) (state : State) (C : Set Compact) : Set Compact :=
  {s | f state = true ∧ s ∈ C}

noncomputable def selectedFrom (f : State → Bool) : Point → Chain → Set Compact
  | l, .last gap => chosen f gap.state {s | l.value < (s : ℝ) ∧ (s : ℝ) < 1}
  | l, .next p gap single rest =>
      chosen f gap.state {s | l.value < (s : ℝ) ∧ (s : ℝ) < p.value} ∪
      chosen f single.state {s | (s : ℝ) = p.value} ∪ selectedFrom f p rest

theorem from_inner_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {l : Point} {chain : Chain} (checked : checkFrom observed r l chain = true) :
    selectedFrom State.inner l chain ⊆ CellEnclosure.actual observed r := by
  induction chain generalizing l with
  | last gap =>
    intro s hs
    exact (openCheck_sound checked s
      (by simpa only [Point.value, Rat.cast_one, Set.mem_Ioo, Set.mem_ofPred_eq]
        using hs.2)).1 hs.1
  | next p gap single rest ih =>
    have parts : openCheck observed r l p gap = true ∧
        pointCheck observed r p single = true ∧ checkFrom observed r p rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, and_assoc] using checked
    intro s hs
    rcases hs with (gapMember | pointMember) | tailMember
    · exact (openCheck_sound parts.1 s gapMember.2).1 gapMember.1
    · exact (pointCheck_sound parts.2.1 s pointMember.2).1 pointMember.1
    · exact ih parts.2.2 tailMember

theorem from_outer_complete {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {l : Point} {chain : Chain} (checked : checkFrom observed r l chain = true)
    (s : Compact) (inside : (s : ℝ) ∈ Set.Ioo l.value 1)
    (accepted : s ∈ CellEnclosure.actual observed r) : s ∈ selectedFrom State.outer l chain := by
  induction chain generalizing l with
  | last gap =>
    exact ⟨(openCheck_sound checked s
      (by simpa only [Point.value, Rat.cast_one] using inside)).2 accepted, inside⟩
  | next p gap single rest ih =>
    have parts : openCheck observed r l p gap = true ∧
        pointCheck observed r p single = true ∧ checkFrom observed r p rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, and_assoc] using checked
    rcases lt_trichotomy (s : ℝ) p.value with before | same | after
    · exact Or.inl (Or.inl ⟨(openCheck_sound parts.1 s ⟨inside.1, before⟩).2 accepted,
        inside.1, before⟩)
    · exact Or.inl (Or.inr ⟨(pointCheck_sound parts.2.1 s same).2 accepted, same⟩)
    · exact Or.inr (ih parts.2.2 ⟨after, inside.2⟩)

noncomputable def structuralSet {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (e : Structural.Endpoint) : Set Compact :=
  {s | Structural.check e r observed = true ∧ s = GlobalHull.endpoint e}

noncomputable def selected {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (f : State → Bool) (chain : Chain) : Set Compact :=
  structuralSet observed r .zero ∪ structuralSet observed r .infinity ∪
    selectedFrom f (.rational 0) chain

noncomputable def acceptedCells {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) : Set Compact := selected observed r State.inner chain

noncomputable def outerCells {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) : Set Compact := selected observed r State.outer chain

theorem structuralSet_sound {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (e : Structural.Endpoint) : structuralSet observed r e ⊆ CellEnclosure.actual observed r := by
  rintro s ⟨checked, rfl⟩
  exact (CellEnclosure.actual_structural _ _ _).mpr ((Structural.check_iff _ _ _).mp checked)

theorem sandwich {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    (checked : GlobalCheckerPartition.check observed r chain order = true) :
    acceptedCells observed r chain ⊆ CellEnclosure.actual observed r ∧
      CellEnclosure.actual observed r ⊆ outerCells observed r chain := by
  have leaves := (Bool.and_eq_true_iff.mp checked).2
  constructor
  · intro s hs
    rcases hs with (zero | one) | finite
    · exact structuralSet_sound _ _ _ zero
    · exact structuralSet_sound _ _ _ one
    · exact from_inner_sound leaves finite
  · intro s hs
    by_cases zero : (s : ℝ) = 0
    · have same : s = GlobalHull.endpoint .zero := Subtype.ext zero
      exact Or.inl (Or.inl ⟨(Structural.check_iff _ _ _).mpr
        ((CellEnclosure.actual_structural _ _ _).mp (same ▸ hs)), same⟩)
    by_cases one : (s : ℝ) = 1
    · have same : s = GlobalHull.endpoint .infinity := Subtype.ext one
      exact Or.inl (Or.inr ⟨(Structural.check_iff _ _ _).mpr
        ((CellEnclosure.actual_structural _ _ _).mp (same ▸ hs)), same⟩)
    apply Or.inr
    apply from_outer_complete leaves s _ hs
    simpa only [Point.value, Rat.cast_zero, Set.mem_Ioo] using
      And.intro (lt_of_le_of_ne s.property.1 (Ne.symm zero))
        (lt_of_le_of_ne s.property.2 one)

def bounds (lo hi : ℚ) (l u : Point) (state : State) : Bool :=
  if state.outer then decide (lo ≤ l.lower ∧ u.upper ≤ hi) else true

def boundsFrom (lo hi : ℚ) : Point → Chain → Bool
  | l, .last gap => bounds lo hi l (.rational 1) gap.state
  | l, .next p gap single rest => bounds lo hi l p gap.state &&
      bounds lo hi p p single.state && boundsFrom lo hi p rest

theorem bounds_sound {lo hi : ℚ} {l u : Point} {state : State}
    (checked : bounds lo hi l u state = true) (kept : state.outer = true)
    (left : l.check = true) (right : u.check = true) {x : ℝ}
    (inside : x ∈ Set.Icc l.value u.value) : x ∈ Set.Icc (lo : ℝ) hi := by
  have facts : lo ≤ l.lower ∧ u.upper ≤ hi := by simpa [bounds, kept] using checked
  exact ⟨(by exact_mod_cast facts.1 : (lo : ℝ) ≤ l.lower).trans
      ((point_bounds left).1.trans inside.1),
    inside.2.trans ((point_bounds right).2.trans (by exact_mod_cast facts.2))⟩

theorem boundsFrom_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {lo hi : ℚ} {l : Point} {chain : Chain}
    (leaves : checkFrom observed r l chain = true)
    (checked : boundsFrom lo hi l chain = true) :
    ∀ s ∈ selectedFrom State.outer l chain, (s : ℝ) ∈ Set.Icc (lo : ℝ) hi := by
  induction chain generalizing l with
  | last gap =>
    intro s hs
    have domain := Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp leaves).1
    have endpoints := Bool.and_eq_true_iff.mp domain.1
    apply bounds_sound checked hs.1 endpoints.1 endpoints.2
    simpa only [Point.value, Rat.cast_one, Set.mem_Icc] using And.intro hs.2.1.le hs.2.2.le
  | next p gap single rest ih =>
    have lc : openCheck observed r l p gap = true ∧ pointCheck observed r p single = true ∧
        checkFrom observed r p rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, and_assoc] using leaves
    have bc : bounds lo hi l p gap.state = true ∧ bounds lo hi p p single.state = true ∧
        boundsFrom lo hi p rest = true := by
      simpa only [boundsFrom, Bool.and_eq_true, and_assoc] using checked
    have endpoints := Bool.and_eq_true_iff.mp
      (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp lc.1).1).1
    intro s hs
    rcases hs with (gapMember | pointMember) | tailMember
    · exact bounds_sound bc.1 gapMember.1 endpoints.1 endpoints.2
        ⟨gapMember.2.1.le, gapMember.2.2.le⟩
    · exact bounds_sound bc.2.1 pointMember.1 endpoints.2 endpoints.2
        (by rw [pointMember.2]; exact ⟨le_rfl, le_rfl⟩)
    · exact ih lc.2.2 bc.2.2 s tailMember

noncomputable def interval (lo hi : ℚ) : Set Compact := {s | (lo : ℝ) ≤ s ∧ (s : ℝ) ≤ hi}

def outerCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r lo hi : ℚ)
    (chain : Chain) : Bool :=
  decide (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) &&
    (if Structural.check .zero r observed then decide (lo ≤ 0 ∧ 0 ≤ hi) else true) &&
    (if Structural.check .infinity r observed then decide (lo ≤ 1 ∧ 1 ≤ hi) else true) &&
    boundsFrom lo hi (.rational 0) chain

theorem outerCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r lo hi : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (checked : outerCheck observed r lo hi chain = true) :
    (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) ∧ outerCells observed r chain ⊆ interval lo hi := by
  have parts : (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) ∧
      (if Structural.check .zero r observed then decide (lo ≤ 0 ∧ 0 ≤ hi) else true) = true ∧
      (if Structural.check .infinity r observed then decide (lo ≤ 1 ∧ 1 ≤ hi) else true) = true ∧
      boundsFrom lo hi (.rational 0) chain = true := by
    simpa only [outerCheck, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  refine ⟨parts.1, ?_⟩
  intro s hs
  rcases hs with (zero | one) | finite
  · have b : lo ≤ 0 ∧ 0 ≤ hi := by simpa [zero.1] using parts.2.1
    rw [zero.2]
    change (lo : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ hi
    exact_mod_cast b
  · have b : lo ≤ 1 ∧ 1 ≤ hi := by simpa [one.1] using parts.2.2.1
    rw [one.2]
    change (lo : ℝ) ≤ 1 ∧ (1 : ℝ) ≤ hi
    exact_mod_cast b
  · exact boundsFrom_sound (Bool.and_eq_true_iff.mp leaves).2 parts.2.2.2 s finite

end ExactCIs.Unconditional.GlobalCheckerEnclosure
