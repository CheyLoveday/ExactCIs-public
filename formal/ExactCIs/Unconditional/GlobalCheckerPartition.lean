/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerLeaf
import ExactCIs.Unconditional.GlobalCheckerProjection

/-! # A complete partition assembled from finite candidate data

The recursive representation has exactly one singleton for each internal point
and one more open leaf than points. Decoding separate arrays rejects a length
mismatch. The two structural endpoints are computed independently. Every compact
effect receives one state; a supplied cover or enclosure proof is never used.
-/
namespace ExactCIs.Unconditional.GlobalCheckerPartition

open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf EffectCoordinate

inductive Chain where
  | last (gap : OpenLeaf)
  | next (point : Point) (gap : OpenLeaf) (single : PointLeaf) (rest : Chain)

def Chain.points : Chain → List Point
  | .last _ => []
  | .next p _ _ rest => p :: rest.points

def fromLists : List Point → List OpenLeaf → List PointLeaf → Option Chain
  | [], [gap], [] => some (.last gap)
  | p :: ps, gap :: gaps, single :: singles =>
      (fromLists ps gaps singles).map (.next p gap single)
  | _, _, _ => none

theorem fromLists_points {ps : List Point} {gaps : List OpenLeaf} {singles : List PointLeaf}
    {chain : Chain} (decoded : fromLists ps gaps singles = some chain) : chain.points = ps := by
  induction ps generalizing gaps singles chain with
  | nil =>
    cases gaps with
    | nil => simp [fromLists] at decoded
    | cons gap gaps =>
      cases gaps <;> cases singles <;> simp only [fromLists] at decoded <;> try contradiction
      case nil.nil => cases decoded; rfl
  | cons p ps ih =>
    cases gaps with
    | nil => simp [fromLists] at decoded
    | cons gap gaps =>
      cases singles with
      | nil => simp [fromLists] at decoded
      | cons single singles =>
        simp only [fromLists, Option.map_eq_some_iff] at decoded
        obtain ⟨tail, ht, rfl⟩ := decoded
        exact congrArg (List.cons p) (ih ht)

def checkFrom {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ) : Point → Chain → Bool
  | l, .last gap => openCheck observed r l (.rational 1) gap
  | l, .next p gap single rest => openCheck observed r l p gap &&
      pointCheck observed r p single && checkFrom observed r p rest

noncomputable def stateAt (x : ℝ) : Chain → State
  | .last gap => gap.state
  | .next p gap single rest =>
      if x < p.value then gap.state else if x = p.value then single.state else stateAt x rest

theorem checkFrom_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {l : Point} (checked : checkFrom observed r l chain = true)
    (s : Compact) (inside : (s : ℝ) ∈ Set.Ioo l.value 1) :
    Sound (stateAt s chain) (s ∈ CellEnclosure.actual observed r) := by
  induction chain generalizing l with
  | last gap =>
    exact openCheck_sound checked s (by simpa only [Point.value, Rat.cast_one] using inside)
  | next p gap single rest ih =>
    have parts : openCheck observed r l p gap = true ∧
        pointCheck observed r p single = true ∧ checkFrom observed r p rest = true := by
      simpa only [checkFrom, Bool.and_eq_true, and_assoc] using checked
    unfold stateAt
    split_ifs with before same
    · exact openCheck_sound parts.1 s ⟨inside.1, before⟩
    · exact pointCheck_sound parts.2.1 s same
    · exact ih parts.2.2 ⟨lt_of_le_of_ne (le_of_not_gt before) (Ne.symm same), inside.2⟩

def check {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) (order : List GlobalCheckerOrder.Witness) : Bool :=
  GlobalCheckerOrder.check chain.points order && checkFrom observed r (.rational 0) chain

def structuralState {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (e : Structural.Endpoint) : State :=
  if Structural.check e r observed then .accepted else .rejectedGreater

noncomputable def state {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) (s : Compact) : State :=
  if (s : ℝ) = 0 then structuralState observed r .zero
  else if (s : ℝ) = 1 then structuralState observed r .infinity
  else stateAt s chain

noncomputable def inner {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) : Set Compact := {s | (state observed r chain s).inner = true}

noncomputable def outer {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (chain : Chain) : Set Compact := {s | (state observed r chain s).outer = true}

theorem structuralState_sound {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ)
    (e : Structural.Endpoint) :
    Sound (structuralState observed r e)
      (GlobalHull.endpoint e ∈ CellEnclosure.actual observed r) := by
  unfold structuralState
  split_ifs with h
  · exact ⟨fun _ => (CellEnclosure.actual_structural _ _ _).mpr
      ((Structural.check_iff _ _ _).mp h), fun _ => rfl⟩
  · refine ⟨by simp [State.inner], ?_⟩
    intro accepted
    exact (h ((Structural.check_iff _ _ _).mpr
      ((CellEnclosure.actual_structural _ _ _).mp accepted))).elim

theorem check_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    (checked : check observed r chain order = true) :
    inner observed r chain ⊆ CellEnclosure.actual observed r ∧
      CellEnclosure.actual observed r ⊆ outer observed r chain := by
  have sound : ∀ s : Compact, Sound (state observed r chain s)
      (s ∈ CellEnclosure.actual observed r) := by
    intro s
    unfold state
    split_ifs with zero one
    · have equal : s = GlobalHull.endpoint .zero := Subtype.ext zero
      simpa only [equal] using structuralState_sound observed r .zero
    · have equal : s = GlobalHull.endpoint .infinity := Subtype.ext one
      simpa only [equal] using structuralState_sound observed r .infinity
    · apply checkFrom_sound (Bool.and_eq_true_iff.mp checked).2 s
      simpa only [Point.value, Rat.cast_zero, Set.mem_Ioo] using
        And.intro (lt_of_le_of_ne s.property.1 (Ne.symm zero))
          (lt_of_le_of_ne s.property.2 one)
  exact ⟨fun s hs => (sound s).1 hs, fun s hs => (sound s).2 hs⟩

def allStates (f : State → Bool) : Chain → Bool
  | .last gap => f gap.state
  | .next _ gap single rest => f gap.state && f single.state && allStates f rest

theorem allStates_sound {f : State → Bool} {chain : Chain}
    (checked : allStates f chain = true) (x : ℝ) : f (stateAt x chain) = true := by
  induction chain with
  | last gap => exact checked
  | next p gap single rest ih =>
    have parts : f gap.state = true ∧ f single.state = true ∧ allStates f rest = true := by
      simpa only [allStates, Bool.and_eq_true, and_assoc] using checked
    unfold stateAt
    split_ifs
    · exact parts.1
    · exact parts.2.1
    · exact ih parts.2.2

def fullCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ) (chain : Chain) : Bool :=
  Structural.check .zero r observed && Structural.check .infinity r observed &&
    allStates State.inner chain

def emptyCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ) (chain : Chain) : Bool :=
  !Structural.check .zero r observed && !Structural.check .infinity r observed &&
    allStates (fun s => !s.outer) chain

theorem fullCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ} {chain : Chain}
    (checked : fullCheck observed r chain = true) : inner observed r chain = Set.univ := by
  have parts : Structural.check .zero r observed = true ∧
      Structural.check .infinity r observed = true ∧ allStates State.inner chain = true := by
    simpa only [fullCheck, Bool.and_eq_true, and_assoc] using checked
  apply Set.eq_univ_iff_forall.mpr
  intro s
  change (state observed r chain s).inner = true
  unfold state
  split_ifs
  · simp [structuralState, parts.1, State.inner]
  · simp [structuralState, parts.2.1, State.inner]
  · exact allStates_sound parts.2.2 s

theorem emptyCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ} {chain : Chain}
    (checked : emptyCheck observed r chain = true) : outer observed r chain = ∅ := by
  have parts : Structural.check .zero r observed = false ∧
      Structural.check .infinity r observed = false ∧
      allStates (fun s => !s.outer) chain = true := by
    simpa only [emptyCheck, Bool.and_eq_true, Bool.not_eq_true_eq_eq_false, and_assoc]
      using checked
  apply Set.eq_empty_iff_forall_notMem.mpr
  intro s
  change (state observed r chain s).outer ≠ true
  unfold state
  split_ifs
  · simp [structuralState, parts.1, State.outer]
  · simp [structuralState, parts.2.1, State.outer]
  · have h := allStates_sound parts.2.2 (s : ℝ)
    exact Bool.eq_false_iff.mp (Bool.eq_false_of_not_eq_true' h)

theorem full_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    (checked : check observed r chain order = true)
    (terminal : fullCheck observed r chain = true) :
    CellEnclosure.actual observed r = Set.univ := by
  exact Set.eq_univ_of_univ_subset (fullCheck_sound terminal ▸ (check_sound checked).1)

theorem empty_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    (checked : check observed r chain order = true)
    (terminal : emptyCheck observed r chain = true) :
    CellEnclosure.actual observed r = ∅ := by
  exact Set.subset_empty_iff.mp (emptyCheck_sound terminal ▸ (check_sound checked).2)

end ExactCIs.Unconditional.GlobalCheckerPartition
