/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalFamily

/-! # Charged leaf layout and complete partition replay -/
namespace ExactCIs.Unconditional.MeteredGlobalPartition
open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay
open ProductBinomial BoschlooOrdering GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition

def leaf {C : Type} (f : Direction → C → Program (Option Bool)) (c : Leaf C) : Program Bool := do
  let _ ← tickP .leafTransition
  visit fun _ => match c.state,c.greater,c.less with
  | .accepted,some g,some l => do
    let greater ← f .greater g
    let less ← f .less l
    metadata fun _ => decide (greater = some true ∧ less = some true)
  | .rejectedGreater,some g,none => do
    let greater ← f .greater g
    metadata fun _ => decide (greater = some false)
  | .rejectedLess,none,some l => do
    let less ← f .less l
    metadata fun _ => decide (less = some false)
  | .boundary,none,none => pure true
  | _,_,_ => pure false
@[simp] theorem erase_leaf {C : Type} (f : Direction → C → Program (Option Bool)) (c : Leaf C) :
    (leaf f c).erase = GlobalCheckerLeaf.check (fun d c => (f d c).erase) c := by
  rcases c with ⟨state,g,l⟩
  cases state <;> cases g <;> cases l <;> simp [leaf, GlobalCheckerLeaf.check]

def openCheck {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (l u : Point) (c : OpenLeaf) : Program Bool :=
  andThen (MeteredGlobalDecision.domain l u) fun _ =>
    leaf (fun d => MeteredGlobalDecision.openDecision d observed r l u) c
@[simp] theorem erase_openCheck {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (l u : Point) (c : OpenLeaf) :
    (openCheck observed r l u c).erase = GlobalCheckerLeaf.openCheck observed r l u c := by
  simp [openCheck, GlobalCheckerLeaf.openCheck]

def pointCheck {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (p : Point) (c : PointLeaf) : Program Bool :=
  andThen (MeteredGlobalOrder.interior p) fun _ =>
    leaf (fun d => MeteredGlobalDecision.pointDecision d observed r p) c
@[simp] theorem erase_pointCheck {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (p : Point) (c : PointLeaf) :
    (pointCheck observed r p c).erase = GlobalCheckerLeaf.pointCheck observed r p c := by
  simp [pointCheck, GlobalCheckerLeaf.pointCheck]

def fromLists (ps : List Point) (gaps : List OpenLeaf) (singles : List PointLeaf) :
    Program (Option Chain) := visit fun _ => match ps,gaps,singles with
  | [],[gap],[] => pure (some (.last gap))
  | p::ps,gap::gaps,single::singles => do
    let rest ← fromLists ps gaps singles
    metadata fun _ => rest.map (.next p gap single)
  | _,_,_ => pure none
@[simp] theorem erase_fromLists (ps : List Point) (gaps : List OpenLeaf) (singles : List PointLeaf) :
    (fromLists ps gaps singles).erase = GlobalCheckerPartition.fromLists ps gaps singles := by
  induction ps generalizing gaps singles with
  | nil => cases gaps with
    | nil => cases singles <;> simp [fromLists, GlobalCheckerPartition.fromLists]
    | cons g gs => cases gs <;> cases singles <;> simp [fromLists, GlobalCheckerPartition.fromLists]
  | cons p ps ih => cases gaps <;> cases singles <;>
    simp [fromLists, GlobalCheckerPartition.fromLists, ih]

def points (chain : Chain) : Program (List Point) := visit fun _ => match chain with
  | .last _ => pure []
  | .next p _ _ rest => do
    let tail ← points rest
    metadata fun _ => p::tail
@[simp] theorem erase_points (chain : Chain) : (points chain).erase = chain.points := by
  induction chain <;> simp_all [points, Chain.points]

def checkFrom {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (l : Point) (chain : Chain) : Program Bool := visit fun _ => match chain with
  | .last gap => openCheck observed r l (.rational 1) gap
  | .next p gap single rest => andThen (openCheck observed r l p gap) fun _ =>
    andThen (pointCheck observed r p single) fun _ => checkFrom observed r p rest
@[simp] theorem erase_checkFrom {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (l : Point) (chain : Chain) :
    (checkFrom observed r l chain).erase = GlobalCheckerPartition.checkFrom observed r l chain := by
  induction chain generalizing l <;>
    simp_all [checkFrom, GlobalCheckerPartition.checkFrom, Bool.and_assoc]

def check {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (chain : Chain) (order : List GlobalCheckerOrder.Witness) : Program Bool :=
  andThen (do let ps ← points chain; MeteredGlobalOrder.order ps order) fun _ =>
    checkFrom observed r (.rational 0) chain
@[simp] theorem erase_check {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (chain : Chain) (order : List GlobalCheckerOrder.Witness) :
    (check observed r chain order).erase = GlobalCheckerPartition.check observed r chain order := by
  simp [check, GlobalCheckerPartition.check]

def structural {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (e : Structural.Endpoint) : Program Bool := do
  let limits ← MeteredGlobalList.indexWork 0 8 (fun _ => Structural.pair e observed)
  andThen (le r limits.1) fun _ => le r limits.2
@[simp] theorem erase_structural {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (e : Structural.Endpoint) : (structural observed r e).erase = Structural.check e r observed := by
  simp [structural, Structural.check, Bool.decide_and]

def allStates (f : State → Bool) (chain : Chain) : Program Bool := visit fun _ => match chain with
  | .last gap => metadata fun _ => f gap.state
  | .next _ gap single rest => andThen (metadata fun _ => f gap.state) fun _ =>
    andThen (metadata fun _ => f single.state) fun _ => allStates f rest
@[simp] theorem erase_allStates (f : State → Bool) (chain : Chain) :
    (allStates f chain).erase = GlobalCheckerPartition.allStates f chain := by
  induction chain <;> simp_all [allStates, GlobalCheckerPartition.allStates, Bool.and_assoc]

def full {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat) (chain : Chain) : Program Bool :=
  andThen (structural observed r .zero) fun _ =>
    andThen (structural observed r .infinity) fun _ => allStates State.inner chain
@[simp] theorem erase_full {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat) (chain : Chain) :
    (full observed r chain).erase = GlobalCheckerPartition.fullCheck observed r chain := by
  simp [full, GlobalCheckerPartition.fullCheck, Bool.and_assoc]

def empty {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat) (chain : Chain) : Program Bool :=
  andThen (do let zero ← structural observed r .zero; metadata fun _ => !zero) fun _ =>
    andThen (do let infinity ← structural observed r .infinity; metadata fun _ => !infinity)
      fun _ => allStates (fun s => !s.outer) chain
@[simp] theorem erase_empty {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat) (chain : Chain) :
    (empty observed r chain).erase = GlobalCheckerPartition.emptyCheck observed r chain := by
  simp [empty, GlobalCheckerPartition.emptyCheck, Bool.and_assoc]

end ExactCIs.Unconditional.MeteredGlobalPartition
