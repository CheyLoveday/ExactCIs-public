/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalPartition
import ExactCIs.Unconditional.GlobalCheckerCore

/-! # Charged T1-min hull, structural/full/empty terminal conditions

Every endpoint comparison and compact-to-beta arithmetic operation is charged.
Anchor resolution traverses the actual accepted leaves, never a producer claim.
-/
namespace ExactCIs.Unconditional.MeteredGlobalTerminal
open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay
open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition
open GlobalCheckerAnchor GlobalCheckerHull

def sub (a b : Rat) : Program Rat :=
  compose (MeteredRationalReplay.ratSub a b) (fun _ => a-b)
    (MeteredRationalReplay.ratSub_safe _ _) (MeteredRationalReplay.ratSub_refines _ _)
@[simp] theorem erase_sub (a b : Rat) : (sub a b).erase = a-b := rfl

def beta (x : Rat) : Program Rat := do
  let denominator ← sub 1 x
  MeteredDecodeInput.divide x denominator
@[simp] theorem erase_beta (x : Rat) : (beta x).erase = x/(1-x) := by simp [beta]

def betaExcess (outer inner epsilon : Rat) : Program Bool := do
  let a ← beta outer
  let b ← beta inner
  let difference ← sub a b
  le difference epsilon
@[simp] theorem erase_betaExcess (outer inner epsilon : Rat) :
    (betaExcess outer inner epsilon).erase = decide (outer/(1-outer)-inner/(1-inner) ≤ epsilon) := by
  simp [betaExcess]

def bounds (lo hi : Rat) (l u : Point) (state : State) : Program Bool := visit fun _ =>
  if state.outer then andThen (le lo l.lower) fun _ => le u.upper hi else pure true
@[simp] theorem erase_bounds (lo hi : Rat) (l u : Point) (state : State) :
    (bounds lo hi l u state).erase = GlobalCheckerEnclosure.bounds lo hi l u state := by
  simp [bounds, GlobalCheckerEnclosure.bounds, Bool.decide_and]

def boundsFrom (lo hi : Rat) (l : Point) (chain : Chain) : Program Bool := visit fun _ =>
  match chain with
  | .last gap => bounds lo hi l (.rational 1) gap.state
  | .next p gap single rest => andThen (bounds lo hi l p gap.state) fun _ =>
    andThen (bounds lo hi p p single.state) fun _ => boundsFrom lo hi p rest
@[simp] theorem erase_boundsFrom (lo hi : Rat) (l : Point) (chain : Chain) :
    (boundsFrom lo hi l chain).erase = GlobalCheckerEnclosure.boundsFrom lo hi l chain := by
  induction chain generalizing l <;>
    simp_all [boundsFrom, GlobalCheckerEnclosure.boundsFrom, Bool.and_assoc]

def outer {n1 n0 : Nat} (observed : Outcome n1 n0) (r lo hi : Rat) (chain : Chain) : Program Bool :=
  andThen (andThen (le 0 lo) fun _ => andThen (le lo hi) fun _ => le hi 1) fun _ =>
    andThen (do
      let accepted ← MeteredGlobalPartition.structural observed r .zero
      if accepted then andThen (le lo 0) fun _ => le 0 hi else pure true) fun _ =>
        andThen (do
          let accepted ← MeteredGlobalPartition.structural observed r .infinity
          if accepted then andThen (le lo 1) fun _ => le 1 hi else pure true) fun _ =>
            boundsFrom lo hi (.rational 0) chain
@[simp] theorem erase_outer {n1 n0 : Nat} (observed : Outcome n1 n0) (r lo hi : Rat) (chain : Chain) :
    (outer observed r lo hi chain).erase = GlobalCheckerEnclosure.outerCheck observed r lo hi chain := by
  simp [outer, GlobalCheckerEnclosure.outerCheck, Bool.decide_and, Bool.and_assoc]

def resolveFrom (l : Point) (chain : Chain) (anchor : Anchor) : Program (Option Point) :=
  visit fun _ => match l,chain,anchor with
  | l,.last gap,.rational q 0 => do
    let checked ← andThen (metadata fun _ => gap.state.inner) fun _ =>
      MeteredOpenReplay.sample l (.rational 1) q
    pure (if checked then some (.rational q) else none)
  | _,.last _,_ => pure none
  | l,.next p gap _ _,.rational q 0 => do
    let checked ← andThen (metadata fun _ => gap.state.inner) fun _ => MeteredOpenReplay.sample l p q
    pure (if checked then some (.rational q) else none)
  | _,.next p _ _ rest,.rational q (i+1) => resolveFrom p rest (.rational q i)
  | _,.next p _ single _,.point 0 => metadata fun _ => if single.state.inner then some p else none
  | _,.next p _ _ rest,.point (i+1) => resolveFrom p rest (.point i)
@[simp] theorem erase_resolveFrom (l : Point) (chain : Chain) (anchor : Anchor) :
    (resolveFrom l chain anchor).erase = GlobalCheckerAnchor.resolveFrom l chain anchor := by
  induction chain generalizing l anchor with
  | last gap => cases anchor with
    | rational q i => cases i <;> simp [resolveFrom, GlobalCheckerAnchor.resolveFrom]
    | point i => simp [resolveFrom, GlobalCheckerAnchor.resolveFrom]
  | next p gap single rest ih => cases anchor with
    | rational q i => cases i <;> simp [resolveFrom, GlobalCheckerAnchor.resolveFrom, ih]
    | point i => cases i <;> simp [resolveFrom, GlobalCheckerAnchor.resolveFrom, ih]

def lower {n1 n0 : Nat} (observed : Outcome n1 n0) (r lo epsilon : Rat)
    (chain : Chain) (branch : Branch) : Program Bool := visit fun _ => match branch with
  | .structural e => andThen (MeteredGlobalPartition.structural observed r e) fun _ => eq lo (endpointRat e)
  | .finite anchor alo ahi => do
    let found ← resolveFrom (.rational 0) chain anchor
    match found with
    | none => pure false
    | some p =>
      andThen (le alo p.lower) fun _ =>
        andThen (le p.upper ahi) fun _ =>
          andThen (lt 0 lo) fun _ =>
            andThen (lt ahi 1) fun _ => betaExcess ahi lo epsilon
@[simp] theorem erase_lower {n1 n0 : Nat} (observed : Outcome n1 n0) (r lo epsilon : Rat)
    (chain : Chain) (branch : Branch) :
    (lower observed r lo epsilon chain branch).erase = GlobalCheckerHull.lowerCheck observed r lo epsilon chain branch := by
  cases branch <;> simp [lower, GlobalCheckerHull.lowerCheck, GlobalCheckerAnchor.resolve,
    Bool.decide_and, Bool.and_assoc]
  cases h : GlobalCheckerAnchor.resolveFrom (.rational 0) chain _ <;>
    simp [h, Bool.decide_and]

def upper {n1 n0 : Nat} (observed : Outcome n1 n0) (r hi epsilon : Rat)
    (chain : Chain) (branch : Branch) : Program Bool := visit fun _ => match branch with
  | .structural e => andThen (MeteredGlobalPartition.structural observed r e) fun _ => eq hi (endpointRat e)
  | .finite anchor alo ahi => do
    let found ← resolveFrom (.rational 0) chain anchor
    match found with
    | none => pure false
    | some p =>
      andThen (le alo p.lower) fun _ =>
        andThen (le p.upper ahi) fun _ =>
          andThen (lt 0 alo) fun _ =>
            andThen (lt hi 1) fun _ => betaExcess hi alo epsilon
@[simp] theorem erase_upper {n1 n0 : Nat} (observed : Outcome n1 n0) (r hi epsilon : Rat)
    (chain : Chain) (branch : Branch) :
    (upper observed r hi epsilon chain branch).erase = GlobalCheckerHull.upperCheck observed r hi epsilon chain branch := by
  cases branch <;> simp [upper, GlobalCheckerHull.upperCheck, GlobalCheckerAnchor.resolve,
    Bool.decide_and, Bool.and_assoc]
  cases h : GlobalCheckerAnchor.resolveFrom (.rational 0) chain _ <;>
    simp [h, Bool.decide_and]

def hull {n1 n0 : Nat} (observed : Outcome n1 n0) (r epsilon lo hi : Rat)
    (chain : Chain) (lb ub : Branch) : Program Bool :=
  andThen (le 0 epsilon) fun _ => andThen (outer observed r lo hi chain) fun _ =>
    andThen (lower observed r lo epsilon chain lb) fun _ => upper observed r hi epsilon chain ub
@[simp] theorem erase_hull {n1 n0 : Nat} (observed : Outcome n1 n0) (r epsilon lo hi : Rat)
    (chain : Chain) (lb ub : Branch) :
    (hull observed r epsilon lo hi chain lb ub).erase = GlobalCheckerHull.check observed r epsilon lo hi chain lb ub := by
  simp [hull, GlobalCheckerHull.check, Bool.and_assoc]

def terminal (input : GlobalCheckerCore.Input) (chain : Chain)
    (endState : GlobalCheckerCore.Terminal) : Program (Option GlobalCheckerCore.Result) := do
  let _ ← tickP .leafTransition
  visit fun _ => match endState with
  | .full => do
    let checked ← MeteredGlobalPartition.full (TableAt.of input.table) input.alphaSide chain
    pure (if checked then some .full else none)
  | .empty => do
    let checked ← MeteredGlobalPartition.empty (TableAt.of input.table) input.alphaSide chain
    pure (if checked then some .empty else none)
  | .hull lo hi lb ub => do
    let checked ← hull (TableAt.of input.table) input.alphaSide input.tolerance lo hi chain lb ub
    pure (if checked then some (.hull lo hi) else none)
@[simp] theorem erase_terminal (input : GlobalCheckerCore.Input) (chain : Chain)
    (endState : GlobalCheckerCore.Terminal) :
    (terminal input chain endState).erase = GlobalCheckerCore.terminalCheck input chain endState := by
  cases endState <;> simp [terminal, GlobalCheckerCore.terminalCheck]

end ExactCIs.Unconditional.MeteredGlobalTerminal
