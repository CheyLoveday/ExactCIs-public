/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalOrder
import ExactCIs.Unconditional.MeteredOpenReplay
import ExactCIs.Unconditional.MeteredParametricReplay
import ExactCIs.Unconditional.MeteredSpecializedRootReplay
import ExactCIs.Unconditional.GlobalCheckerLeaf

/-! # Charged decisions for every real effect in open cells and singletons

The masks and signed objectives are reconstructed using the concrete charged
polynomial code. No pure decision or certificate predicate is an atomic body.
-/
namespace ExactCIs.Unconditional.MeteredGlobalDecision
open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay
open ProductBinomial BoschlooOrdering GlobalCheckerPoint RootCertificate

@[simp] theorem erase_if {α : Type} (p : Prop) [Decidable p] (a b : Program α) :
    (if p then a else b).erase = if p then a.erase else b.erase := by
  split <;> rfl

def index {n1 n0 : Nat} (o : Outcome n1 n0) : Program Nat := do
  let width ← MeteredDecodeInput.natAdd n0 1
  let offset ← MeteredGlobalPolynomials.natMul o.1.val width
  MeteredDecodeInput.natAdd offset o.2.val
@[simp] theorem erase_index {n1 n0 : Nat} (o : Outcome n1 n0) :
    (index o).erase = GlobalCheckerOpenDecision.index o := by
  simp [index, GlobalCheckerOpenDecision.index]

def grid (n1 n0 : Nat) : Program Nat := do
  let a ← MeteredDecodeInput.natAdd n1 1
  let b ← MeteredDecodeInput.natAdd n0 1
  MeteredGlobalPolynomials.natMul a b
@[simp] theorem erase_grid (n1 n0 : Nat) : (grid n1 n0).erase = (n1+1)*(n0+1) := by
  simp [grid]

def openWitness {n1 n0 : Nat} (ws : List GlobalCheckerOpenSign.Witness)
    (o : Outcome n1 n0) : Program GlobalCheckerOpenSign.Witness := do
  let i ← index o
  let w ← MeteredGlobalList.get ws i
  metadata fun _ => w.getD .identityZero
@[simp] theorem erase_openWitness {n1 n0 : Nat} (ws : List GlobalCheckerOpenSign.Witness)
    (o : Outcome n1 n0) :
    (openWitness ws o).erase = GlobalCheckerOpenDecision.orderingWitness ws o := by
  simp [openWitness, GlobalCheckerOpenDecision.orderingWitness]

def pointWitness {n1 n0 : Nat} (ws : List SignWitness) (o : Outcome n1 n0) :
    Program SignWitness := do
  let i ← index o
  let w ← MeteredGlobalList.get ws i
  metadata fun _ => w.getD .rational
@[simp] theorem erase_pointWitness {n1 n0 : Nat} (ws : List SignWitness)
    (o : Outcome n1 n0) :
    (pointWitness ws o).erase = GlobalCheckerPointDecision.witness ws o := by
  simp [pointWitness, GlobalCheckerPointDecision.witness,
    GlobalCheckerPointDecision.index, GlobalCheckerOpenDecision.index]

def openMask (n1 n0 : Nat) (ws : List GlobalCheckerOpenSign.Witness) :
    Program (Finset (Outcome n1 n0)) := do
  let space ← MeteredGlobalList.sampleUniverse n1 n0
  MeteredGlobalList.filterOutcomes space fun o => do
    let w ← openWitness ws o
    metadata fun _ => decide (w.sign ≠ 1)
@[simp] theorem erase_openMask (n1 n0 : Nat) (ws : List GlobalCheckerOpenSign.Witness) :
    (openMask n1 n0 ws).erase = GlobalCheckerOpenDecision.certifiedMask n1 n0 ws := by
  simp [openMask, GlobalCheckerOpenDecision.certifiedMask]

def pointMask {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ws : List SignWitness) : Program (Finset (Outcome n1 n0)) := do
  let space ← MeteredGlobalList.sampleUniverse n1 n0
  MeteredGlobalList.filterOutcomes space fun o => do
    let h ← MeteredGlobalPolynomials.comparison dir o observed
    let w ← pointWitness ws o
    let answer ← pointSign h p w
    metadata fun _ => decide (answer.getD 0 ≠ 1)
@[simp] theorem erase_pointMask {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ws : List SignWitness) :
    (pointMask dir observed p ws).erase =
      GlobalCheckerPointDecision.certifiedMask dir observed p ws := by
  simp [pointMask, GlobalCheckerPointDecision.certifiedMask,
    GlobalCheckerPointDecision.orderingSign] <;> rfl

def fullMask {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) : Program Bool := do
  let g ← grid n1 n0
  MeteredGlobalList.indexWork g (8*(g+1)*(g+1)) (fun _ => decide (mask = Finset.univ))
@[simp] theorem erase_fullMask {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) :
    (fullMask mask).erase = decide (mask = Finset.univ) := by simp [fullMask]

def openOrdering {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (l u : Point) (ws : List GlobalCheckerOpenSign.Witness) : Program Bool :=
  andThen (do
    let size ← MeteredGlobalList.length ws
    let expected ← grid n1 n0
    MeteredGlobalOrder.natEQ size expected) fun _ =>
      MeteredGlobalList.allOutcomes fun o => do
        let h ← MeteredGlobalPolynomials.comparison dir o observed
        let w ← openWitness ws o
        MeteredOpenReplay.sign h l u w
@[simp] theorem erase_openOrdering {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (l u : Point) (ws : List GlobalCheckerOpenSign.Witness) :
    (openOrdering dir observed l u ws).erase =
      GlobalCheckerOpenDecision.orderingCheck dir observed l u ws := by
  simp [openOrdering, GlobalCheckerOpenDecision.orderingCheck]

def pointOrdering {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ws : List SignWitness) : Program Bool :=
  andThen (do
    let size ← MeteredGlobalList.length ws
    let expected ← grid n1 n0
    MeteredGlobalOrder.natEQ size expected) fun _ =>
      MeteredGlobalList.allOutcomes fun o => do
        let h ← MeteredGlobalPolynomials.comparison dir o observed
        let w ← pointWitness ws o
        let answer ← pointSign h p w
        metadata fun _ => answer.isSome
@[simp] theorem erase_pointOrdering {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0)
    (p : Point) (ws : List SignWitness) :
    (pointOrdering dir observed p ws).erase =
      GlobalCheckerPointDecision.orderingCheck dir observed p ws := by
  simp [pointOrdering, GlobalCheckerPointDecision.orderingCheck]

def domain (l u : Point) : Program Bool :=
  andThen (point l) fun _ => andThen (point u) fun _ =>
    andThen (le 0 l.lower) fun _ => le u.upper 1
@[simp] theorem erase_domain (l u : Point) :
    (domain l u).erase = GlobalCheckerOpenDecision.domainCheck l u := by
  simp [domain, GlobalCheckerOpenDecision.domainCheck, Bool.decide_and, Bool.and_assoc]

def nuisanceCount (left right : List GlobalCheckerOpenSign.Witness) : Program Nat := do
  let ls ← MeteredGlobalList.map (fun w => metadata fun _ => w.sign) left
  let rs ← MeteredGlobalList.map (fun w => metadata fun _ => w.sign) right
  let lv ← MeteredOpenReplay.variations ls
  let rv ← MeteredOpenReplay.variations rs
  MeteredGlobalPolynomials.natSub lv rv
@[simp] theorem erase_nuisanceCount (left right : List GlobalCheckerOpenSign.Witness) :
    (nuisanceCount left right).erase = GlobalCheckerOpenSign.nuisanceCount left right := by
  simp [nuisanceCount, GlobalCheckerOpenSign.nuisanceCount]

def openRootGuards (r : Rat) (full : Bool) (l u : Point) (h : B)
    (b : GlobalCheckerOpenDecision.RootBranch) : Program Bool :=
  andThen (lt 0 r) fun _ => andThen (metadata fun _ => !full) fun _ =>
    andThen (do let p ← atRational h 0; MeteredOpenReplay.sign p l u b.originalLeft) fun _ =>
      andThen (metadata fun _ => decide (b.originalLeft.sign = -1)) fun _ =>
        andThen (do let p ← atRational h 1; MeteredOpenReplay.sign p l u b.originalRight) fun _ =>
          andThen (metadata fun _ => decide (b.originalRight.sign = -1)) fun _ =>
            andThen (MeteredParametricReplay.check l u h b.root) fun _ =>
              andThen (MeteredOpenReplay.signs l u 0 (b.root.representative :: b.root.tail) b.left)
                fun _ => MeteredOpenReplay.signs l u 1
                  (b.root.representative :: b.root.tail) b.right

def openDecision {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0) (r : Rat)
    (l u : Point) (c : GlobalCheckerOpenDecision.Certificate) : Program (Option Bool) := do
  let checked ← andThen (domain l u) fun _ => openOrdering dir observed l u c.ordering
  if checked then
    let m ← openMask n1 n0 c.ordering
    visit fun _ => match c.branch with
    | .fullMask => do
      let full ← fullMask m
      if full then do let accepted ← le r 1; pure (some accepted) else pure none
    | .zeroLevel => do let zero ← eq r 0; pure (if zero then some true else none)
    | .interiorRoot b => do
      let h ← MeteredGlobalPolynomials.objective m r
      let full ← fullMask m
      let checked ← openRootGuards r full l u h b
      if checked then do
        let count ← nuisanceCount b.left b.right
        let accepted ← MeteredDecodeInput.positiveNat count
        pure (some accepted)
      else pure none
  else pure none
@[simp] theorem erase_openDecision {n1 n0 : Nat} (dir : Direction)
    (observed : Outcome n1 n0) (r : Rat) (l u : Point)
    (c : GlobalCheckerOpenDecision.Certificate) :
    (openDecision dir observed r l u c).erase =
      GlobalCheckerOpenDecision.check dir observed r l u c := by
  simp only [openDecision, erase_monadic_bind, erase_andThen, erase_domain,
    erase_openOrdering, erase_openMask]
  split <;> simp only [GlobalCheckerOpenDecision.check, *]
  · cases c.branch <;> simp [openRootGuards, Bool.decide_and, Bool.and_assoc]
  · rfl

def specialize (x : Rat) (h : B) : Program Coefficients :=
  MeteredGlobalList.map (fun p => value p x) h
@[simp] theorem erase_specialize (x : Rat) (h : B) :
    (specialize x h).erase = GlobalCheckerPointDecision.specializeRational x h := by
  simp [specialize, GlobalCheckerPointDecision.specializeRational]

def rootSign (h : Coefficients) (lo hi : Rat) (c : RootCountCertificate.Certificate) :
    Program (Option Bool) :=
  compose (MeteredRationalReplay.signCheck h lo hi c)
    (fun _ => RootSignCertificate.check h lo hi c)
    (MeteredRationalReplay.signCheck_safe _ _ _ _)
    (MeteredRationalReplay.signCheck_refines _ _ _ _)
@[simp] theorem erase_rootSign (h : Coefficients) (lo hi : Rat)
    (c : RootCountCertificate.Certificate) :
    (rootSign h lo hi c).erase = RootSignCertificate.check h lo hi c := rfl

def algebraicDecision (a : SelectedRoot.Root) (h : B)
    (c : GlobalCheckerPointDecision.AlgebraicBranch) : Program (Option Bool) := do
  let checked ← andThen (selectedRoot a) fun _ => MeteredSpecializedRootReplay.check a.definer h c.root
  if checked then
    let p ← atRational h 0
    let original ← pointSign p (.algebraic a) c.original
    if original = some (-1) then
      let leftPolys ← MeteredGlobalList.map (fun p => atRational p 0)
        (c.root.representative :: c.root.tail)
      let ls ← MeteredOpenReplay.pointSigns (.algebraic a) leftPolys c.left
      match ls with
      | none => pure none
      | some ls => do
        let rightPolys ← MeteredGlobalList.map (fun p => atRational p 1)
          (c.root.representative :: c.root.tail)
        let rs ← MeteredOpenReplay.pointSigns (.algebraic a) rightPolys c.right
        match rs with
        | none => pure none
        | some rs => do
          let lv ← MeteredOpenReplay.variations ls
          let rv ← MeteredOpenReplay.variations rs
          let count ← MeteredGlobalPolynomials.natSub lv rv
          let accepted ← MeteredDecodeInput.positiveNat count
          pure (some accepted)
    else pure none
  else pure none
@[simp] theorem erase_algebraicDecision (a : SelectedRoot.Root) (h : B)
    (c : GlobalCheckerPointDecision.AlgebraicBranch) :
    (algebraicDecision a h c).erase = GlobalCheckerPointDecision.algebraicCheck a h c := by
  by_cases h0 : (a.check && AlgebraicRootCertificate.check a.definer h c.root) = true
  · by_cases h1 : GlobalCheckerPoint.sign (AlgebraicSignReplay.atRational h 0)
        (.algebraic a) c.original = some (-1)
    · cases hl : GlobalCheckerPoint.signs (.algebraic a)
          ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 0)
          c.left <;>
        cases hr : GlobalCheckerPoint.signs (.algebraic a)
          ((c.root.representative :: c.root.tail).map fun p => AlgebraicSignReplay.atRational p 1)
          c.right <;>
        simp only [List.map_cons] at hl hr <;>
        simp [algebraicDecision, GlobalCheckerPointDecision.algebraicCheck, h0, h1, hl, hr] <;> rfl
    · simp [algebraicDecision, GlobalCheckerPointDecision.algebraicCheck, h0, h1]
  · simp [algebraicDecision, GlobalCheckerPointDecision.algebraicCheck, h0]

def pointDecision {n1 n0 : Nat} (dir : Direction) (observed : Outcome n1 n0) (r : Rat)
    (p : Point) (c : GlobalCheckerPointDecision.Certificate) : Program (Option Bool) := do
  let checked ← andThen (MeteredGlobalOrder.interior p) fun _ => pointOrdering dir observed p c.ordering
  if checked then
    let m ← pointMask dir observed p c.ordering
    let h ← MeteredGlobalPolynomials.objective m r
    visit fun _ => match c.branch with
    | .fullMask => do
      let full ← fullMask m
      if full then do let accepted ← le r 1; pure (some accepted) else pure none
    | .zeroLevel => do let zero ← eq r 0; pure (if zero then some true else none)
    | .rationalRoot root => match p with
      | .algebraic _ => pure none
      | .rational x => do
        let hs ← specialize x h
        let checked ← andThen (lt 0 r) fun _ => andThen (do
          let full ← fullMask m; metadata fun _ => !full) fun _ =>
            andThen (do let left ← value hs 0; lt left 0) fun _ =>
              do let right ← value hs 1; lt right 0
        if checked then rootSign hs 0 1 root else pure none
    | .algebraicRoot branch => match p with
      | .rational _ => pure none
      | .algebraic a => do
        let checked ← andThen (lt 0 r) fun _ => do
          let full ← fullMask m; metadata fun _ => !full
        if checked then algebraicDecision a h branch else pure none
  else pure none
@[simp] theorem erase_pointDecision {n1 n0 : Nat} (dir : Direction)
    (observed : Outcome n1 n0) (r : Rat) (p : Point)
    (c : GlobalCheckerPointDecision.Certificate) :
    (pointDecision dir observed r p c).erase =
      GlobalCheckerPointDecision.check dir observed r p c := by
  simp only [pointDecision, erase_monadic_bind, erase_andThen,
    MeteredGlobalOrder.erase_interior, erase_pointOrdering, erase_pointMask,
    MeteredGlobalPolynomials.erase_objective]
  split <;> simp only [GlobalCheckerPointDecision.check, *]
  · cases c.branch <;> cases p <;> simp [Bool.decide_and, Bool.and_assoc]
  · rfl

end ExactCIs.Unconditional.MeteredGlobalDecision
