/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalDecision
import ExactCIs.Unconditional.GlobalCheckerFamily

/-! # Charged reconstruction of the full required projection family

Trailing-zero trimming and exact signed coefficient-list deduplication use
charged rational equality. No root-set or monic normalization changes a sign.
-/
namespace ExactCIs.Unconditional.MeteredGlobalFamily
open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay
open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition RootCertificate

def coefficientsEQ (p q : Coefficients) : Program Bool := visit fun _ => match p,q with
  | [], [] => pure true
  | a::ps, b::qs => andThen (eq a b) fun _ => coefficientsEQ ps qs
  | _,_ => pure false
@[simp] theorem erase_coefficientsEQ (p q : Coefficients) :
    (coefficientsEQ p q).erase = decide (p=q) := by
  induction p generalizing q with
  | nil => cases q <;> simp [coefficientsEQ]
  | cons a ps ih => cases q <;> simp [coefficientsEQ, ih, Bool.decide_and]

def coefficientCons (c : Rat) (cs : Coefficients) : Program Coefficients :=
  compose (MeteredRationalReplay.cons c cs) (fun _ => c::cs)
    (MeteredRationalReplay.cons_safe _ _) (MeteredRationalReplay.cons_refines _ _)
@[simp] theorem erase_coefficientCons (c : Rat) (cs : Coefficients) :
    (coefficientCons c cs).erase = c::cs := rfl

def trim (p : Coefficients) : Program Coefficients := visit fun _ => match p with
  | [] => pure []
  | c::cs => do
    let tail ← trim cs
    let zero ← andThen (metadata fun _ => tail.isEmpty) fun _ => eq c 0
    if zero then pure [] else coefficientCons c tail
@[simp] theorem erase_trim (p : Coefficients) :
    (trim p).erase = CanonicalEncoding.trim p := by
  induction p <;> simp_all [trim, CanonicalEncoding.trim, Bool.decide_and]

def dropEmpty (ps : List Coefficients) : Program (List Coefficients) := visit fun _ => match ps with
  | [] => pure []
  | p::ps => do
    let tail ← dropEmpty ps
    metadata fun _ => if p.isEmpty then tail else p::tail
@[simp] theorem erase_dropEmpty (ps : List Coefficients) :
    (dropEmpty ps).erase = ps.filter (fun p => p != []) := by
  induction ps with
  | nil => simp [dropEmpty]
  | cons p ps ih => cases p <;> simp [dropEmpty, ih]

def dedup (ps : List Coefficients) : Program (List Coefficients) := visit fun _ => match ps with
  | [] => pure []
  | p::ps => do
    let duplicate ← MeteredGlobalList.any (coefficientsEQ p) ps
    let tail ← dedup ps
    metadata fun _ => if duplicate then tail else p::tail
@[simp] theorem erase_dedup (ps : List Coefficients) :
    (dedup ps).erase = ps.dedup := by
  induction ps <;> simp_all [dedup, List.dedup_cons]

def normalize (ps : List Coefficients) : Program (List Coefficients) := do
  let trimmed ← MeteredGlobalList.map (fun p => do
    let _ ← tickP .projectionPolynomial
    trim p) ps
  let nonempty ← dropEmpty trimmed
  dedup nonempty
@[simp] theorem erase_normalize (ps : List Coefficients) :
    (normalize ps).erase = GlobalCheckerFamily.normalize ps := by
  simp [normalize, GlobalCheckerFamily.normalize]

def finRange (n : Nat) : Program (List (Fin n)) :=
  MeteredGlobalList.indexWork n (4*n+1) (fun _ => List.finRange n)
@[simp] theorem erase_finRange (n : Nat) : (finRange n).erase = List.finRange n := rfl

def comparisons {n1 n0 : Nat} (observed : Outcome n1 n0) : Program (List Coefficients) := do
  let xs ← finRange (n1+1)
  let rows ← MeteredGlobalList.map (fun x => do
    let ys ← finRange (n0+1)
    let pairs ← MeteredGlobalList.map (fun y => do
      let greater ← MeteredGlobalPolynomials.comparison .greater (x,y) observed
      let less ← MeteredGlobalPolynomials.comparison .less (x,y) observed
      metadata fun _ => [greater,less]) ys
    MeteredGlobalList.flatten pairs) xs
  MeteredGlobalList.flatten rows
@[simp] theorem erase_comparisons {n1 n0 : Nat} (observed : Outcome n1 n0) :
    (comparisons observed).erase = GlobalCheckerFamily.comparisons observed := by
  simp [comparisons, GlobalCheckerFamily.comparisons, List.flatMap]

def rootGuards (c : GlobalCheckerParametricRoot.Certificate) : Program (List Coefficients) := do
  let a ← MeteredGlobalList.append [c.rootScale,c.powerScale,c.bezoutScale,c.last] c.representative
  let a ← MeteredGlobalList.append a c.quotient
  let a ← MeteredGlobalList.append a c.powerQuotient
  let a ← MeteredGlobalList.append a c.bezoutLeft
  let a ← MeteredGlobalList.append a c.bezoutRight
  let tails ← MeteredGlobalList.flatten c.tail
  let a ← MeteredGlobalList.append a tails
  let steps ← MeteredGlobalList.map (fun s => metadata fun _ => s.scale::s.quotient) c.steps
  let steps ← MeteredGlobalList.flatten steps
  let a ← MeteredGlobalList.append a steps
  let ends ← MeteredGlobalList.map (fun p => do
    let left ← atRational p 0
    let right ← atRational p 1
    metadata fun _ => [left,right]) (c.representative::c.tail)
  let ends ← MeteredGlobalList.flatten ends
  MeteredGlobalList.append a ends
@[simp] theorem erase_rootGuards (c : GlobalCheckerParametricRoot.Certificate) :
    (rootGuards c).erase = GlobalCheckerFamily.rootGuards c := by
  simp [rootGuards, GlobalCheckerFamily.rootGuards, List.flatMap]

def decisionGuards (n1 n0 : Nat) (r : Rat) (c : GlobalCheckerOpenDecision.Certificate) :
    Program (List Coefficients) := visit fun _ => match c.branch with
  | .fullMask | .zeroLevel => pure []
  | .interiorRoot branch => do
    let mask ← MeteredGlobalDecision.openMask n1 n0 c.ordering
    let h ← MeteredGlobalPolynomials.objective mask r
    let left ← atRational h 0
    let right ← atRational h 1
    let roots ← rootGuards branch.root
    let fields ← MeteredGlobalList.append [left,right] h
    MeteredGlobalList.append fields roots
@[simp] theorem erase_decisionGuards (n1 n0 : Nat) (r : Rat)
    (c : GlobalCheckerOpenDecision.Certificate) :
    (decisionGuards n1 n0 r c).erase =
      GlobalCheckerFamily.decisionGuards (n1:=n1) (n0:=n0) r c := by
  cases h : c.branch <;>
    simp [decisionGuards, GlobalCheckerFamily.decisionGuards, h, List.append_assoc]

def leafGuards (n1 n0 : Nat) (r : Rat) (leaf : OpenLeaf) : Program (List Coefficients) := do
  let packets ← MeteredGlobalList.append leaf.greater.toList leaf.less.toList
  let fields ← MeteredGlobalList.map (decisionGuards n1 n0 r) packets
  MeteredGlobalList.flatten fields
@[simp] theorem erase_leafGuards (n1 n0 : Nat) (r : Rat) (leaf : OpenLeaf) :
    (leafGuards n1 n0 r leaf).erase = GlobalCheckerFamily.leafGuards n1 n0 r leaf := by
  simp [leafGuards, GlobalCheckerFamily.leafGuards, List.flatMap]

def chainGuards (n1 n0 : Nat) (r : Rat) (chain : Chain) : Program (List Coefficients) :=
  visit fun _ => match chain with
  | .last gap => leafGuards n1 n0 r gap
  | .next _ gap _ rest => do
    let head ← leafGuards n1 n0 r gap
    let tail ← chainGuards n1 n0 r rest
    MeteredGlobalList.append head tail
@[simp] theorem erase_chainGuards (n1 n0 : Nat) (r : Rat) (chain : Chain) :
    (chainGuards n1 n0 r chain).erase = GlobalCheckerFamily.chainGuards n1 n0 r chain := by
  induction chain <;> simp_all [chainGuards, GlobalCheckerFamily.chainGuards]

def required {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat) (chain : Chain) :
    Program (List Coefficients) := do
  let a ← comparisons observed
  let b ← chainGuards n1 n0 r chain
  let combined ← MeteredGlobalList.append a b
  normalize combined
@[simp] theorem erase_required {n1 n0 : Nat} (observed : Outcome n1 n0) (r : Rat)
    (chain : Chain) : (required observed r chain).erase = GlobalCheckerFamily.required observed r chain := by
  simp [required, GlobalCheckerFamily.required]

def check (points : List Point) (family : List Coefficients)
    (covers : List GlobalCheckerProjection.Cover) : Program Bool :=
  andThen (MeteredGlobalList.all (MeteredGlobalOrder.cover points) covers) fun _ =>
    MeteredGlobalList.all (fun p => MeteredGlobalList.any
      (fun c => coefficientsEQ c.polynomial p) covers) family
@[simp] theorem erase_check (points : List Point) (family : List Coefficients)
    (covers : List GlobalCheckerProjection.Cover) :
    (check points family covers).erase = GlobalCheckerFamily.check points family covers := by
  simp [check, GlobalCheckerFamily.check]

end ExactCIs.Unconditional.MeteredGlobalFamily
