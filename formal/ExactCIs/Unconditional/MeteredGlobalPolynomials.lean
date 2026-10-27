/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalList
import ExactCIs.Unconditional.CompactPolynomial

/-! # Reconstruct the actual Boschloo comparison and threshold polynomials

Only finite support/index-set construction is delegated to index primitives.
Every binomial coefficient, natural conversion, rational operation, coefficient
cell and polynomial operation is charged before its concrete body executes.
-/
namespace ExactCIs.Unconditional.MeteredGlobalPolynomials
open ResourceModel MeteredProgram RootCertificate ProductBinomial BoschlooOrdering
open MeteredIntervalReplay MeteredAlgebraicReplay

abbrev P := Coefficients

def natMul (a b : Nat) : Program Nat :=
  compose (perform .integer (cost .integer 1
    (MeteredRationalReplay.natBits a + MeteredRationalReplay.natBits b + 1))
    (fun _ => a*b)) (fun _ => a*b) (perform_safe _ _ _) (perform_refines _ _ _)
@[simp] theorem erase_natMul (a b : Nat) : (natMul a b).erase = a*b := rfl

def natSub (a b : Nat) : Program Nat :=
  compose (perform .integer (cost .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b) + 1))
    (fun _ => a-b)) (fun _ => a-b) (perform_safe _ _ _) (perform_refines _ _ _)
@[simp] theorem erase_natSub (a b : Nat) : (natSub a b).erase = a-b := rfl

def natDiv (a b : Nat) : Program Nat :=
  compose (perform .integer (cost .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b) + 1))
    (fun _ => a/b)) (fun _ => a/b) (perform_safe _ _ _) (perform_refines _ _ _)
@[simp] theorem erase_natDiv (a b : Nat) : (natDiv a b).erase = a/b := rfl

def factorial (n : Nat) : Program Nat := visit fun _ => match n with
  | 0 => pure 1
  | n+1 => do let rest ← factorial n; natMul (n+1) rest
@[simp] theorem erase_factorial (n : Nat) : (factorial n).erase = n.factorial := by
  induction n <;> simp_all [factorial, Nat.factorial_succ]

def descFactorial (n k : Nat) : Program Nat := visit fun _ => match k with
  | 0 => pure 1
  | k+1 => do
    let factor ← natSub n k
    let rest ← descFactorial n k
    natMul factor rest
@[simp] theorem erase_descFactorial (n k : Nat) :
    (descFactorial n k).erase = n.descFactorial k := by
  induction k <;> simp_all [descFactorial, Nat.descFactorial_succ]

/-- The factorial loops expose every multiplication and the exact final division. -/
def choose (n k : Nat) : Program Nat := do
  let numerator ← descFactorial n k
  let denominator ← factorial k
  natDiv numerator denominator
@[simp] theorem erase_choose (n k : Nat) : (choose n k).erase = n.choose k := by
  simp [choose, Nat.choose_eq_descFactorial_div_factorial]

def ofNat (n : Nat) : Program Rat :=
  compose (MeteredRationalReplay.ratOfNat n) (fun _ => (n : Rat))
    (MeteredRationalReplay.ratOfNat_safe _) (MeteredRationalReplay.ratOfNat_refines _)
@[simp] theorem erase_ofNat (n : Nat) : (ofNat n).erase = (n : Rat) := rfl

def rationalMul (a b : Rat) : Program Rat :=
  compose (MeteredRationalReplay.ratMul a b) (fun _ => a*b)
    (MeteredRationalReplay.ratMul_safe _ _) (MeteredRationalReplay.ratMul_refines _ _)
@[simp] theorem erase_rationalMul (a b : Rat) : (rationalMul a b).erase = a*b := rfl

def negate (a : Rat) : Program Rat :=
  compose (MeteredRationalReplay.ratSub 0 a) (fun _ => -a)
    (MeteredRationalReplay.ratSub_safe _ _)
    (by simpa only [zero_sub] using MeteredRationalReplay.ratSub_refines 0 a)
@[simp] theorem erase_negate (a : Rat) : (negate a).erase = -a := rfl

def coefficient (a : Rat) : Program P :=
  compose (MeteredRationalReplay.cons a []) (fun _ => [a])
    (MeteredRationalReplay.cons_safe _ _) (MeteredRationalReplay.cons_refines _ _)
@[simp] theorem erase_coefficient (a : Rat) : (coefficient a).erase = [a] := rfl

def binomialWeight (n1 n0 x y : Nat) : Program Rat := do
  let a ← choose n1 x
  let b ← choose n0 y
  let qa ← ofNat a
  let qb ← ofNat b
  rationalMul qa qb
@[simp] theorem erase_binomialWeight (n1 n0 x y : Nat) :
    (binomialWeight n1 n0 x y).erase = (n1.choose x : Rat) * n0.choose y := by
  simp [binomialWeight]

def monomial (c : Rat) (n : Nat) : Program P := do
  let p ← MeteredIntervalReplay.power [0,1] n
  MeteredIntervalReplay.scale c p
@[simp] theorem erase_monomial (c : Rat) (n : Nat) :
    (monomial c n).erase = ParametricPolynomial.monomial c n := by
  simp [monomial, ParametricPolynomial.monomial]

def sum (ps : List P) : Program P := visit fun _ => match ps with
  | [] => pure []
  | p :: ps => do let rest ← sum ps; MeteredIntervalReplay.add p rest
@[simp] theorem erase_sum (ps : List P) : (sum ps).erase = ParametricPolynomial.sum ps := by
  induction ps <;> simp_all [sum, ParametricPolynomial.sum]

/-- Support construction contains only admitted bounded count/index tests. -/
def support (n1 n0 m : Nat) : Program (Finset Nat) :=
  MeteredGlobalList.indexWork (n1+1) (8*(n1+1)+8)
    (fun _ => FNCH.Support.valid n1 n0 m)
@[simp] theorem erase_support (n1 n0 m : Nat) :
    (support n1 n0 m).erase = FNCH.Support.valid n1 n0 m := rfl

def tailSet (n1 n0 m x : Nat) (dir : Direction) : Program (Finset Nat) :=
  MeteredGlobalList.indexWork (n1+1) (12*(n1+1)+12)
    (fun _ => BoschlooOrdering.tailSet n1 n0 m x dir)
@[simp] theorem erase_tailSet (n1 n0 m x : Nat) (dir : Direction) :
    (tailSet n1 n0 m x dir).erase = BoschlooOrdering.tailSet n1 n0 m x dir := rfl

def event (n1 n0 m : Nat) (ks : Finset Nat) : Program P := do
  let ordered ← MeteredGlobalList.indexWork 0 (5*(n1+2)*(n1+2))
    (fun _ => ks.sort (· ≤ ·))
  let terms ← MeteredGlobalList.map (fun k => do
    let c ← binomialWeight n1 n0 k (m-k)
    monomial c k) ordered
  sum terms
@[simp] theorem erase_event (n1 n0 m : Nat) (ks : Finset Nat) :
    (event n1 n0 m ks).erase = ParametricPolynomial.event n1 n0 m ks := by
  simp [event, ParametricPolynomial.event]

def rawComparison {n1 n0 : Nat} (dir : Direction) (candidate observed : Outcome n1 n0) :
    Program P := do
  let mc ← MeteredDecodeInput.natAdd candidate.1.val candidate.2.val
  let mo ← MeteredDecodeInput.natAdd observed.1.val observed.2.val
  let tc ← tailSet n1 n0 mc candidate.1.val dir
  let so ← support n1 n0 mo
  let observedTail ← tailSet n1 n0 mo observed.1.val dir
  let sc ← support n1 n0 mc
  let a ← event n1 n0 mc tc
  let b ← event n1 n0 mo so
  let c ← event n1 n0 mo observedTail
  let d ← event n1 n0 mc sc
  let left ← MeteredIntervalReplay.mul a b
  let right ← MeteredIntervalReplay.mul c d
  let negative ← MeteredIntervalReplay.scale (-1) right
  MeteredIntervalReplay.add left negative
@[simp] theorem erase_rawComparison {n1 n0 : Nat} (dir : Direction)
    (candidate observed : Outcome n1 n0) :
    (rawComparison dir candidate observed).erase =
      ParametricPolynomial.comparison dir candidate observed := by
  simp [rawComparison, ParametricPolynomial.comparison]

def outcome {n1 n0 : Nat} (o : Outcome n1 n0) : Program B := do
  let weight ← binomialWeight n1 n0 o.1.val o.2.val
  let coefficient ← monomial weight o.1.val
  let margin ← MeteredDecodeInput.natAdd o.1.val o.2.val
  let qPower ← bpower [[],[1]] margin
  let complement ← bpower [[1],[-1]] (n1+n0-margin)
  let product ← bmul qPower complement
  bscale coefficient product
@[simp] theorem erase_outcome {n1 n0 : Nat} (o : Outcome n1 n0) :
    (outcome o).erase = ParametricPolynomial.outcome o := by
  simp [outcome, ParametricPolynomial.outcome]

def sumB (ps : List B) : Program B := visit fun _ => match ps with
  | [] => pure []
  | p :: ps => do let rest ← sumB ps; badd p rest
@[simp] theorem erase_sumB (ps : List B) : (sumB ps).erase = ParametricPolynomial.sumB ps := by
  induction ps <;> simp_all [sumB, ParametricPolynomial.sumB]

def rawObjective {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) (r : Rat) : Program B := do
  let ordered ← MeteredGlobalList.outcomeSort mask
  let selectedTerms ← MeteredGlobalList.map outcome ordered
  let selected ← sumB selectedTerms
  let space ← MeteredGlobalList.sampleUniverse n1 n0
  let allOrdered ← MeteredGlobalList.outcomeSort space
  let allTerms ← MeteredGlobalList.map outcome allOrdered
  let total ← sumB allTerms
  let neg ← negate r
  let scalar ← coefficient neg
  let negative ← bscale scalar total
  badd selected negative
@[simp] theorem erase_rawObjective {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) (r : Rat) :
    (rawObjective mask r).erase = ParametricPolynomial.objective mask r := by
  simp [rawObjective, ParametricPolynomial.objective]

def transform (degree : Nat) (p : P) : Program P := visit fun _ =>
  match degree, p with
  | _, [] => pure []
  | 0, c :: _ => coefficient c
  | n+1, c :: cs => do
    let power ← MeteredIntervalReplay.power [1,-1] (n+1)
    let left ← MeteredIntervalReplay.scale c power
    let tail ← transform n cs
    let right ← MeteredIntervalReplay.mul [0,1] tail
    MeteredIntervalReplay.add left right
@[simp] theorem erase_transform (degree : Nat) (p : P) :
    (transform degree p).erase = CompactPolynomial.transform degree p := by
  induction degree generalizing p with
  | zero => cases p <;> simp [transform, CompactPolynomial.transform]
  | succ n ih => cases p <;> simp [transform, CompactPolynomial.transform, ih]

def degreeBound (p : B) : Program Nat := visit fun _ => match p with
  | [] => pure 0
  | c :: cs => do
    let n ← MeteredGlobalList.length c
    let tail ← degreeBound cs
    metadata fun _ => max n tail
@[simp] theorem erase_degreeBound (p : B) :
    (degreeBound p).erase = CompactPolynomial.degreeBound p := by
  induction p <;> simp_all [degreeBound, CompactPolynomial.degreeBound]

def comparison {n1 n0 : Nat} (dir : Direction) (candidate observed : Outcome n1 n0) :
    Program P := do
  let p ← rawComparison dir candidate observed
  let n ← MeteredGlobalList.length p
  transform n p
@[simp] theorem erase_comparison {n1 n0 : Nat} (dir : Direction)
    (candidate observed : Outcome n1 n0) :
    (comparison dir candidate observed).erase = CompactPolynomial.comparison dir candidate observed := by
  simp [comparison, CompactPolynomial.comparison]

def objective {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) (r : Rat) : Program B := do
  let p ← rawObjective mask r
  let n ← degreeBound p
  MeteredGlobalList.map (transform n) p
@[simp] theorem erase_objective {n1 n0 : Nat} (mask : Finset (Outcome n1 n0)) (r : Rat) :
    (objective mask r).erase = CompactPolynomial.objective mask r := by
  simp [objective, CompactPolynomial.objective, CompactPolynomial.transformB]
end ExactCIs.Unconditional.MeteredGlobalPolynomials
