/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeTyped

/-! # Metered reconstruction of canonical modular-witness row padding

Only admitted list-width counters are routed through these helpers. Arithmetic
and each recursive width-list visit are charged. Padding checks its target cap
before allocating and retains every supplied row, including malicious extras.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram
open SpecializedWitnessWidth (Shape Widths)

def widthMax (a b : Nat) : Program Nat :=
  primitive .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b))
    (fun _ => max a b)

def widthSub (a b : Nat) : Program Nat :=
  primitive .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b))
    (fun _ => a - b)

/-- Two zero comparisons, one addition and one subtraction at most. -/
def widthMul (a b : Nat) : Program Nat :=
  primitive .integer 4
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b) + 1)
    (fun _ => SpecializedWitnessWidth.mulWidth a b)

@[simp] theorem erase_widthMax (a b : Nat) : (widthMax a b).erase = max a b := rfl
@[simp] theorem erase_widthSub (a b : Nat) : (widthSub a b).erase = a - b := rfl
@[simp] theorem erase_widthMul (a b : Nat) :
    (widthMul a b).erase = SpecializedWitnessWidth.mulWidth a b := rfl

def widthPower (a : Nat) : Nat → Program Nat
  | 0 => visit fun _ => pure 1
  | n + 1 => visit fun _ => do
      let previous ← widthPower a n
      widthMul a previous

@[simp] theorem erase_widthPower (a n : Nat) :
    (widthPower a n).erase = SpecializedWitnessWidth.powerWidth a n := by
  induction n <;> simp_all [widthPower, SpecializedWitnessWidth.powerWidth]

def widthCons (a : Nat) (tail : List Nat) : Program (List Nat) := do
  let _ ← reserve .decodeItem
  metadata fun _ => a :: tail

@[simp] theorem erase_widthCons (a : Nat) (tail : List Nat) :
    (widthCons a tail).erase = a :: tail := by simp [widthCons]

def widthChain : List Nat → List Nat → Program (List Nat)
  | [], _ => visit fun _ => pure []
  | [p], _ => visit fun _ => do
      let n ← widthMax p 1
      widthCons n []
  | [_, q], _ => visit fun _ => do
      let n ← widthMax q 1
      widthCons n []
  | p :: q :: r :: ps, quotient :: qs => visit fun _ => do
      let product ← widthMul q quotient
      let next ← widthMax product r
      let head ← widthMax p next
      let tail ← widthChain (q :: r :: ps) qs
      widthCons head tail
  | _ :: _ :: _ :: _, [] => visit fun _ => pure []

@[simp] theorem erase_widthChain (ps qs : List Nat) :
    (widthChain ps qs).erase = SpecializedWitnessWidth.chainWidths ps qs := by
  match ps, qs with
  | [], _ => simp [widthChain, SpecializedWitnessWidth.chainWidths]
  | [_], _ => simp [widthChain, SpecializedWitnessWidth.chainWidths]
  | [_, _], _ => simp [widthChain, SpecializedWitnessWidth.chainWidths]
  | p :: q :: r :: ps, quotient :: qs =>
      simp [widthChain, SpecializedWitnessWidth.chainWidths, erase_widthChain (q :: r :: ps) qs]
  | _ :: _ :: _ :: _, [] => simp [widthChain, SpecializedWitnessWidth.chainWidths]
termination_by ps.length

def widthLengths : List AlgebraicSpecialization.Bivariate → Program (List Nat)
  | [] => visit fun _ => pure []
  | p :: ps => visit fun _ => do
      let n ← length p
      let tail ← widthLengths ps
      widthCons n tail

@[simp] theorem erase_widthLengths (ps : List AlgebraicSpecialization.Bivariate) :
    (widthLengths ps).erase = ps.map List.length := by
  induction ps <;> simp_all [widthLengths]

def widthShape (c : AlgebraicRootCertificate.Certificate) : Program Shape := do
  pure {
    representative := ← length c.representative
    quotient := ← length c.quotient
    powerQuotient := ← length c.powerQuotient
    exponent := c.exponent
    bezoutLeft := ← length c.bezoutLeft
    bezoutRight := ← length c.bezoutRight
    tail := ← widthLengths c.tail
    quotients := ← widthLengths c.quotients }

@[simp] theorem erase_widthShape (c : AlgebraicRootCertificate.Certificate) :
    (widthShape c).erase = SpecializedWitnessWidth.shape c := by
  simp [widthShape, SpecializedWitnessWidth.shape]

def widthFrom (original : Nat) (c : Shape) : Program Widths := do
  let product ← widthMul c.representative c.quotient
  let root ← widthMax original product
  let power ← widthPower c.representative c.exponent
  let originalProduct ← widthMul original c.powerQuotient
  let power ← widthMax power originalProduct
  let first ← widthMul c.bezoutLeft c.representative
  let second ← widthMul c.bezoutRight c.representative
  let combined ← widthMax first second
  let bezout ← widthMax combined 1
  let chainInput ← widthCons c.representative c.tail
  let chain ← widthChain chainInput c.quotients
  let derivative ← match c.tail with
    | [] => pure 0
    | p :: _ => widthMax p c.representative
  pure ⟨root, power, bezout, chain, derivative⟩

@[simp] theorem erase_widthFrom (original : Nat) (c : Shape) :
    (widthFrom original c).erase = SpecializedWitnessWidth.widthsFrom original c := by
  simp only [widthFrom, erase_monadic_bind, erase_widthMul, erase_widthMax,
    erase_widthPower, erase_widthChain, erase_widthCons]
  cases shape : c.tail <;> simp [SpecializedWitnessWidth.widthsFrom, shape]

def witnessWidths (original : Nat) (c : AlgebraicRootCertificate.Certificate) : Decode Widths := do
  let shape ← liftD (widthShape c)
  liftD (widthFrom original shape)

@[simp] theorem erase_witnessWidths (original : Nat) (c : AlgebraicRootCertificate.Certificate) :
    eraseD (witnessWidths original c) = pure (SpecializedWitnessWidth.widths original c) := by
  simp [witnessWidths, SpecializedWitnessWidth.widths]

def padWitness (caps : Caps) (width : Nat) (witness : AlgebraicSpecialization.Bivariate) :
    Decode AlgebraicSpecialization.Bivariate := do
  let cap ← liftD (MeteredDecodeInput.natAdd caps.degree 1)
  require (← liftD (MeteredDecodeInput.natLE width cap)) (.resource .degree)
  let n ← liftD (length witness)
  let padding ← liftD (widthSub width n)
  let total ← liftD (MeteredDecodeInput.natAdd n padding)
  let degree ← liftD (widthSub total 1)
  let _ ← liftD (observeDegree degree)
  let _ ← liftD (reserve .structural total)
  liftD (primitive .decodeItem total 0 (fun _ =>
    witness ++ List.replicate padding []))

@[simp] theorem erase_padWitness (caps : Caps) (width : Nat)
    (witness : AlgebraicSpecialization.Bivariate) :
    eraseD (padWitness caps width witness) = GlobalCheckerDecode.padWitness caps width witness := by
  simp [padWitness, GlobalCheckerDecode.padWitness, SpecializedWitnessWidth.pad]

def padWitnesses (caps : Caps) : List Nat → List AlgebraicSpecialization.Bivariate →
    Decode (List AlgebraicSpecialization.Bivariate)
  | width :: widths, witness :: witnesses => do
      let _ ← liftD (reserve .structural)
      let head ← padWitness caps width witness
      let tail ← padWitnesses caps widths witnesses
      let _ ← liftD (reserve .decodeItem)
      pure (head :: tail)
  | _, witnesses => do
      let _ ← liftD (reserve .structural)
      pure witnesses

@[simp] theorem erase_padWitnesses (caps : Caps) (widths : List Nat)
    (witnesses : List AlgebraicSpecialization.Bivariate) :
    eraseD (padWitnesses caps widths witnesses) =
      GlobalCheckerDecode.padWitnesses caps widths witnesses := by
  induction widths generalizing witnesses with
  | nil => simp [padWitnesses, GlobalCheckerDecode.padWitnesses]
  | cons width widths ih =>
      cases witnesses <;> simp_all [padWitnesses, GlobalCheckerDecode.padWitnesses]

def rehydrateWitnesses (caps : Caps) (originalWidth : Nat)
    (c : AlgebraicRootCertificate.Certificate) : Decode AlgebraicRootCertificate.Certificate := do
  let widths ← witnessWidths originalWidth c
  let root ← padWitness caps widths.root c.rootWitness
  let power ← padWitness caps widths.power c.powerWitness
  let bezout ← padWitness caps widths.bezout c.bezoutWitness
  let chain ← padWitnesses caps widths.chain c.witnesses
  let derivative ← padWitness caps widths.derivative c.derivativeWitness
  return { c with
    rootWitness := root
    powerWitness := power
    bezoutWitness := bezout
    witnesses := chain
    derivativeWitness := derivative }

@[simp] theorem erase_rehydrateWitnesses (caps : Caps) (originalWidth : Nat)
    (c : AlgebraicRootCertificate.Certificate) :
    eraseD (rehydrateWitnesses caps originalWidth c) =
      GlobalCheckerDecode.rehydrateWitnesses caps originalWidth c := by
  simp [rehydrateWitnesses, GlobalCheckerDecode.rehydrateWitnesses]

end ExactCIs.Unconditional.MeteredDecode
