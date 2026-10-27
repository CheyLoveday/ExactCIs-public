/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredRationalReplay
import ExactCIs.Unconditional.MeteredProgram

/-! # Suspended interval and algebraic-identity replay

Every rational/polynomial body below delegates to the concrete vector-metered
kernel. `MeteredProgram.erase` appears in proof statements, not runtime branches.
-/
namespace ExactCIs.Unconditional.MeteredIntervalReplay

open ResourceModel MeteredProgram
open RootCertificate

abbrev Replay := Program

def add (a b : Coefficients) : Replay Coefficients :=
  compose (MeteredRationalReplay.polyAdd a b) (fun _ => RootCertificate.add a b)
    (MeteredRationalReplay.polyAdd_safe _ _) (MeteredRationalReplay.polyAdd_correct _ _)
def scale (a : Rat) (b : Coefficients) : Replay Coefficients :=
  compose (MeteredRationalReplay.polyScale a b) (fun _ => RootCertificate.scale a b)
    (MeteredRationalReplay.polyScale_safe _ _) (MeteredRationalReplay.polyScale_correct _ _)
def mul (a b : Coefficients) : Replay Coefficients :=
  compose (MeteredRationalReplay.polyMul a b) (fun _ => RootCertificate.mul a b)
    (MeteredRationalReplay.polyMul_safe _ _) (MeteredRationalReplay.polyMul_correct _ _)
def power (a : Coefficients) (n : Nat) : Replay Coefficients :=
  compose (MeteredRationalReplay.polyPower a n) (fun _ => RootCertificate.power a n)
    (MeteredRationalReplay.polyPower_safe _ _) (MeteredRationalReplay.polyPower_correct _ _)
def derivative (a : Coefficients) : Replay Coefficients :=
  compose (MeteredRationalReplay.polyDerivative a) (fun _ => RootCertificate.derivative a)
    (MeteredRationalReplay.polyDerivative_safe _) (MeteredRationalReplay.polyDerivative_correct _)
def value (a : Coefficients) (x : Rat) : Replay Rat :=
  compose (MeteredRationalReplay.polyValue a x) (fun _ => RootCertificate.value a x)
    (MeteredRationalReplay.polyValue_safe _ _) (MeteredRationalReplay.polyValue_correct _ _)
def identity (a b : Coefficients) : Replay Bool :=
  compose (MeteredRationalReplay.polyIdentity a b) (fun _ => RootCertificate.identityCheck a b)
    (MeteredRationalReplay.polyIdentity_safe _ _) (MeteredRationalReplay.polyIdentity_correct _ _)
def bounds (a : Coefficients) (l u : Rat) : Replay (Rat × Rat) :=
  compose (MeteredRationalReplay.polyBounds a l u) (fun _ => RootCertificate.bounds a l u)
    (MeteredRationalReplay.polyBounds_safe _ _ _) (MeteredRationalReplay.polyBounds_correct _ _ _)
def le (a b : Rat) : Replay Bool :=
  compose (MeteredRationalReplay.ratLE a b) (fun _ => decide (a ≤ b)) (MeteredRationalReplay.ratLE_safe _ _) (MeteredRationalReplay.ratLE_refines _ _)
def lt (a b : Rat) : Replay Bool :=
  compose (MeteredRationalReplay.ratLT a b) (fun _ => decide (a < b)) (MeteredRationalReplay.ratLT_safe _ _) (MeteredRationalReplay.ratLT_refines _ _)
def eq (a b : Rat) : Replay Bool :=
  compose (MeteredRationalReplay.ratEQ a b) (fun _ => decide (a = b)) (MeteredRationalReplay.ratEQ_safe _ _) (MeteredRationalReplay.ratEQ_refines _ _)

def andThen (first : Replay Bool) (second : Unit → Replay Bool) : Replay Bool := do
  let answer ← first
  if answer then second () else pure false

def orElse (first : Replay Bool) (second : Unit → Replay Bool) : Replay Bool := do
  let answer ← first
  if answer then pure true else second ()

@[simp] theorem erase_compose {α : Type} (body : M α) (value : Unit → α)
    (safe : Safe body) (refines : Refines body (value ())) :
    (compose body value safe refines).erase = value () := rfl

@[simp] theorem erase_andThen (first : Replay Bool) (second : Unit → Replay Bool) :
    (andThen first second).erase = (first.erase && (second ()).erase) := by
  simp only [andThen, erase_monadic_bind]
  cases first.erase <;> simp only [Bool.false_eq_true, ↓reduceIte, erase_pure,
    Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or]

@[simp] theorem erase_orElse (first : Replay Bool) (second : Unit → Replay Bool) :
    (orElse first second).erase = (first.erase || (second ()).erase) := by
  simp only [orElse, erase_monadic_bind]
  cases first.erase <;> simp only [Bool.false_eq_true, ↓reduceIte, erase_pure,
    Bool.false_and, Bool.true_and, Bool.false_or, Bool.true_or]

@[simp] theorem erase_add (a b : Coefficients) : (add a b).erase = RootCertificate.add a b := rfl
@[simp] theorem erase_scale (a : Rat) (b : Coefficients) :
    (scale a b).erase = RootCertificate.scale a b := rfl
@[simp] theorem erase_mul (a b : Coefficients) : (mul a b).erase = RootCertificate.mul a b := rfl
@[simp] theorem erase_power (a : Coefficients) (n : Nat) :
    (power a n).erase = RootCertificate.power a n := rfl
@[simp] theorem erase_derivative (a : Coefficients) :
    (derivative a).erase = RootCertificate.derivative a := rfl
@[simp] theorem erase_value (a : Coefficients) (x : Rat) :
    (value a x).erase = RootCertificate.value a x := rfl
@[simp] theorem erase_identity (a b : Coefficients) :
    (identity a b).erase = RootCertificate.identityCheck a b := rfl
@[simp] theorem erase_bounds (a : Coefficients) (l u : Rat) :
    (bounds a l u).erase = RootCertificate.bounds a l u := rfl
@[simp] theorem erase_le (a b : Rat) : (le a b).erase = decide (a ≤ b) := rfl
@[simp] theorem erase_lt (a b : Rat) : (lt a b).erase = decide (a < b) := rfl
@[simp] theorem erase_eq (a b : Rat) : (eq a b).erase = decide (a = b) := rfl

def positive (p : Coefficients) (l u : Rat) : Replay Bool :=
  andThen (le 0 l) fun _ => andThen (le l u) fun _ => do
    let enclosure ← bounds p l u
    lt 0 enclosure.1

def negative (p : Coefficients) (l u : Rat) : Replay Bool :=
  andThen (le 0 l) fun _ => andThen (le l u) fun _ => do
    let enclosure ← bounds p l u
    lt enclosure.2 0

def nonzero (p : Coefficients) (l u : Rat) : Replay Bool :=
  orElse (positive p l u) fun _ => negative p l u

def zero (p d quotient : Coefficients) : Replay Bool := do
  let product ← mul d quotient
  identity p product

def positiveRemainder (p d quotient remainder : Coefficients) (l u : Rat) : Replay Bool :=
  andThen (do let product ← mul d quotient; let sum ← add product remainder; identity p sum)
    fun _ => positive remainder l u

def inverse (d denominator inv quotient : Coefficients) : Replay Bool := do
  let left ← mul denominator inv
  let product ← mul d quotient
  let right ← add [1] product
  identity left right

def localize (d removed retained : Coefficients) (l u : Rat) : Replay Bool :=
  andThen (zero d removed retained) fun _ => nonzero removed l u

@[simp] theorem erase_positive (p : Coefficients) (l u : Rat) :
    (positive p l u).erase = RootCertificate.positiveCheck p l u := by
  simp [positive, RootCertificate.positiveCheck, Bool.decide_and, Bool.and_assoc]
@[simp] theorem erase_negative (p : Coefficients) (l u : Rat) :
    (negative p l u).erase = RootCertificate.negativeCheck p l u := by
  simp [negative, RootCertificate.negativeCheck, Bool.decide_and, Bool.and_assoc]
@[simp] theorem erase_nonzero (p : Coefficients) (l u : Rat) :
    (nonzero p l u).erase = AlgebraicCertificate.nonzeroCheck p l u := by
  simp [nonzero, AlgebraicCertificate.nonzeroCheck]
@[simp] theorem erase_zero (p d q : Coefficients) :
    (zero p d q).erase = AlgebraicCertificate.zeroCheck p d q := by
  simp [zero, AlgebraicCertificate.zeroCheck]
@[simp] theorem erase_positiveRemainder (p d q r : Coefficients) (l u : Rat) :
    (positiveRemainder p d q r l u).erase =
      AlgebraicCertificate.positiveRemainderCheck p d q r l u := by
  simp [positiveRemainder, AlgebraicCertificate.positiveRemainderCheck]
@[simp] theorem erase_inverse (d denominator inv quotient : Coefficients) :
    (inverse d denominator inv quotient).erase =
      AlgebraicCertificate.inverseCheck d denominator inv quotient := by
  simp [inverse, AlgebraicCertificate.inverseCheck]
@[simp] theorem erase_localize (d removed retained : Coefficients) (l u : Rat) :
    (localize d removed retained l u).erase =
      AlgebraicCertificate.localizeCheck d removed retained l u := by
  simp [localize, AlgebraicCertificate.localizeCheck, AlgebraicCertificate.zeroCheck]

/-- Checked localization retains the selected root, including reducible definers. -/
theorem localize_sound {d removed retained : Coefficients} {l u : Rat}
    {p : Profile} {used next : Vector}
    (success : (localize d removed retained l u).run p used = .ok (true, next))
    {x : ℝ} (inside : x ∈ Set.Icc (l : ℝ) u) :
    eval d x = 0 ↔ eval retained x = 0 := by
  have same := run_refines (localize d removed retained l u) p used true next success
  rw [erase_localize] at same
  exact AlgebraicCertificate.localizeCheck_root_iff same.symm inside

end ExactCIs.Unconditional.MeteredIntervalReplay
