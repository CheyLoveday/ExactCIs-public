/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredAlgebraicReplay

/-! # Metered modular Sturm replay at a selected effect

All coefficient identities are checked modulo the same supplied definer. The
inverse of the terminal coefficient is checked explicitly; reducible definers
are never treated as fields by an unchecked division.
-/
namespace ExactCIs.Unconditional.MeteredSpecializedRootReplay

open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay RootCertificate

def terminal (d last inv quotient : Coefficients) (p : B) (qs ws : List B) : Replay Bool :=
  visit fun _ => match qs, ws with
  | [], [w] => andThen (bidentity d p [last] w) fun _ => inverse d last inv quotient
  | _, _ => pure false

def tail (d last inv quotient : Coefficients) (previous : B)
    (ps qs ws : List B) : Replay Bool := visit fun _ => do
  tickP .rootStep
  match ps with
  | [] => terminal d last inv quotient previous qs ws
  | q :: rest => match rest with
    | [] => terminal d last inv quotient q qs ws
    | r :: _ => match qs, ws with
      | quot :: qs, w :: ws =>
        andThen (do
          let product ← bmul q quot
          let negative ← bscale [-1] r
          let sum ← badd product negative
          bidentity d previous sum w) fun _ => tail d last inv quotient q rest qs ws
      | _, _ => pure false

def chain (d last inv quotient : Coefficients) (ps qs ws : List B) : Replay Bool := visit fun _ =>
  match ps with
  | [] => pure false
  | p :: ps => tail d last inv quotient p ps qs ws

private theorem erase_terminal (d last inv quotient : Coefficients) (p : B) (qs ws : List B) :
    (terminal d last inv quotient p qs ws).erase =
      (match qs, ws with
      | [], [w] => AlgebraicSpecialization.identityCheck d p [last] w &&
          AlgebraicCertificate.inverseCheck d last inv quotient
      | _, _ => false) := by
  cases qs with
  | cons _ _ => simp [terminal]
  | nil =>
    cases ws with
    | nil => simp [terminal]
    | cons w ws => cases ws <;> simp [terminal]

private theorem erase_tail (d last inv quotient : Coefficients) (p : B) (ps qs ws : List B) :
    (tail d last inv quotient p ps qs ws).erase =
      AlgebraicRootCertificate.chainCheck d last inv quotient (p :: ps) qs ws := by
  induction ps generalizing p qs ws with
  | nil =>
    simp only [tail, erase_visit, erase_monadic_bind, erase_tickP, erase_terminal]
    cases qs with
    | cons _ _ => rfl
    | nil =>
      cases ws with
      | nil => rfl
      | cons w ws => cases ws <;> rfl
  | cons q rest ih =>
    simp only [tail, erase_visit, erase_monadic_bind, erase_tickP]
    cases rest with
    | nil =>
      rw [erase_terminal]
      cases qs with
      | cons _ _ => rfl
      | nil =>
        cases ws with
        | nil => rfl
        | cons w ws => cases ws <;> rfl
    | cons r rs =>
      cases qs <;> cases ws <;>
        simp [AlgebraicRootCertificate.chainCheck, ih]

@[simp] theorem erase_chain (d last inv quotient : Coefficients) (ps qs ws : List B) :
    (chain d last inv quotient ps qs ws).erase =
      AlgebraicRootCertificate.chainCheck d last inv quotient ps qs ws := by
  cases ps with
  | nil => simp [chain, AlgebraicRootCertificate.chainCheck]
  | cons p ps => simpa only [chain, erase_visit] using erase_tail d last inv quotient p ps qs ws

def first (d : Coefficients) (c : AlgebraicRootCertificate.Certificate) : Replay Bool := visit fun _ =>
  match c.tail with
  | [] => pure true
  | p :: _ => do
    let derivative ← bderivative c.representative
    bidentity d p derivative c.derivativeWitness

@[simp] theorem erase_first (d : Coefficients) (c : AlgebraicRootCertificate.Certificate) :
    (first d c).erase = AlgebraicRootCertificate.firstCheck d c := by
  cases ht : c.tail <;> simp [first, ht, AlgebraicRootCertificate.firstCheck]

def rootIdentity (d : Coefficients) (h : B) (c : AlgebraicRootCertificate.Certificate) :
    Replay Bool := do
  let product ← bmul c.representative c.quotient
  bidentity d h product c.rootWitness

def powerIdentity (d : Coefficients) (h : B) (c : AlgebraicRootCertificate.Certificate) :
    Replay Bool := do
  let power ← bpower c.representative c.exponent
  let product ← bmul h c.powerQuotient
  bidentity d power product c.powerWitness

def bezoutIdentity (d : Coefficients) (c : AlgebraicRootCertificate.Certificate) : Replay Bool := do
  let derivative ← bderivative c.representative
  let left ← bmul c.bezoutLeft c.representative
  let right ← bmul c.bezoutRight derivative
  let sum ← badd left right
  bidentity d sum [[1]] c.bezoutWitness

def check (d : Coefficients) (h : B) (c : AlgebraicRootCertificate.Certificate) : Replay Bool := do
  tickP .rootStep
  andThen (metadata fun _ => decide (0 < c.exponent)) fun _ =>
    andThen (rootIdentity d h c) fun _ =>
      andThen (powerIdentity d h c) fun _ =>
        andThen (bezoutIdentity d c) fun _ =>
          andThen (chain d c.last c.lastInverse c.lastQuotient
            (c.representative :: c.tail) c.quotients c.witnesses) fun _ => first d c

@[simp] theorem erase_check (d : Coefficients) (h : B) (c : AlgebraicRootCertificate.Certificate) :
    (check d h c).erase = AlgebraicRootCertificate.check d h c := by
  simp [check, rootIdentity, powerIdentity, bezoutIdentity,
    AlgebraicRootCertificate.check, Bool.and_assoc]

def signs (d : Coefficients) (l u q : Rat) (ps : List B)
    (ws : List AlgebraicSignReplay.SignWitness) : Replay Bool := visit fun _ =>
  match ps, ws with
  | [], [] => pure true
  | p :: ps, w :: ws =>
    andThen (do let coefficient ← atRational p q; algebraicSign d coefficient l u w)
      fun _ => signs d l u q ps ws
  | _, _ => pure false

@[simp] theorem erase_signs (d : Coefficients) (l u q : Rat) (ps : List B)
    (ws : List AlgebraicSignReplay.SignWitness) :
    (signs d l u q ps ws).erase = AlgebraicSignReplay.signsCheck d l u q ps ws := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp [signs, AlgebraicSignReplay.signsCheck]
  | cons p ps ih => cases ws <;> simp [signs, AlgebraicSignReplay.signsCheck, ih]

theorem check_bounded {d : Coefficients} {h : B} {c : AlgebraicRootCertificate.Certificate}
    {profile : Profile} {used next : Vector} {answer : Bool}
    (fits : Fits profile used)
    (success : (check d h c).run profile used = .ok (answer, next)) : Fits profile next :=
  run_safe (check d h c) profile used fits answer next success

theorem checked_facts {d : Coefficients} {h : B} {c : AlgebraicRootCertificate.Certificate}
    {profile : Profile} {used next : Vector}
    (success : (check d h c).run profile used = .ok (true, next))
    {x : ℝ} (root : eval d x = 0) :
    (∀ q : ℝ, (AlgebraicSpecialization.specialize x h).eval q = 0 ↔
      (AlgebraicSpecialization.specialize x c.representative).eval q = 0) ∧
    (AlgebraicSpecialization.specialize x c.representative).Separable ∧
    SturmVariation.Chain ((c.representative :: c.tail).map fun p =>
      (AlgebraicSpecialization.specialize x p).eval) ∧
    AlgebraicRootCertificate.firstCheck d c = true := by
  have same := run_refines (check d h c) profile used true next success
  rw [erase_check] at same
  exact AlgebraicRootCertificate.checked_facts same.symm root

end ExactCIs.Unconditional.MeteredSpecializedRootReplay
