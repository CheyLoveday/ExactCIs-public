/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredAlgebraicReplay
import ExactCIs.Unconditional.GlobalCheckerOpenSign

/-! # Metered signs and root counts on open effect cells -/
namespace ExactCIs.Unconditional.MeteredOpenReplay

open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay RootCertificate
open GlobalCheckerPoint

def variations (ss : List SignType) : Replay Nat :=
  compose (MeteredRationalReplay.changes 0 ss) (fun _ => SturmVariation.variations ss)
    (MeteredRationalReplay.changes_safe _ _) (MeteredRationalReplay.changes_refines _ _)

@[simp] theorem erase_variations (ss : List SignType) :
    (variations ss).erase = SturmVariation.variations ss := rfl

def pointSigns (a : Point) (ps : List Coefficients) (ws : List SignWitness) :
    Replay (Option (List SignType)) := visit fun _ => match ps, ws with
  | [], [] => pure (some [])
  | p :: ps, w :: ws => do
    let head ← pointSign p a w
    match head with
    | none => pure none
    | some s => do
      let tail ← pointSigns a ps ws
      metadata fun _ => tail.map (s :: ·)
  | _, _ => pure none

@[simp] theorem erase_pointSigns (a : Point) (ps : List Coefficients) (ws : List SignWitness) :
    (pointSigns a ps ws).erase = GlobalCheckerPoint.signs a ps ws := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp [pointSigns, GlobalCheckerPoint.signs]
  | cons p ps ih =>
    cases ws with
    | nil => simp [pointSigns, GlobalCheckerPoint.signs]
    | cons w ws =>
      simp only [pointSigns, erase_visit, erase_monadic_bind, erase_pointSign]
      cases h : GlobalCheckerPoint.sign p a w <;>
        simp [GlobalCheckerPoint.signs, h, ih] <;>
        cases GlobalCheckerPoint.signs a ps ws <;> rfl

def sample (a b : Point) (q : Rat) : Replay Bool :=
  andThen (point a) fun _ => andThen (point b) fun _ =>
    andThen (visit fun _ => match a with
      | .rational x => lt x q
      | .algebraic x => le x.upper q) fun _ =>
        visit fun _ => match b with
          | .rational x => lt q x
          | .algebraic x => le q x.lower

@[simp] theorem erase_sample (a b : Point) (q : Rat) :
    (sample a b q).erase = GlobalCheckerPoint.sampleCheck a b q := by
  cases a <;> cases b <;> simp [sample, GlobalCheckerPoint.sampleCheck, Bool.and_assoc]

def count (c : RootCountCertificate.Certificate) (a b : Point)
    (left right : List SignWitness) : Replay (Option Nat) := do
  let ls ← pointSigns a (c.representative :: c.tail) left
  match ls with
  | none => pure none
  | some ls => do
    let rs ← pointSigns b (c.representative :: c.tail) right
    match rs with
    | none => pure none
    | some rs => do
      let lv ← variations ls
      let rv ← variations rs
      metadata fun _ => some (lv - rv - if rs.headD 0 = 0 then 1 else 0)

@[simp] theorem erase_count (c : RootCountCertificate.Certificate) (a b : Point)
    (left right : List SignWitness) :
    (count c a b left right).erase = GlobalCheckerOpenSign.count c a b left right := by
  simp only [count, erase_monadic_bind, erase_pointSigns]
  cases hl : GlobalCheckerPoint.signs a (c.representative :: c.tail) left <;>
    cases hr : GlobalCheckerPoint.signs b (c.representative :: c.tail) right <;>
    simp [GlobalCheckerOpenSign.count, hl, hr]

def sign (p : Coefficients) (a b : Point) (w : GlobalCheckerOpenSign.Witness) : Replay Bool :=
  visit fun _ => match w with
  | .identityZero => identity p []
  | .rootFree s c left right q =>
    andThen (rootCheck p c) fun _ =>
      andThen (sample a b q) fun _ =>
        andThen (do
          let y ← value p q
          let actual ← ratSign y
          metadata fun _ => decide (s ≠ 0 ∧ actual = s)) fun _ => do
            let n ← count c a b left right
            metadata fun _ => decide (n = some 0)

@[simp] theorem erase_sign (p : Coefficients) (a b : Point)
    (w : GlobalCheckerOpenSign.Witness) :
    (sign p a b w).erase = GlobalCheckerOpenSign.check p a b w := by
  cases w <;> simp [sign, GlobalCheckerOpenSign.check, Bool.and_assoc] <;> rfl

def nonzero (p : Coefficients) (a b : Point) (w : GlobalCheckerOpenSign.Witness) : Replay Bool :=
  andThen (metadata fun _ => decide (w.sign ≠ 0)) fun _ => sign p a b w

@[simp] theorem erase_nonzero (p : Coefficients) (a b : Point)
    (w : GlobalCheckerOpenSign.Witness) :
    (nonzero p a b w).erase = GlobalCheckerOpenSign.nonzeroCheck p a b w := by
  simp [nonzero, GlobalCheckerOpenSign.nonzeroCheck]

def signs (a b : Point) (q : Rat) (ps : List B) (ws : List GlobalCheckerOpenSign.Witness) :
    Replay Bool := visit fun _ => match ps, ws with
  | [], [] => pure true
  | p :: ps, w :: ws =>
    andThen (do let coefficient ← atRational p q; sign coefficient a b w)
      fun _ => signs a b q ps ws
  | _, _ => pure false

@[simp] theorem erase_signs (a b : Point) (q : Rat) (ps : List B)
    (ws : List GlobalCheckerOpenSign.Witness) :
    (signs a b q ps ws).erase = GlobalCheckerOpenSign.signsCheck a b q ps ws := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp [signs, GlobalCheckerOpenSign.signsCheck]
  | cons p ps ih => cases ws <;> simp [signs, GlobalCheckerOpenSign.signsCheck, ih]

theorem sign_sound {p : Coefficients} {a b : Point} {w : GlobalCheckerOpenSign.Witness}
    {profile : Profile} {used next : Vector}
    (success : (sign p a b w).run profile used = .ok (true, next))
    {x : ℝ} (inside : x ∈ Set.Ioo a.value b.value) : SignType.sign (eval p x) = w.sign := by
  have same := run_refines (sign p a b w) profile used true next success
  rw [erase_sign] at same
  exact GlobalCheckerOpenSign.check_sound same.symm inside

end ExactCIs.Unconditional.MeteredOpenReplay
