/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredOpenReplay
import ExactCIs.Unconditional.GlobalCheckerParametricRoot

/-! # Metered polynomial Sturm replay on a whole open effect cell -/
namespace ExactCIs.Unconditional.MeteredParametricReplay

open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay RootCertificate
open GlobalCheckerPoint

def allZero (ps : B) : Replay Bool := visit fun _ => match ps with
  | [] => pure true
  | p :: ps => andThen (identity p []) fun _ => allZero ps

private theorem allZero_eq (ps : B) :
    (allZero ps).erase =
      AlgebraicSpecialization.zeroCheck [] ps (List.replicate ps.length []) := by
  induction ps <;>
    simp_all [allZero, List.replicate_succ, AlgebraicSpecialization.zeroCheck, AlgebraicCertificate.zeroCheck,
      RootCertificate.mul]

def stratumIdentity (p q : B) : Replay Bool := do
  let negative ← bscale [-1] q
  let sum ← badd p negative
  allZero sum

@[simp] theorem erase_stratumIdentity (p q : B) :
    (stratumIdentity p q).erase = StratumSignReplay.identityCheck p q := by
  simp only [stratumIdentity, erase_monadic_bind, erase_bscale, erase_badd, allZero_eq,
    StratumSignReplay.identityCheck, AlgebraicSpecialization.identityCheck]

def step (l u : Point) (p q r : B) (s : GlobalCheckerParametricRoot.Step) : Replay Bool :=
  andThen (do
    let left ← bscale s.scale p
    let product ← bmul q s.quotient
    let negative ← bscale [-1] r
    let right ← badd product negative
    stratumIdentity left right) fun _ =>
      andThen (metadata fun _ => decide (s.guard.sign = 1)) fun _ =>
        MeteredOpenReplay.sign s.scale l u s.guard

@[simp] theorem erase_step (l u : Point) (p q r : B) (s : GlobalCheckerParametricRoot.Step) :
    (step l u p q r s).erase = GlobalCheckerParametricRoot.stepCheck l u p q r s := by
  simp [step, GlobalCheckerParametricRoot.stepCheck, Bool.and_assoc]

def terminal (l u : Point) (last : Coefficients) (guard : GlobalCheckerOpenSign.Witness)
    (p : B) (ss : List GlobalCheckerParametricRoot.Step) : Replay Bool := visit fun _ =>
  match ss with
  | [] => andThen (stratumIdentity p [last]) fun _ => MeteredOpenReplay.nonzero last l u guard
  | _ :: _ => pure false

def tail (l u : Point) (last : Coefficients) (guard : GlobalCheckerOpenSign.Witness)
    (previous : B) (ps : List B) (ss : List GlobalCheckerParametricRoot.Step) : Replay Bool :=
  visit fun _ => do
    tickP .rootStep
    match ps with
    | [] => terminal l u last guard previous ss
    | q :: rest => match rest with
      | [] => terminal l u last guard q ss
      | r :: _ => match ss with
        | [] => pure false
        | s :: ss => andThen (step l u previous q r s) fun _ => tail l u last guard q rest ss

def chain (l u : Point) (last : Coefficients) (guard : GlobalCheckerOpenSign.Witness)
    (ps : List B) (ss : List GlobalCheckerParametricRoot.Step) : Replay Bool := visit fun _ =>
  match ps with
  | [] => pure false
  | p :: ps => tail l u last guard p ps ss

private theorem erase_terminal (l u : Point) (last : Coefficients)
    (guard : GlobalCheckerOpenSign.Witness) (p : B) (ss : List GlobalCheckerParametricRoot.Step) :
    (terminal l u last guard p ss).erase =
      (match ss with
      | [] => StratumSignReplay.identityCheck p [last] &&
          GlobalCheckerOpenSign.nonzeroCheck last l u guard
      | _ :: _ => false) := by
  cases ss <;> simp [terminal]

private theorem erase_tail (l u : Point) (last : Coefficients)
    (guard : GlobalCheckerOpenSign.Witness) (p : B) (ps : List B)
    (ss : List GlobalCheckerParametricRoot.Step) :
    (tail l u last guard p ps ss).erase =
      GlobalCheckerParametricRoot.chainCheck l u last guard (p :: ps) ss := by
  induction ps generalizing p ss with
  | nil =>
    simp only [tail, erase_visit, erase_monadic_bind, erase_tickP, erase_terminal]
    cases ss <;> rfl
  | cons q rest ih =>
    simp only [tail, erase_visit, erase_monadic_bind, erase_tickP]
    cases rest with
    | nil => rw [erase_terminal]; cases ss <;> rfl
    | cons r rs => cases ss <;> simp [GlobalCheckerParametricRoot.chainCheck, ih]

@[simp] theorem erase_chain (l u : Point) (last : Coefficients)
    (guard : GlobalCheckerOpenSign.Witness) (ps : List B)
    (ss : List GlobalCheckerParametricRoot.Step) :
    (chain l u last guard ps ss).erase = GlobalCheckerParametricRoot.chainCheck l u last guard ps ss := by
  cases ps with
  | nil => simp [chain, GlobalCheckerParametricRoot.chainCheck]
  | cons p ps => simpa only [chain, erase_visit] using erase_tail l u last guard p ps ss

def first (c : GlobalCheckerParametricRoot.Certificate) : Replay Bool := visit fun _ =>
  match c.tail with
  | [] => pure true
  | p :: _ => do
    let derivative ← bderivative c.representative
    stratumIdentity p derivative

@[simp] theorem erase_first (c : GlobalCheckerParametricRoot.Certificate) :
    (first c).erase = GlobalCheckerParametricRoot.firstCheck c := by
  cases ht : c.tail <;> simp [first, ht, GlobalCheckerParametricRoot.firstCheck]

def rootIdentity (h : B) (c : GlobalCheckerParametricRoot.Certificate) : Replay Bool := do
  let left ← bscale c.rootScale h
  let right ← bmul c.representative c.quotient
  stratumIdentity left right

def powerIdentity (h : B) (c : GlobalCheckerParametricRoot.Certificate) : Replay Bool := do
  let power ← bpower c.representative c.exponent
  let left ← bscale c.powerScale power
  let right ← bmul h c.powerQuotient
  stratumIdentity left right

def bezoutIdentity (c : GlobalCheckerParametricRoot.Certificate) : Replay Bool := do
  let derivative ← bderivative c.representative
  let left ← bmul c.bezoutLeft c.representative
  let right ← bmul c.bezoutRight derivative
  let sum ← badd left right
  stratumIdentity sum [c.bezoutScale]

def check (l u : Point) (h : B) (c : GlobalCheckerParametricRoot.Certificate) : Replay Bool := do
  tickP .rootStep
  andThen (metadata fun _ => decide (0 < c.exponent)) fun _ =>
    andThen (MeteredOpenReplay.nonzero c.rootScale l u c.rootGuard) fun _ =>
      andThen (MeteredOpenReplay.nonzero c.powerScale l u c.powerGuard) fun _ =>
        andThen (MeteredOpenReplay.nonzero c.bezoutScale l u c.bezoutGuard) fun _ =>
          andThen (rootIdentity h c) fun _ =>
            andThen (powerIdentity h c) fun _ =>
              andThen (bezoutIdentity c) fun _ =>
                andThen (chain l u c.last c.lastGuard (c.representative :: c.tail) c.steps)
                  fun _ => first c

@[simp] theorem erase_check (l u : Point) (h : B) (c : GlobalCheckerParametricRoot.Certificate) :
    (check l u h c).erase = GlobalCheckerParametricRoot.check l u h c := by
  simp [check, rootIdentity, powerIdentity, bezoutIdentity,
    GlobalCheckerParametricRoot.check, Bool.and_assoc]

theorem check_bounded {l u : Point} {h : B} {c : GlobalCheckerParametricRoot.Certificate}
    {profile : Profile} {used next : Vector} {answer : Bool}
    (fits : Fits profile used)
    (success : (check l u h c).run profile used = .ok (answer, next)) : Fits profile next :=
  run_safe (check l u h c) profile used fits answer next success

end ExactCIs.Unconditional.MeteredParametricReplay
