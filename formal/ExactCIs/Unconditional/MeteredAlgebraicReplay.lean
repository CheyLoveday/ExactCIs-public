/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredIntervalReplay
import ExactCIs.Unconditional.RootComparison
import ExactCIs.Unconditional.GlobalCheckerPoint

/-! # Metered selected-embedding replay

Selected roots retain their exact open-isolator semantics. Sign, divisibility,
localization and equality/order witnesses use concrete rational replay; no
quotient-field assumption or unmetered semantic fallback is used.
-/
namespace ExactCIs.Unconditional.MeteredAlgebraicReplay

open ResourceModel MeteredProgram MeteredIntervalReplay RootCertificate

abbrev B := AlgebraicSpecialization.Bivariate

def rootCheck (h : Coefficients) (c : RootCountCertificate.Certificate) : Replay Bool :=
  compose (MeteredRationalReplay.rootCheck h c) (fun _ => RootCountCertificate.check h c)
    (MeteredRationalReplay.rootCheck_safe _ _) (MeteredRationalReplay.rootCheck_refines _ _)

def rootCount (c : RootCountCertificate.Certificate) (l u : Rat) : Replay Nat :=
  compose (MeteredRationalReplay.rootCount c l u) (fun _ => RootCountCertificate.count c l u)
    (MeteredRationalReplay.rootCount_safe _ _ _) (MeteredRationalReplay.rootCount_refines _ _ _)

def ratSign (x : Rat) : Replay SignType :=
  compose (MeteredRationalReplay.ratSign x) (fun _ => SignType.sign x)
    (MeteredRationalReplay.ratSign_safe _) (MeteredRationalReplay.ratSign_refines _)

def tickP (event : Event) : Replay Unit :=
  compose (tick event) (fun _ => ()) (tick_safe _ _ _ _) (tick_refines _ _ _ _)

@[simp] theorem erase_rootCheck (h : Coefficients) (c : RootCountCertificate.Certificate) :
    (rootCheck h c).erase = RootCountCertificate.check h c := rfl
@[simp] theorem erase_rootCount (c : RootCountCertificate.Certificate) (l u : Rat) :
    (rootCount c l u).erase = RootCountCertificate.count c l u := rfl
@[simp] theorem erase_ratSign (x : Rat) : (ratSign x).erase = SignType.sign x := rfl
@[simp] theorem erase_tickP (event : Event) : (tickP event).erase = () := rfl

/-- Degree preflight precedes outer-variable coefficient-row construction. -/
def row (a : Coefficients) (as : B) : Replay B := do
  let n ← compose (MeteredRationalReplay.lengthM as) (fun _ => as.length)
    (MeteredRationalReplay.lengthM_safe _) (MeteredRationalReplay.lengthM_refines _)
  compose (do tick .degree 0 0 n
              perform .structural (cost .structural 1) (fun _ => a :: as))
    (fun _ => a :: as)
    (bind_safe (tick_safe _ _ _ _) (fun _ => perform_safe _ _ _))
    (bind_refines (tick_refines _ _ _ _) (perform_refines _ _ _))

@[simp] theorem erase_row (a : Coefficients) (as : B) : (row a as).erase = a :: as := by
  simp [row]

def badd (as bs : B) : Replay B := visit fun _ =>
  match as, bs with
  | [], bs => pure bs
  | as, [] => pure as
  | a :: as, b :: bs => do
    let head ← add a b
    let tail ← badd as bs
    row head tail

def bscale (a : Coefficients) (bs : B) : Replay B := visit fun _ =>
  match bs with
  | [] => pure []
  | b :: bs => do
    let head ← mul a b
    let tail ← bscale a bs
    row head tail

def bmul (as bs : B) : Replay B := visit fun _ =>
  match as with
  | [] => pure []
  | a :: as => do
    let head ← bscale a bs
    let tail ← bmul as bs
    let shifted ← row [] tail
    badd head shifted

def bpower (as : B) (n : Nat) : Replay B := visit fun _ =>
  match n with
  | 0 => row [1] []
  | n + 1 => do let previous ← bpower as n; bmul as previous

def bderivative (as : B) : Replay B := visit fun _ =>
  match as with
  | [] => pure []
  | _ :: as => do
    let tail ← bderivative as
    let shifted ← row [] tail
    badd as shifted

def atRational (as : B) (q : Rat) : Replay Coefficients := visit fun _ =>
  match as with
  | [] => pure []
  | a :: as => do
    let tail ← atRational as q
    let scaled ← scale q tail
    add a scaled

@[simp] theorem erase_badd (as bs : B) : (badd as bs).erase = AlgebraicSpecialization.add as bs := by
  induction as generalizing bs with
  | nil => simp [badd, AlgebraicSpecialization.add]
  | cons a as ih => cases bs <;> simp [badd, AlgebraicSpecialization.add, ih]
@[simp] theorem erase_bscale (a : Coefficients) (bs : B) :
    (bscale a bs).erase = AlgebraicSpecialization.scale a bs := by
  induction bs <;> simp_all [bscale, AlgebraicSpecialization.scale]
@[simp] theorem erase_bmul (as bs : B) : (bmul as bs).erase = AlgebraicSpecialization.mul as bs := by
  induction as <;> simp_all [bmul, AlgebraicSpecialization.mul]
@[simp] theorem erase_bpower (as : B) (n : Nat) :
    (bpower as n).erase = AlgebraicSpecialization.power as n := by
  induction n <;> simp_all [bpower, AlgebraicSpecialization.power]
@[simp] theorem erase_bderivative (as : B) :
    (bderivative as).erase = AlgebraicSpecialization.derivative as := by
  induction as <;> simp_all [bderivative, AlgebraicSpecialization.derivative]
@[simp] theorem erase_atRational (as : B) (q : Rat) :
    (atRational as q).erase = AlgebraicSignReplay.atRational as q := by
  induction as <;> simp_all [atRational, AlgebraicSignReplay.atRational]

def bzero (d : Coefficients) (ps qs : B) : Replay Bool := visit fun _ =>
  match ps, qs with
  | [], [] => pure true
  | p :: ps, q :: qs => andThen (zero p d q) fun _ => bzero d ps qs
  | _, _ => pure false

def bidentity (d : Coefficients) (ps qs witness : B) : Replay Bool := do
  let negative ← bscale [-1] qs
  let sum ← badd ps negative
  bzero d sum witness

@[simp] theorem erase_bzero (d : Coefficients) (ps qs : B) :
    (bzero d ps qs).erase = AlgebraicSpecialization.zeroCheck d ps qs := by
  induction ps generalizing qs with
  | nil => cases qs <;> simp [bzero, AlgebraicSpecialization.zeroCheck]
  | cons p ps ih => cases qs <;> simp [bzero, AlgebraicSpecialization.zeroCheck, ih]
@[simp] theorem erase_bidentity (d : Coefficients) (ps qs witness : B) :
    (bidentity d ps qs witness).erase = AlgebraicSpecialization.identityCheck d ps qs witness := by
  simp [bidentity, AlgebraicSpecialization.identityCheck]

def algebraicSign (d p : Coefficients) (l u : Rat)
    (w : AlgebraicSignReplay.SignWitness) : Replay Bool := do
  tickP .algebraicCompare
  visit fun _ =>
    if w.sign = 0 then zero p d w.quotient
    else if w.sign = 1 then positiveRemainder p d w.quotient w.remainder l u
    else do
      let negative ← scale (-1) p
      positiveRemainder negative d w.quotient w.remainder l u

@[simp] theorem erase_algebraicSign (d p : Coefficients) (l u : Rat)
    (w : AlgebraicSignReplay.SignWitness) :
    (algebraicSign d p l u w).erase = AlgebraicSignReplay.signCheck d p l u w := by
  simp only [algebraicSign, erase_monadic_bind, erase_tickP, erase_visit]
  by_cases z : w.sign = 0
  · simp [z, AlgebraicSignReplay.signCheck]
  · by_cases pos : w.sign = 1 <;> simp [z, pos, AlgebraicSignReplay.signCheck]

def nonzeroValue (p : Coefficients) (x : Rat) : Replay Bool := do
  let y ← value p x
  let isZero ← eq y 0
  pure (!isZero)

@[simp] theorem erase_nonzeroValue (p : Coefficients) (x : Rat) :
    (nonzeroValue p x).erase = decide (RootCertificate.value p x ≠ 0) := by
  simp [nonzeroValue]

def selectedRoot (a : SelectedRoot.Root) : Replay Bool :=
  andThen (lt a.lower a.upper) fun _ =>
    andThen (nonzeroValue a.definer a.lower) fun _ =>
      andThen (nonzeroValue a.definer a.upper) fun _ =>
        andThen (rootCheck a.definer a.certificate) fun _ => do
          let count ← rootCount a.certificate a.lower a.upper
          metadata fun _ => decide (count = 1)

@[simp] theorem erase_selectedRoot (a : SelectedRoot.Root) :
    (selectedRoot a).erase = a.check := by
  simp [selectedRoot, SelectedRoot.Root.check, AlgebraicEmbedding.check, Bool.and_assoc] <;> rfl

def refinement (a : SelectedRoot.Root) (s : SelectedRoot.Refinement) : Replay Bool :=
  andThen (selectedRoot (s.root a)) fun _ =>
    andThen (lt a.lower s.lower) fun _ => lt s.upper a.upper

@[simp] theorem erase_refinement (a : SelectedRoot.Root) (s : SelectedRoot.Refinement) :
    (refinement a s).erase = s.check a := by
  simp [refinement, SelectedRoot.Refinement.check, Bool.decide_and, Bool.and_assoc]

def separated (a b : SelectedRoot.Root) (l r : SelectedRoot.Refinement) : Replay Bool :=
  andThen (refinement a l) fun _ => andThen (refinement b r) fun _ => le l.upper r.lower

@[simp] theorem erase_separated (a b : SelectedRoot.Root) (l r : SelectedRoot.Refinement) :
    (separated a b l r).erase = RootComparison.separated a b l r := by
  simp [separated, RootComparison.separated, Bool.and_assoc]

def common (a b c : SelectedRoot.Root) (qa qb : Coefficients) : Replay Bool :=
  andThen (selectedRoot c) fun _ =>
    andThen (andThen (lt a.lower c.lower) fun _ =>
      andThen (lt c.upper a.upper) fun _ =>
        andThen (lt b.lower c.lower) fun _ => lt c.upper b.upper) fun _ =>
      andThen (zero a.definer c.definer qa) fun _ => zero b.definer c.definer qb

@[simp] theorem erase_common (a b c : SelectedRoot.Root) (qa qb : Coefficients) :
    (common a b c qa qb).erase = RootComparison.commonCheck a b c qa qb := by
  simp [common, RootComparison.commonCheck, Bool.decide_and, Bool.and_assoc]

def comparison (a b : SelectedRoot.Root) (w : RootComparison.Certificate) :
    Replay (Option Ordering) := do
  tickP .algebraicCompare
  let valid ← andThen (selectedRoot a) fun _ => selectedRoot b
  if valid then visit fun _ =>
    match w with
    | .less l r => do let ok ← separated a b l r; pure (if ok then some .lt else none)
    | .greater l r => do let ok ← separated b a r l; pure (if ok then some .gt else none)
    | .equal c qa qb => do let ok ← common a b c qa qb; pure (if ok then some .eq else none)
  else pure none

@[simp] theorem erase_comparison (a b : SelectedRoot.Root) (w : RootComparison.Certificate) :
    (comparison a b w).erase = RootComparison.check a b w := by
  simp only [comparison, erase_monadic_bind, erase_tickP, erase_andThen, erase_selectedRoot]
  by_cases valid : (a.check && b.check) = true
  · cases w <;> simp [valid, RootComparison.check]
  · simp [valid, RootComparison.check]

def point (a : GlobalCheckerPoint.Point) : Replay Bool := visit fun _ =>
  match a with
  | .rational _ => pure true
  | .algebraic a => selectedRoot a

@[simp] theorem erase_point (a : GlobalCheckerPoint.Point) : (point a).erase = a.check := by
  cases a <;> simp [point, GlobalCheckerPoint.Point.check]

def pointSign (p : Coefficients) (a : GlobalCheckerPoint.Point)
    (w : GlobalCheckerPoint.SignWitness) : Replay (Option SignType) := visit fun _ =>
  match a, w with
  | .rational q, .rational => do let y ← value p q; let s ← ratSign y; pure (some s)
  | .algebraic a, .algebraic w => do
    let ok ← andThen (selectedRoot a) fun _ => algebraicSign a.definer p a.lower a.upper w
    pure (if ok then some w.sign else none)
  | _, _ => pure none

@[simp] theorem erase_pointSign (p : Coefficients) (a : GlobalCheckerPoint.Point)
    (w : GlobalCheckerPoint.SignWitness) :
    (pointSign p a w).erase = GlobalCheckerPoint.sign p a w := by
  cases a <;> cases w <;> simp [pointSign, GlobalCheckerPoint.sign]

theorem comparison_sound {a b : SelectedRoot.Root} {w : RootComparison.Certificate}
    {p : Profile} {used next : Vector} {answer : Ordering}
    (success : (comparison a b w).run p used = .ok (some answer, next))
    {x y : ℝ} (hx : a.Means x) (hy : b.Means y) :
    a.check = true ∧ b.check = true ∧ RootComparison.Relation answer x y := by
  have same := run_refines (comparison a b w) p used (some answer) next success
  rw [erase_comparison] at same
  exact RootComparison.check_sound same.symm hx hy

theorem pointSign_sound {p : Coefficients} {a : GlobalCheckerPoint.Point}
    {w : GlobalCheckerPoint.SignWitness} {profile : Profile} {used next : Vector}
    {answer : SignType}
    (success : (pointSign p a w).run profile used = .ok (some answer, next)) :
    a.check = true ∧ SignType.sign (eval p a.value) = answer := by
  have same := run_refines (pointSign p a w) profile used (some answer) next success
  rw [erase_pointSign] at same
  exact GlobalCheckerPoint.sign_sound same.symm

end ExactCIs.Unconditional.MeteredAlgebraicReplay
