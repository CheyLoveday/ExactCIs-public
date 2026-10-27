/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ParametricPolynomial
import ExactCIs.Unconditional.RootSignCertificate

/-! # Whole-cell signs from exact rational root/sign certificates

A nonzero sign means strict sign everywhere on the closed real interval;
a zero sign requires an exact polynomial identity. No representative sampling.
-/
namespace ExactCIs.Unconditional.StratumSignReplay

open RootCertificate AlgebraicSpecialization

structure SignWitness where
  sign : SignType
  root : RootCountCertificate.Certificate

def signCheck (p : Coefficients) (l u : ℚ) (w : SignWitness) : Bool :=
  if w.sign = 0 then RootCertificate.identityCheck p []
  else if w.sign = 1 then
    decide (RootSignCertificate.check (RootCertificate.scale (-1) p) l u w.root = some false)
  else decide (RootSignCertificate.check p l u w.root = some false)

theorem signCheck_sound {p : Coefficients} {l u : ℚ} {w : SignWitness}
    (checked : signCheck p l u w = true) {x : ℝ} (inside : x ∈ Set.Icc (l : ℝ) u) :
    SignType.sign (eval p x) = w.sign := by
  rcases w with ⟨s, c⟩
  cases s with
  | zero =>
    simp only [signCheck, SignType.zero_eq_zero, ite_true] at checked
    rw [RootCertificate.identityCheck_sound checked x]
    simp [eval]
  | pos =>
    simp only [signCheck, SignType.pos_eq_one, one_ne_zero, ite_false, ite_true,
      decide_eq_true_eq] at checked
    have h := RootSignCertificate.rejected_strict checked x inside
    simp only [eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul] at h
    exact sign_pos (by linarith)
  | neg =>
    simp only [signCheck, SignType.neg_eq_neg_one] at checked
    exact sign_neg (RootSignCertificate.rejected_strict (of_decide_eq_true checked) x inside)

structure NonzeroWitness where
  positive : Bool
  root : RootCountCertificate.Certificate

def nonzeroCheck (p : Coefficients) (l u : ℚ) (w : NonzeroWitness) : Bool :=
  signCheck p l u ⟨if w.positive then 1 else -1, w.root⟩

theorem nonzeroCheck_sound {p : Coefficients} {l u : ℚ} {w : NonzeroWitness}
    (checked : nonzeroCheck p l u w = true) {x : ℝ} (inside : x ∈ Set.Icc (l : ℝ) u) :
    eval p x ≠ 0 := by
  have h := signCheck_sound checked inside
  intro zero
  rw [zero] at h
  cases hp : w.positive <;> simp [hp] at h

/-- Exact bivariate identities hold at every real effect, without a definer. -/
def identityCheck (p q : Bivariate) : Bool :=
  AlgebraicSpecialization.identityCheck [] p q
    (List.replicate (AlgebraicSpecialization.add p
      (AlgebraicSpecialization.scale [-1] q)).length [])

theorem identityCheck_sound {p q : Bivariate} (checked : identityCheck p q = true) (x : ℝ) :
    specialize x p = specialize x q :=
  AlgebraicSpecialization.identityCheck_sound checked (by rfl : eval [] x = 0)

def signsCheck (l u q : ℚ) : List Bivariate → List SignWitness → Bool
  | [], [] => true
  | p :: ps, w :: ws => signCheck (AlgebraicSignReplay.atRational p q) l u w &&
      signsCheck l u q ps ws
  | _, _ => false

theorem signsCheck_sound {l u q : ℚ} {ps : List Bivariate} {ws : List SignWitness}
    (checked : signsCheck l u q ps ws = true) {x : ℝ} (inside : x ∈ Set.Icc (l : ℝ) u) :
    (ps.map fun p => SignType.sign ((specialize x p).eval (q : ℝ))) = ws.map SignWitness.sign := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp_all [signsCheck]
  | cons p ps ih =>
    cases ws with
    | nil => simp [signsCheck] at checked
    | cons w ws =>
      have h : signCheck (AlgebraicSignReplay.atRational p q) l u w = true ∧
          signsCheck l u q ps ws = true := by
        simpa only [signsCheck, Bool.and_eq_true] using checked
      have hs := signCheck_sound h.1 inside
      rw [AlgebraicSignReplay.atRational_sound] at hs
      simp only [List.map_cons, hs, ih h.2]

def count (left right : List SignWitness) : ℕ :=
  SturmVariation.variations (left.map SignWitness.sign) -
    SturmVariation.variations (right.map SignWitness.sign)

end ExactCIs.Unconditional.StratumSignReplay
