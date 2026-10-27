/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicRootCertificate
import ExactCIs.Unconditional.AlgebraicEmbedding

/-! # Executable endpoint-sign replay at an isolated algebraic effect -/
namespace ExactCIs.Unconditional.AlgebraicSignReplay

open RootCertificate AlgebraicSpecialization SturmVariation

structure SignWitness where
  sign : SignType
  quotient : Coefficients
  remainder : Coefficients

def signCheck (d p : Coefficients) (l u : ℚ) (w : SignWitness) : Bool :=
  if w.sign = 0 then AlgebraicCertificate.zeroCheck p d w.quotient
  else if w.sign = 1 then
    AlgebraicCertificate.positiveRemainderCheck p d w.quotient w.remainder l u
  else AlgebraicCertificate.positiveRemainderCheck (RootCertificate.scale (-1) p)
    d w.quotient w.remainder l u

theorem signCheck_sound {d p : Coefficients} {l u : ℚ} {w : SignWitness}
    (checked : signCheck d p l u w = true) {x : ℝ}
    (root : eval d x = 0) (inside : x ∈ Set.Icc (l : ℝ) u) :
    SignType.sign (eval p x) = w.sign := by
  rcases w with ⟨s, quotient, remainder⟩
  cases s with
  | zero =>
    simp only [signCheck, SignType.zero_eq_zero, ite_true] at checked
    rw [AlgebraicCertificate.zeroCheck_sound checked root]
    simp
  | pos =>
    simp only [signCheck, SignType.pos_eq_one, one_ne_zero, ite_false, ite_true] at checked
    exact sign_pos (AlgebraicCertificate.positiveRemainderCheck_sound checked inside root)
  | neg =>
    simp only [signCheck, SignType.neg_eq_neg_one] at checked
    have positive := AlgebraicCertificate.positiveRemainderCheck_sound checked inside root
    simp only [eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul] at positive
    exact sign_neg (by linarith)

def atRational : Bivariate → ℚ → Coefficients
  | [], _ => []
  | p :: ps, q => RootCertificate.add p (RootCertificate.scale q (atRational ps q))

theorem atRational_sound (ps : Bivariate) (q : ℚ) (x : ℝ) :
    eval (atRational ps q) x = (specialize x ps).eval (q : ℝ) := by
  induction ps with
  | nil => simp [atRational, eval, specialize]
  | cons p ps ih =>
    simp [atRational, eval_add, eval_scale, specialize, ih]

def signsCheck (d : Coefficients) (l u q : ℚ) : List Bivariate → List SignWitness → Bool
  | [], [] => true
  | p :: ps, w :: ws => signCheck d (atRational p q) l u w && signsCheck d l u q ps ws
  | _, _ => false

theorem signsCheck_sound {d : Coefficients} {l u q : ℚ}
    {ps : List Bivariate} {ws : List SignWitness}
    (checked : signsCheck d l u q ps ws = true) {x : ℝ}
    (root : eval d x = 0) (inside : x ∈ Set.Icc (l : ℝ) u) :
    (ps.map fun p => SignType.sign ((specialize x p).eval (q : ℝ))) = ws.map SignWitness.sign := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp_all [signsCheck]
  | cons p ps ih =>
    cases ws with
    | nil => simp [signsCheck] at checked
    | cons w ws =>
      have h : signCheck d (atRational p q) l u w = true ∧
          signsCheck d l u q ps ws = true := by
        simpa only [signsCheck, Bool.and_eq_true] using checked
      have sign := signCheck_sound h.1 root inside
      rw [atRational_sound] at sign
      simp only [List.map_cons, sign, ih h.2]

def count (left right : List SignWitness) : ℕ :=
  variations (left.map SignWitness.sign) - variations (right.map SignWitness.sign)

theorem count_sound {d : Coefficients} {h : Bivariate} {c : AlgebraicRootCertificate.Certificate}
    (checked : AlgebraicRootCertificate.check d h c = true) {l u a b : ℚ}
    {left right : List SignWitness}
    (left_checked : signsCheck d l u a (c.representative :: c.tail) left = true)
    (right_checked : signsCheck d l u b (c.representative :: c.tail) right = true)
    {x : ℝ} (root : eval d x = 0) (inside : x ∈ Set.Icc (l : ℝ) u) (ordered : a ≤ b) :
    count left right = {q : ℝ | (a : ℝ) < q ∧ q ≤ (b : ℝ) ∧
      (specialize x h).eval q = 0}.ncard := by
  have hl := signsCheck_sound left_checked root inside
  have hr := signsCheck_sound right_checked root inside
  have result := AlgebraicRootCertificate.count_sound checked root
    (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast ordered)
  simpa only [count, AlgebraicRootCertificate.count, variationAt, List.map_map,
    Function.comp_def, hl, hr] using result

theorem acceptance_iff {d : Coefficients} {h : Bivariate} {c : AlgebraicRootCertificate.Certificate}
    (checked : AlgebraicRootCertificate.check d h c = true) {l u a b : ℚ}
    {left right : List SignWitness} {original : SignWitness}
    (left_checked : signsCheck d l u a (c.representative :: c.tail) left = true)
    (right_checked : signsCheck d l u b (c.representative :: c.tail) right = true)
    (original_checked : signCheck d (atRational h a) l u original = true)
    (negative : original.sign = -1)
    {x : ℝ} (root : eval d x = 0) (inside : x ∈ Set.Icc (l : ℝ) u) (ordered : a ≤ b) :
    (∃ q ∈ Set.Icc (a : ℝ) b, 0 ≤ (specialize x h).eval q) ↔ 0 < count left right := by
  have sign := signCheck_sound original_checked root inside
  rw [atRational_sound, negative] at sign
  have hn : (specialize x h).eval (a : ℝ) < 0 := by
    exact sign_eq_neg_one_iff.mp sign
  have result := AlgebraicRootCertificate.negative_left_acceptance checked root
    (show (a : ℝ) ≤ (b : ℝ) by exact_mod_cast ordered) hn
  have hl := signsCheck_sound left_checked root inside
  have hr := signsCheck_sound right_checked root inside
  simpa only [count, AlgebraicRootCertificate.count, variationAt, List.map_map,
    Function.comp_def, hl, hr] using result

end ExactCIs.Unconditional.AlgebraicSignReplay
