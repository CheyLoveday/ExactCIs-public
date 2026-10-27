/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCertificate

/-!
# Checked algebraic identities at a selected real root

These checks use rational coefficient lists and exact identities. A selected
root need not have an irreducible definer. No quotient-ring field assumption,
Sturm-count theorem, certificate search completeness, or Python correspondence
is asserted. All interval sign claims require membership in the checked interval.
-/
namespace ExactCIs.Unconditional.AlgebraicCertificate

open RootCertificate

def nonzeroCheck (p : Coefficients) (l u : ℚ) : Bool :=
  positiveCheck p l u || negativeCheck p l u

theorem nonzeroCheck_sound {p : Coefficients} {l u : ℚ}
    (checked : nonzeroCheck p l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) : eval p x ≠ 0 := by
  have checks : positiveCheck p l u = true ∨ negativeCheck p l u = true := by
    simpa only [nonzeroCheck, Bool.or_eq_true] using checked
  rcases checks with hp | hn
  · exact (positiveCheck_sound hp hx).ne'
  · exact (negativeCheck_sound hn hx).ne

def rootSetCheck (h s quotient powerQuotient : Coefficients) (exponent : ℕ) : Bool :=
  decide (0 < exponent) && identityCheck h (mul s quotient) &&
    identityCheck (power s exponent) (mul h powerQuotient)

theorem rootSetCheck_sound {h s quotient powerQuotient : Coefficients} {exponent : ℕ}
    (checked : rootSetCheck h s quotient powerQuotient exponent = true) (x : ℝ) :
    eval h x = 0 ↔ eval s x = 0 := by
  have checks : (decide (0 < exponent) = true ∧
      identityCheck h (mul s quotient) = true) ∧
      identityCheck (power s exponent) (mul h powerQuotient) = true := by
    simpa only [rootSetCheck, Bool.and_eq_true] using checked
  have first := identityCheck_sound checks.1.2 x
  have second := identityCheck_sound checks.2 x
  simp only [eval_mul, eval_power] at first second
  constructor
  · intro zero
    rw [zero, zero_mul] at second
    exact (eq_zero_of_pow_eq_zero second)
  · intro zero
    rw [first, zero, zero_mul]

def zeroCheck (p d quotient : Coefficients) : Bool := identityCheck p (mul d quotient)

theorem zeroCheck_sound {p d quotient : Coefficients}
    (checked : zeroCheck p d quotient = true) {x : ℝ} (root : eval d x = 0) :
    eval p x = 0 := by
  rw [identityCheck_sound checked x, eval_mul, root, zero_mul]

def localizeCheck (d removed retained : Coefficients) (l u : ℚ) : Bool :=
  identityCheck d (mul removed retained) && nonzeroCheck removed l u

theorem localizeCheck_sound {d removed retained : Coefficients} {l u : ℚ}
    (checked : localizeCheck d removed retained l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) (root : eval d x = 0) : eval retained x = 0 := by
  have checks : identityCheck d (mul removed retained) = true ∧
      nonzeroCheck removed l u = true := by
    simpa only [localizeCheck, Bool.and_eq_true] using checked
  have identity := identityCheck_sound checks.1 x
  rw [eval_mul, root] at identity
  exact (mul_eq_zero.mp identity.symm).resolve_left (nonzeroCheck_sound checks.2 hx)

theorem localizeCheck_root_iff {d removed retained : Coefficients} {l u : ℚ}
    (checked : localizeCheck d removed retained l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) : eval d x = 0 ↔ eval retained x = 0 := by
  constructor
  · exact localizeCheck_sound checked hx
  · intro root
    have checks : identityCheck d (mul removed retained) = true ∧
        nonzeroCheck removed l u = true := by
      simpa only [localizeCheck, Bool.and_eq_true] using checked
    rw [identityCheck_sound checks.1 x, eval_mul, root, mul_zero]

def inverseCheck (d denominator inverse quotient : Coefficients) : Bool :=
  identityCheck (mul denominator inverse) (add [1] (mul d quotient))

theorem inverseCheck_sound {d denominator inverse quotient : Coefficients}
    (checked : inverseCheck d denominator inverse quotient = true) {x : ℝ}
    (root : eval d x = 0) :
    eval denominator x ≠ 0 ∧ eval inverse x = 1 / eval denominator x := by
  have identity := identityCheck_sound checked x
  simp only [eval_mul, eval_add, eval, Rat.cast_one, mul_zero, add_zero,
    root, zero_mul] at identity
  have nonzero : eval denominator x ≠ 0 := by
    intro zero
    rw [zero, zero_mul] at identity
    norm_num at identity
  refine ⟨nonzero, (eq_div_iff nonzero).mpr ?_⟩
  simpa [mul_comm] using identity

def positiveRemainderCheck (p d quotient remainder : Coefficients) (l u : ℚ) : Bool :=
  identityCheck p (add (mul d quotient) remainder) && positiveCheck remainder l u

theorem positiveRemainderCheck_sound {p d quotient remainder : Coefficients} {l u : ℚ}
    (checked : positiveRemainderCheck p d quotient remainder l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) (root : eval d x = 0) : 0 < eval p x := by
  have checks : identityCheck p (add (mul d quotient) remainder) = true ∧
      positiveCheck remainder l u = true := by
    simpa only [positiveRemainderCheck, Bool.and_eq_true] using checked
  rw [identityCheck_sound checks.1 x, eval_add, eval_mul, root, zero_mul, zero_add]
  exact positiveCheck_sound checks.2 hx

/-- A factored scale is part of the signed recurrence, even if it is negative. -/
def remainderCheck (a b quotient scale remainder : Coefficients) : Bool :=
  identityCheck a (add (mul b quotient) (mul scale remainder))

theorem remainderCheck_sound {a b quotient scale remainder : Coefficients}
    (checked : remainderCheck a b quotient scale remainder = true) (x : ℝ) :
    eval a x = eval b x * eval quotient x + eval scale x * eval remainder x := by
  simpa only [eval_add, eval_mul] using identityCheck_sound checked x

theorem remainderCheck_zero_divisor {a b quotient scale remainder : Coefficients}
    (checked : remainderCheck a b quotient scale remainder = true) {x : ℝ}
    (root : eval b x = 0) : eval a x = eval scale x * eval remainder x := by
  simpa only [root, zero_mul, zero_add] using remainderCheck_sound checked x

theorem positive_scale_invariant (p : Coefficients) {c : ℚ} (positive : 0 < c) (x : ℝ) :
    0 ≤ eval (scale c p) x ↔ 0 ≤ eval p x := by
  rw [eval_scale]
  exact mul_nonneg_iff_of_pos_left (by exact_mod_cast positive)

end ExactCIs.Unconditional.AlgebraicCertificate
