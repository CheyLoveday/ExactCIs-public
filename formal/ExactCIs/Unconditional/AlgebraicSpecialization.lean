/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicCertificate
import ExactCIs.Unconditional.PolynomialList
import ExactCIs.Unconditional.BoschlooOrdering

/-! # Guarded specialization at a selected real embedding

The outer variable is nuisance; each coefficient is a rational polynomial in
an effect. Modular witnesses are checked coefficient by coefficient. A definer
may be reducible. All semantic claims refer to the same selected real root.
-/
namespace ExactCIs.Unconditional.AlgebraicSpecialization

open RootCertificate Polynomial

abbrev Bivariate := List Coefficients

noncomputable def specialize (x : ℝ) : Bivariate → Polynomial ℝ
  | [] => 0
  | p :: ps => C (eval p x) + X * specialize x ps

def add : Bivariate → Bivariate → Bivariate
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => RootCertificate.add a b :: add as bs

def scale (c : Coefficients) (ps : Bivariate) : Bivariate :=
  ps.map (RootCertificate.mul c)

def mul : Bivariate → Bivariate → Bivariate
  | [], _ => []
  | p :: ps, qs => add (scale p qs) ([] :: mul ps qs)

def power (ps : Bivariate) : ℕ → Bivariate
  | 0 => [[1]]
  | n + 1 => mul ps (power ps n)

theorem specialize_add (x : ℝ) (ps qs : Bivariate) :
    specialize x (add ps qs) = specialize x ps + specialize x qs := by
  induction ps generalizing qs with
  | nil => simp [add, specialize]
  | cons p ps ih =>
    cases qs with
    | nil => simp [add, specialize]
    | cons q qs => simp [add, specialize, eval_add, ih]; ring

theorem specialize_scale (x : ℝ) (c : Coefficients) (ps : Bivariate) :
    specialize x (scale c ps) = C (eval c x) * specialize x ps := by
  induction ps with
  | nil => simp [scale, specialize]
  | cons p ps ih =>
    change specialize x (RootCertificate.mul c p :: scale c ps) = _
    rw [specialize, specialize, eval_mul, map_mul, ih]
    ring

theorem specialize_mul (x : ℝ) (ps qs : Bivariate) :
    specialize x (mul ps qs) = specialize x ps * specialize x qs := by
  induction ps with
  | nil => simp [mul, specialize]
  | cons p ps ih =>
    rw [mul, specialize_add, specialize_scale, specialize, specialize, ih]
    simp only [RootCertificate.eval, map_zero, zero_add]
    ring

theorem specialize_power (x : ℝ) (ps : Bivariate) (n : ℕ) :
    specialize x (power ps n) = specialize x ps ^ n := by
  induction n with
  | zero => simp [power, specialize, RootCertificate.eval]
  | succ n ih => simp [power, specialize_mul, ih, pow_succ, mul_comm]

/-- Formal derivative in the outer (nuisance) variable. -/
def derivative : Bivariate → Bivariate
  | [] => []
  | _ :: ps => add ps ([] :: derivative ps)

theorem specialize_derivative (x : ℝ) (ps : Bivariate) :
    specialize x (derivative ps) = (specialize x ps).derivative := by
  induction ps with
  | nil => simp [derivative, specialize]
  | cons p ps ih =>
    simp [derivative, specialize_add, specialize, ih, Polynomial.derivative_mul,
      RootCertificate.eval]

/-- Both lengths must match: unmatched witness coefficients are rejected. -/
def zeroCheck (d : Coefficients) : Bivariate → Bivariate → Bool
  | [], [] => true
  | p :: ps, q :: qs => AlgebraicCertificate.zeroCheck p d q && zeroCheck d ps qs
  | _, _ => false

theorem zeroCheck_sound {d : Coefficients} {ps qs : Bivariate}
    (checked : zeroCheck d ps qs = true) {x : ℝ} (root : eval d x = 0) :
    specialize x ps = 0 := by
  induction ps generalizing qs with
  | nil => simp [specialize]
  | cons p ps ih =>
    cases qs with
    | nil => simp [zeroCheck] at checked
    | cons q qs =>
      have checks : AlgebraicCertificate.zeroCheck p d q = true ∧
          zeroCheck d ps qs = true := by
        simpa only [zeroCheck, Bool.and_eq_true] using checked
      simp [specialize, AlgebraicCertificate.zeroCheck_sound checks.1 root, ih checks.2]

def identityCheck (d : Coefficients) (ps qs witness : Bivariate) : Bool :=
  zeroCheck d (add ps (scale [-1] qs)) witness

theorem identityCheck_sound {d : Coefficients} {ps qs witness : Bivariate}
    (checked : identityCheck d ps qs witness = true) {x : ℝ} (root : eval d x = 0) :
    specialize x ps = specialize x qs := by
  have h := zeroCheck_sound checked root
  rw [specialize_add, specialize_scale] at h
  apply sub_eq_zero.mp
  simpa [RootCertificate.eval, sub_eq_add_neg] using h

/-- A common effect denominator represents all rational-function coefficients.
It must be checked at the selected embedding before any division is used. -/
structure Fraction where
  numerator : Bivariate
  denominator : Coefficients
  deriving Repr

noncomputable def Fraction.value (f : Fraction) (x : ℝ) : Polynomial ℝ :=
  C ((eval f.denominator x)⁻¹) * specialize x f.numerator

def Fraction.guard (d : Coefficients) (f : Fraction)
    (inverse quotient : Coefficients) : Bool :=
  AlgebraicCertificate.inverseCheck d f.denominator inverse quotient

theorem denominator_nonzero {d inverse quotient : Coefficients} {f : Fraction}
    (checked : f.guard d inverse quotient = true) {x : ℝ} (root : eval d x = 0) :
    eval f.denominator x ≠ 0 :=
  (AlgebraicCertificate.inverseCheck_sound checked root).1

/-- Cross multiplication is legal only after checking both denominators. -/
def fractionIdentityCheck (d : Coefficients) (f g : Fraction) (witness : Bivariate) : Bool :=
  identityCheck d (scale g.denominator f.numerator) (scale f.denominator g.numerator) witness

theorem fractionIdentity_sound {d fi fq gi gq : Coefficients} {f g : Fraction}
    {witness : Bivariate} (left : f.guard d fi fq = true)
    (right : g.guard d gi gq = true)
    (checked : fractionIdentityCheck d f g witness = true)
    {x : ℝ} (root : eval d x = 0) : f.value x = g.value x := by
  have hf := denominator_nonzero left root
  have hg := denominator_nonzero right root
  have h := identityCheck_sound checked root
  simp only [specialize_scale] at h
  apply Polynomial.ext
  intro n
  have hc := congrArg (fun p : Polynomial ℝ => p.coeff n) h
  simp only [Fraction.value, coeff_C_mul] at hc ⊢
  field_simp [hf, hg]
  nlinarith [hc]

/-- A checked inverse turns rational-function coefficients into polynomial
coefficients at this embedding, suitable for modular signed-chain replay. -/
theorem fraction_realization {d inverse quotient : Coefficients} {f : Fraction}
    (checked : f.guard d inverse quotient = true) {x : ℝ} (root : eval d x = 0) :
    specialize x (scale inverse f.numerator) = f.value x := by
  rw [specialize_scale, (AlgebraicCertificate.inverseCheck_sound checked root).2]
  simp [Fraction.value, one_div]

/-- Retain the actual signed denominator; multiplying by its square is safe. -/
theorem fraction_nonnegative_iff {d inverse quotient : Coefficients} {f : Fraction}
    (checked : f.guard d inverse quotient = true) {x : ℝ} (root : eval d x = 0) (q : ℝ) :
    0 ≤ (f.value x).eval q ↔
      0 ≤ eval f.denominator x * (specialize x f.numerator).eval q := by
  have hd := denominator_nonzero checked root
  simp only [Fraction.value, Polynomial.eval_mul, Polynomial.eval_C]
  rcases lt_or_gt_of_ne hd with hn | hp
  · have hi := inv_lt_zero.mpr hn
    simp [mul_nonneg_iff, hi.le, hn.le, not_le.mpr hi, not_le.mpr hn]
  · rw [mul_nonneg_iff_of_pos_left (inv_pos.mpr hp), mul_nonneg_iff_of_pos_left hp]

/-- Exact zero is inclusive; the numerator need not have a definite sign nearby. -/
theorem fraction_zero_iff {d inverse quotient : Coefficients} {f : Fraction}
    (checked : f.guard d inverse quotient = true) {x : ℝ} (root : eval d x = 0) (q : ℝ) :
    (f.value x).eval q = 0 ↔ (specialize x f.numerator).eval q = 0 := by
  have hd := denominator_nonzero checked root
  simp [Fraction.value, hd]

/-- Positive leading-coefficient information is unnecessary: nonzero is enough
for exact specialized degree, and its sign is retained elsewhere. -/
theorem specialized_degree (x : ℝ) (ps : Bivariate) (n : ℕ)
    (above : ∀ k, n < k → (specialize x ps).coeff k = 0)
    (leading : (specialize x ps).coeff n ≠ 0) : (specialize x ps).degree = n := by
  apply le_antisymm
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro k hk
    exact above k (by exact_mod_cast hk)
  · exact Polynomial.le_degree_of_ne_zero leading

/-- Selected-root comparator evidence is tied to the actual inclusive mask. -/
theorem actual_mask_iff {n1 n0 : ℕ} {x : ℝ} (positive : 0 < x)
    (direction : BoschlooOrdering.Direction) (candidate observed : ProductBinomial.Outcome n1 n0)
    (p : Coefficients)
    (binding : PolynomialList.polynomial p =
      BoschlooOrdering.comparisonPolynomial direction candidate observed) :
    candidate ∈ BoschlooOrdering.mask direction x observed ↔ eval p x ≤ 0 := by
  rw [BoschlooOrdering.mask_iff_polynomial positive]
  rw [← binding]
  simpa only [BoschlooOrdering.realEval, Polynomial.eval_map] using
    (PolynomialList.polynomial_eval p x).symm ▸ Iff.rfl

theorem actual_mask_tie {n1 n0 : ℕ} {x : ℝ} (positive : 0 < x)
    (direction : BoschlooOrdering.Direction) (candidate observed : ProductBinomial.Outcome n1 n0)
    {p d quotient : Coefficients}
    (binding : PolynomialList.polynomial p =
      BoschlooOrdering.comparisonPolynomial direction candidate observed)
    (checked : AlgebraicCertificate.zeroCheck p d quotient = true) (root : eval d x = 0) :
    candidate ∈ BoschlooOrdering.mask direction x observed := by
  rw [actual_mask_iff positive direction candidate observed p binding,
    AlgebraicCertificate.zeroCheck_sound checked root]

end ExactCIs.Unconditional.AlgebraicSpecialization
