/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ParametricPolynomial
import ExactCIs.Unconditional.CanonicalEncoding
import ExactCIs.Unconditional.EffectCoordinate

/-! # Executable positive-factor substitution into the compact effect chart

The degree bound is checked, never inferred from a candidate identity. Every
nuisance coefficient is transformed with the same effect degree. The multiplier
is strictly positive only on the open chart; structural points remain separate.
-/
namespace ExactCIs.Unconditional.CompactPolynomial

open RootCertificate AlgebraicSpecialization

def transform : ℕ → Coefficients → Coefficients
  | _, [] => []
  | 0, c :: _ => [c]
  | n + 1, c :: cs => RootCertificate.add
      (RootCertificate.scale c (RootCertificate.power [1, -1] (n + 1)))
      (RootCertificate.mul [0, 1] (transform n cs))

theorem transform_eval (n : ℕ) (p : Coefficients) (degree : p.length ≤ n + 1)
    {s : ℝ} (denominator : 1 - s ≠ 0) :
    eval (transform n p) s = (1 - s) ^ n * eval p (s / (1 - s)) := by
  induction n generalizing p with
  | zero =>
    cases p with
    | nil => simp [transform, eval]
    | cons c cs =>
      have empty : cs = [] := by
        apply List.length_eq_zero_iff.mp
        simp only [List.length_cons] at degree
        omega
      subst cs
      simp [transform, eval]
  | succ n ih =>
    cases p with
    | nil => simp [transform, eval]
    | cons c cs =>
      have tail : cs.length ≤ n + 1 := by simpa using degree
      rw [transform, eval_add, eval_scale, eval_power, eval_mul, ih cs tail]
      simp only [eval, Rat.cast_one, Rat.cast_neg, Rat.cast_zero, mul_zero, add_zero,
        mul_one, zero_add]
      rw [show (1 : ℝ) + s * -1 = 1 - s by ring, pow_succ]
      field_simp

def transformB (degree : ℕ) (p : Bivariate) : Bivariate := p.map (transform degree)

def degreeCheck (degree : ℕ) (p : Bivariate) : Bool :=
  p.all fun c => decide (c.length ≤ degree + 1)

def degreeBound : Bivariate → ℕ
  | [] => 0
  | c :: cs => max c.length (degreeBound cs)

theorem degreeBound_checks (p : Bivariate) : degreeCheck (degreeBound p) p = true := by
  have bound : ∀ c ∈ p, c.length ≤ degreeBound p := by
    induction p with
    | nil => simp
    | cons d ds ih =>
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact le_max_left _ _
      · exact (ih c hc).trans (le_max_right _ _)
  apply List.all_eq_true.mpr
  intro c hc
  exact decide_eq_true (by have := bound c hc; omega)

def comparison {n1 n0 : ℕ} (direction : BoschlooOrdering.Direction)
    (candidate observed : ProductBinomial.Outcome n1 n0) : Coefficients :=
  let p := ParametricPolynomial.comparison direction candidate observed
  transform p.length p

def objective {n1 n0 : ℕ} (mask : Finset (ProductBinomial.Outcome n1 n0))
    (r : ℚ) : Bivariate :=
  let p := ParametricPolynomial.objective mask r
  transformB (degreeBound p) p

theorem transformB_eval (degree : ℕ) (p : Bivariate)
    (checked : degreeCheck degree p = true) {s : ℝ} (denominator : 1 - s ≠ 0) (q : ℝ) :
    (specialize s (transformB degree p)).eval q =
      (1 - s) ^ degree * (specialize (s / (1 - s)) p).eval q := by
  induction p with
  | nil => simp [transformB, specialize]
  | cons c cs ih =>
    have checks : c.length ≤ degree + 1 ∧ degreeCheck degree cs = true := by
      simpa only [degreeCheck, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] using checked
    simp only [transformB, List.map_cons, specialize, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    rw [transform_eval degree c checks.1 denominator]
    have ht := ih checks.2
    dsimp only [transformB] at ht
    rw [ht]
    ring

theorem transform_sign (n : ℕ) (p : Coefficients) (degree : p.length ≤ n + 1)
    {s : ℝ} (inside : s ∈ Set.Ioo (0 : ℝ) 1) :
    SignType.sign (eval (transform n p) s) =
      SignType.sign (eval p (EffectCoordinate.beta s)) := by
  rw [transform_eval n p degree (sub_pos.mpr inside.2).ne', sign_mul,
    sign_pos (pow_pos (sub_pos.mpr inside.2) n), one_mul]
  rfl

theorem transformB_nonnegative (degree : ℕ) (p : Bivariate)
    (checked : degreeCheck degree p = true) {s : ℝ} (inside : s ∈ Set.Ioo (0 : ℝ) 1) (q : ℝ) :
    0 ≤ (specialize s (transformB degree p)).eval q ↔
      0 ≤ (specialize (EffectCoordinate.beta s) p).eval q := by
  rw [transformB_eval degree p checked (sub_pos.mpr inside.2).ne']
  exact mul_nonneg_iff_of_pos_left (pow_pos (sub_pos.mpr inside.2) degree)

theorem objective_accept_iff {n1 n0 : ℕ} (mask : Finset (ProductBinomial.Outcome n1 n0))
    (r : ℚ) (degree : ℕ)
    (checked : degreeCheck degree (ParametricPolynomial.objective mask r) = true)
    {s : ℝ} (inside : s ∈ Set.Ioo (0 : ℝ) 1) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1,
      0 ≤ (specialize s (transformB degree (ParametricPolynomial.objective mask r))).eval q) ↔
      (r : ℝ) ≤ NuisanceSupremum.value mask (EffectCoordinate.beta s) := by
  simp_rw [transformB_nonnegative degree _ checked inside]
  exact ParametricPolynomial.objective_accept_iff mask r
    (div_pos inside.1 (sub_pos.mpr inside.2))

theorem comparison_sign {n1 n0 : ℕ} (direction : BoschlooOrdering.Direction)
    (candidate observed : ProductBinomial.Outcome n1 n0) {s : ℝ}
    (inside : s ∈ Set.Ioo (0 : ℝ) 1) :
    SignType.sign (eval (comparison direction candidate observed) s) =
      SignType.sign (eval (ParametricPolynomial.comparison direction candidate observed)
        (EffectCoordinate.beta s)) :=
  transform_sign _ _ (by omega) inside

theorem reconstructed_objective_accept_iff {n1 n0 : ℕ}
    (mask : Finset (ProductBinomial.Outcome n1 n0)) (r : ℚ) {s : ℝ}
    (inside : s ∈ Set.Ioo (0 : ℝ) 1) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (specialize s (objective mask r)).eval q) ↔
      (r : ℝ) ≤ NuisanceSupremum.value mask (EffectCoordinate.beta s) :=
  objective_accept_iff mask r _ (degreeBound_checks _) inside

end ExactCIs.Unconditional.CompactPolynomial
