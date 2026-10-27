/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicSignReplay
import ExactCIs.Unconditional.ORBernstein
import ExactCIs.Unconditional.NuisanceSupremum

/-! # Primitive reconstruction of Fisher comparisons and the OR objective

The outer bivariate variable is nuisance; coefficients are polynomials in
effect. Decision consumers reconstruct these executable lists from counts.
-/
namespace ExactCIs.Unconditional.ParametricPolynomial

open RootCertificate ProductBinomial BoschlooOrdering AlgebraicSpecialization

theorem sorted_sum {α : Type*} (rel : α → α → Prop) [DecidableRel rel]
    [IsTrans α rel] [Std.Antisymm rel] [Std.Total rel] (s : Finset α) (f : α → ℝ) :
    ((s.sort rel).map f).sum = ∑ a ∈ s, f a := by
  rw [List.Perm.sum_eq ((Finset.sort_perm_toList s rel).map f)]
  simp

def monomial (c : ℚ) (n : ℕ) : Coefficients :=
  RootCertificate.scale c (RootCertificate.power [0, 1] n)

theorem monomial_eval (c : ℚ) (n : ℕ) (x : ℝ) :
    eval (monomial c n) x = c * x ^ n := by
  simp [monomial, eval_scale, eval_power, eval]

def sum : List Coefficients → Coefficients
  | [] => []
  | p :: ps => RootCertificate.add p (sum ps)

theorem sum_eval (ps : List Coefficients) (x : ℝ) :
    eval (sum ps) x = (ps.map (fun p => eval p x)).sum := by
  induction ps <;> simp_all [sum, eval_add, eval]

def event (n1 n0 m : ℕ) (ks : Finset ℕ) : Coefficients :=
  sum ((ks.sort (· ≤ ·)).map fun k => monomial ((n1.choose k : ℚ) * n0.choose (m-k)) k)

theorem event_eval (n1 n0 m : ℕ) (ks : Finset ℕ) (x : ℝ) :
    eval (event n1 n0 m ks) x =
      ∑ k ∈ ks, FNCH.Recurrence.unnormalizedWeight n1 n0 k (m-k) x := by
  simp [event, sum_eval, List.map_map, Function.comp_def, monomial_eval, sorted_sum,
    FNCH.Recurrence.unnormalizedWeight]

def comparison {n1 n0 : ℕ} (dir : Direction) (candidate observed : Outcome n1 n0) :
    Coefficients :=
  let mc := candidate.1.val + candidate.2.val
  let mo := observed.1.val + observed.2.val
  RootCertificate.add
    (RootCertificate.mul (event n1 n0 mc (tailSet n1 n0 mc candidate.1.val dir))
      (event n1 n0 mo (FNCH.Support.valid n1 n0 mo)))
    (RootCertificate.scale (-1)
      (RootCertificate.mul (event n1 n0 mo (tailSet n1 n0 mo observed.1.val dir))
        (event n1 n0 mc (FNCH.Support.valid n1 n0 mc))))

theorem comparison_eval {n1 n0 : ℕ} (dir : Direction)
    (candidate observed : Outcome n1 n0) (x : ℝ) :
    eval (comparison dir candidate observed) x =
      realEval (comparisonPolynomial dir candidate observed) x := by
  rw [comparisonPolynomial_eval]
  simp [comparison, eval_add, eval_mul, eval_scale, event_eval, numerator, normalizer,
    sub_eq_add_neg]

theorem mask_iff {n1 n0 : ℕ} {x : ℝ} (positive : 0 < x) (dir : Direction)
    (candidate observed : Outcome n1 n0) :
    candidate ∈ mask dir x observed ↔ eval (comparison dir candidate observed) x ≤ 0 := by
  rw [mask_iff_polynomial positive, comparison_eval]

def sumB : List Bivariate → Bivariate
  | [] => []
  | p :: ps => AlgebraicSpecialization.add p (sumB ps)

theorem sumB_eval (ps : List Bivariate) (x q : ℝ) :
    (specialize x (sumB ps)).eval q =
      (ps.map fun p => (specialize x p).eval q).sum := by
  induction ps <;> simp_all [sumB, specialize_add, specialize]

def outcome {n1 n0 : ℕ} (o : Outcome n1 n0) : Bivariate :=
  AlgebraicSpecialization.scale
    (monomial ((n1.choose o.1.val : ℚ) * n0.choose o.2.val) o.1.val)
    (AlgebraicSpecialization.mul
      (AlgebraicSpecialization.power [[], [1]] (o.1.val + o.2.val))
      (AlgebraicSpecialization.power [[1], [-1]] (n1 + n0 - (o.1.val + o.2.val))))

theorem outcome_eval {n1 n0 : ℕ} (o : Outcome n1 n0) (x q : ℝ) :
    (specialize x (outcome o)).eval q = ORNull.numerator x q o := by
  simp [outcome, specialize_scale, specialize_mul, specialize_power,
    monomial_eval, specialize, eval, ORNull.numerator]
  ring

local instance lexAntisymm (n1 n0 : ℕ) :
    Std.Antisymm (fun a b : Outcome n1 n0 => toLex a ≤ toLex b) :=
  ⟨fun _ _ hab hba => toLex.injective (le_antisymm hab hba)⟩

def objective {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (r : ℚ) : Bivariate :=
  AlgebraicSpecialization.add (sumB ((mask.sort (fun a b => toLex a ≤ toLex b)).map outcome))
    (AlgebraicSpecialization.scale [-r]
      (sumB (((Finset.univ : Finset (Outcome n1 n0)).sort
        (fun a b => toLex a ≤ toLex b)).map outcome)))

theorem objective_eval {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (r : ℚ) (x q : ℝ) :
    (specialize x (objective mask r)).eval q = ORBernstein.threshold mask x r q := by
  simp [objective, specialize_add, specialize_scale, sumB_eval, List.map_map,
    Function.comp_def, sorted_sum,
    outcome_eval, eval, ORBernstein.threshold, ORBernstein.numerator_identity,
    sub_eq_add_neg]

theorem objective_accept_iff {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (r : ℚ)
    {x : ℝ} (positive : 0 < x) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1, 0 ≤ (specialize x (objective mask r)).eval q) ↔
      (r : ℝ) ≤ NuisanceSupremum.value mask x := by
  rw [NuisanceSupremum.accept_iff positive]
  constructor
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, (ORBernstein.threshold_iff positive hq mask).mpr
      ((objective_eval mask r x q) ▸ h)⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, hq, (objective_eval mask r x q).symm ▸
      (ORBernstein.threshold_iff positive hq mask).mp h⟩

end ExactCIs.Unconditional.ParametricPolynomial
