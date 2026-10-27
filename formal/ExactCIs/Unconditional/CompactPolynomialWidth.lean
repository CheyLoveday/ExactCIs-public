/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.CompactPolynomial

/-! # Exact raw nuisance widths before modular witness padding

These are list lengths of the frozen constructors, including rows whose
polynomial meaning is zero. Semantic degree cannot replace these widths.
No trimming, signed-polynomial change or protocol change is performed here.
-/
namespace ExactCIs.Unconditional.CompactPolynomialWidth

open AlgebraicSpecialization ProductBinomial

def mulWidth (a b : ℕ) : ℕ :=
  if a = 0 then 0 else if b = 0 then a else a + b - 1

theorem mulWidth_succ (a b : ℕ) :
    mulWidth (a + 1) b = max b (mulWidth a b + 1) := by
  by_cases az : a = 0 <;> by_cases bz : b = 0 <;> simp [mulWidth, az, bz] <;> omega

theorem add_length (ps qs : Bivariate) :
    (AlgebraicSpecialization.add ps qs).length = max ps.length qs.length := by
  induction ps generalizing qs with
  | nil => simp [AlgebraicSpecialization.add]
  | cons p ps ih =>
    cases qs with
    | nil => simp [AlgebraicSpecialization.add]
    | cons q qs =>
      simp only [AlgebraicSpecialization.add, List.length_cons, ih]
      omega

theorem scale_length (c : RootCertificate.Coefficients) (ps : Bivariate) :
    (AlgebraicSpecialization.scale c ps).length = ps.length := by
  simp only [AlgebraicSpecialization.scale, List.length_map]

theorem mul_length (ps qs : Bivariate) :
    (AlgebraicSpecialization.mul ps qs).length = mulWidth ps.length qs.length := by
  induction ps with
  | nil => simp [AlgebraicSpecialization.mul, mulWidth]
  | cons p ps ih =>
    rw [AlgebraicSpecialization.mul, add_length, scale_length, List.length_cons, ih]
    exact (mulWidth_succ ps.length qs.length).symm

def powerWidth (a : ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 => mulWidth a (powerWidth a n)

theorem power_length (ps : Bivariate) (n : ℕ) :
    (AlgebraicSpecialization.power ps n).length = powerWidth ps.length n := by
  induction n with
  | zero => simp [AlgebraicSpecialization.power, powerWidth]
  | succ n ih => rw [AlgebraicSpecialization.power, mul_length, ih, powerWidth]

theorem powerWidth_two (n : ℕ) : powerWidth 2 n = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [powerWidth, ih]; simp [mulWidth]; omega

theorem derivative_length (ps : Bivariate) :
    (AlgebraicSpecialization.derivative ps).length = ps.length := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    rw [AlgebraicSpecialization.derivative, add_length, List.length_cons, ih,
      List.length_cons]
    exact max_eq_right (Nat.le_succ _)

theorem outcome_length {n1 n0 : ℕ} (o : Outcome n1 n0) :
    (ParametricPolynomial.outcome o).length = n1 + n0 + 1 := by
  have first := o.1.isLt
  have second := o.2.isLt
  have total : o.1.val + o.2.val ≤ n1 + n0 := by omega
  rw [ParametricPolynomial.outcome, scale_length, mul_length, power_length, power_length]
  simp only [List.length_cons, List.length_nil]
  simp [mulWidth, powerWidth_two]
  omega

theorem sumB_length_le (ps : List Bivariate) (width : ℕ)
    (bounded : ∀ p ∈ ps, p.length ≤ width) :
    (ParametricPolynomial.sumB ps).length ≤ width := by
  revert bounded
  induction ps with
  | nil => intro _; simp [ParametricPolynomial.sumB]
  | cons p ps ih =>
    intro bounded
    rw [ParametricPolynomial.sumB, add_length]
    exact max_le (bounded p (by simp)) (ih (fun q member => bounded q (by simp [member])))

theorem sumB_length (ps : List Bivariate) (width : ℕ) (nonempty : ps ≠ [])
    (equal : ∀ p ∈ ps, p.length = width) :
    (ParametricPolynomial.sumB ps).length = width := by
  apply Nat.le_antisymm (sumB_length_le ps width (fun p member => (equal p member).le))
  cases ps with
  | nil => contradiction
  | cons p ps =>
    rw [ParametricPolynomial.sumB, add_length, equal p (by simp)]
    exact le_max_left _ _

local instance lexAntisymm (n1 n0 : ℕ) :
    Std.Antisymm (fun a b : Outcome n1 n0 => toLex a ≤ toLex b) :=
  ⟨fun _ _ hab hba => toLex.injective (le_antisymm hab hba)⟩

theorem parametric_objective_length {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (r : ℚ) :
    (ParametricPolynomial.objective mask r).length = n1 + n0 + 1 := by
  let total := (((Finset.univ : Finset (Outcome n1 n0)).sort
    (fun a b => toLex a ≤ toLex b)).map ParametricPolynomial.outcome)
  have positive : 0 < (Finset.univ : Finset (Outcome n1 n0)).card :=
    Finset.card_pos.mpr Finset.univ_nonempty
  have total_nonempty : total ≠ [] := by
    intro empty
    have width : total.length = (Finset.univ : Finset (Outcome n1 n0)).card := by
      simp [total]
    rw [empty, List.length_nil] at width
    omega
  have total_width : (ParametricPolynomial.sumB total).length = n1 + n0 + 1 := by
    apply sumB_length total _ total_nonempty
    intro p member
    obtain ⟨o, _, rfl⟩ := List.mem_map.mp member
    exact outcome_length o
  rw [ParametricPolynomial.objective, add_length, scale_length, total_width]
  apply max_eq_right
  apply sumB_length_le
  intro p member
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp member
  exact (outcome_length o).le

theorem transformB_length (degree : ℕ) (ps : Bivariate) :
    (CompactPolynomial.transformB degree ps).length = ps.length := by
  simp only [CompactPolynomial.transformB, List.length_map]

theorem objective_length {n1 n0 : ℕ} (mask : Finset (Outcome n1 n0)) (r : ℚ) :
    (CompactPolynomial.objective mask r).length = n1 + n0 + 1 := by
  rw [CompactPolynomial.objective, transformB_length, parametric_objective_length]

end ExactCIs.Unconditional.CompactPolynomialWidth
