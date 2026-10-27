/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.FNCH.NormalizedMass
import ExactCIs.Unconditional.ORBernstein
import ExactCIs.Unconditional.OrderedPValue

/-!
# Actual inclusive Fisher ordering for the Boschloo OR construction

U0 B.5: tails use the feasible fixed-margin FNCH support and its positive
normalizer. These definitions have no nuisance argument. Finite positive effects
only; no structural-endpoint or executable root-checker correctness is claimed.
-/
namespace ExactCIs.Unconditional.BoschlooOrdering

open FNCH ProductBinomial

inductive Direction where
  | less
  | greater
  deriving DecidableEq

def tailSet (n1 n0 m x : ℕ) (direction : Direction) : Finset ℕ :=
  match direction with
  | .less => (Support.valid n1 n0 m).filter fun k => k ≤ x
  | .greater => (Support.valid n1 n0 m).filter fun k => x ≤ k

noncomputable def normalizer (n1 n0 m : ℕ) (psi : ℝ) : ℝ :=
  ∑ k ∈ Support.valid n1 n0 m, Recurrence.unnormalizedWeight n1 n0 k (m - k) psi

noncomputable def numerator (n1 n0 m x : ℕ) (direction : Direction) (psi : ℝ) : ℝ :=
  ∑ k ∈ tailSet n1 n0 m x direction, Recurrence.unnormalizedWeight n1 n0 k (m - k) psi

noncomputable def tail (n1 n0 m x : ℕ) (direction : Direction) (psi : ℝ) : ℝ :=
  numerator n1 n0 m x direction psi / normalizer n1 n0 m psi

theorem tailSet_subset (n1 n0 m x : ℕ) (direction : Direction) :
    tailSet n1 n0 m x direction ⊆ Support.valid n1 n0 m := by
  cases direction <;> exact Finset.filter_subset _ _

theorem normalizer_pos {n1 n0 m : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) : 0 < normalizer n1 n0 m psi :=
  PositiveNormalizer.normalizer_pos n1 n0 m margin positive

theorem tail_eq_eventMass {n1 n0 m x : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (direction : Direction) :
    tail n1 n0 m x direction psi =
      (NormalizedMass.finiteMass n1 n0 m psi margin positive).eventMass
        (tailSet n1 n0 m x direction) := by
  change (∑ k ∈ tailSet n1 n0 m x direction,
    Recurrence.unnormalizedWeight n1 n0 k (m - k) psi) / normalizer n1 n0 m psi = _
  rw [Finset.sum_div]
  rfl

theorem tail_mem_Icc {n1 n0 m x : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (direction : Direction) :
    tail n1 n0 m x direction psi ∈ Set.Icc (0 : ℝ) 1 := by
  rw [tail_eq_eventMass margin positive]
  exact ⟨FiniteMass.eventMass_nonnegative _ (tailSet_subset _ _ _ _ _),
    FiniteMass.eventMass_le_one _ (tailSet_subset _ _ _ _ _)⟩

theorem tail_pos {n1 n0 m x : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (supported : x ∈ Support.valid n1 n0 m) (direction : Direction) :
    0 < tail n1 n0 m x direction psi := by
  apply div_pos _ (normalizer_pos margin positive)
  apply Finset.sum_pos'
  · intro k hk
    exact (PositiveNormalizer.weight_pos n1 n0 m positive
      (tailSet_subset _ _ _ _ _ hk)).le
  · refine ⟨x, ?_, PositiveNormalizer.weight_pos n1 n0 m positive supported⟩
    cases direction <;> simp [tailSet, supported]

theorem singleton_tail {n1 n0 m x : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (singleton : Support.valid n1 n0 m = {x})
    (direction : Direction) : tail n1 n0 m x direction psi = 1 := by
  have full : tailSet n1 n0 m x direction = Support.valid n1 n0 m := by
    cases direction <;> simp [tailSet, singleton]
  rw [tail_eq_eventMass margin positive, full]
  exact FiniteMass.support_eventMass _

theorem less_tail_mono {n1 n0 m x y : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (ordered : x ≤ y) :
    tail n1 n0 m x .less psi ≤ tail n1 n0 m y .less psi := by
  rw [tail_eq_eventMass margin positive, tail_eq_eventMass margin positive]
  apply FiniteMass.eventMass_mono _ _ (tailSet_subset _ _ _ _ _)
  intro k hk
  simp only [tailSet, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, hk.2.trans ordered⟩

theorem greater_tail_antitone {n1 n0 m x y : ℕ} {psi : ℝ} (margin : m ≤ n1 + n0)
    (positive : 0 < psi) (ordered : x ≤ y) :
    tail n1 n0 m y .greater psi ≤ tail n1 n0 m x .greater psi := by
  rw [tail_eq_eventMass margin positive, tail_eq_eventMass margin positive]
  apply FiniteMass.eventMass_mono _ _ (tailSet_subset _ _ _ _ _)
  intro k hk
  simp only [tailSet, Finset.mem_filter] at hk ⊢
  exact ⟨hk.1, ordered.trans hk.2⟩

noncomputable def statistic {n1 n0 : ℕ} (direction : Direction) (psi : ℝ)
    (o : Outcome n1 n0) : ℝ := tail n1 n0 (o.1.val + o.2.val) o.1.val direction psi

theorem outcome_margin {n1 n0 : ℕ} (o : Outcome n1 n0) : o.1.val + o.2.val ≤ n1 + n0 := by
  have := o.1.isLt; have := o.2.isLt; omega

theorem outcome_supported {n1 n0 : ℕ} (o : Outcome n1 n0) :
    o.1.val ∈ Support.valid n1 n0 (o.1.val + o.2.val) := by
  rw [Support.mem_valid_iff]
  have := o.1.isLt; have := o.2.isLt; omega

theorem statistic_mem_Icc {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (o : Outcome n1 n0) : statistic direction psi o ∈ Set.Icc (0 : ℝ) 1 :=
  tail_mem_Icc (outcome_margin o) positive direction

noncomputable def mask {n1 n0 : ℕ} (direction : Direction) (psi : ℝ)
    (observed : Outcome n1 n0) : Finset (Outcome n1 n0) := by
  classical
  exact Finset.univ.filter fun o => statistic direction psi o ≤ statistic direction psi observed

theorem observed_mem_mask {n1 n0 : ℕ} (direction : Direction) (psi : ℝ)
    (observed : Outcome n1 n0) : observed ∈ mask direction psi observed := by
  classical
  simp [mask]

theorem full_mask_of_one {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (observed : Outcome n1 n0)
    (one : statistic direction psi observed = 1) : mask direction psi observed = Finset.univ := by
  classical
  ext o
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and]
  exact iff_true_intro (one ▸ (statistic_mem_Icc positive direction o).2)

/-- Both different-margin denominators in the literal U0 comparison are positive. -/
theorem comparison_iff {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (candidate observed : Outcome n1 n0) :
    statistic direction psi candidate ≤ statistic direction psi observed ↔
      numerator n1 n0 (candidate.1.val + candidate.2.val) candidate.1.val direction psi *
        normalizer n1 n0 (observed.1.val + observed.2.val) psi -
      numerator n1 n0 (observed.1.val + observed.2.val) observed.1.val direction psi *
        normalizer n1 n0 (candidate.1.val + candidate.2.val) psi ≤ 0 := by
  unfold statistic tail
  rw [div_le_div_iff₀ (normalizer_pos (outcome_margin candidate) positive)
    (normalizer_pos (outcome_margin observed) positive)]
  exact sub_nonpos.symm

noncomputable def eventPolynomial (n1 n0 m : ℕ) (event : Finset ℕ) : Polynomial ℚ :=
  ∑ k ∈ event, Polynomial.C ((n1.choose k : ℚ) * n0.choose (m - k)) * Polynomial.X ^ k

noncomputable def realEval (p : Polynomial ℚ) (psi : ℝ) : ℝ :=
  (p.map (Rat.castHom ℝ)).eval psi

theorem eventPolynomial_eval (n1 n0 m : ℕ) (event : Finset ℕ) (psi : ℝ) :
    realEval (eventPolynomial n1 n0 m event) psi =
      ∑ k ∈ event, Recurrence.unnormalizedWeight n1 n0 k (m - k) psi := by
  simp only [realEval, eventPolynomial, Polynomial.map_sum, Polynomial.eval_finsetSum,
    Polynomial.map_mul, Polynomial.map_pow, Polynomial.map_natCast, Polynomial.map_X,
    Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_natCast, Polynomial.eval_X,
    map_mul, map_natCast, Recurrence.unnormalizedWeight]

noncomputable def comparisonPolynomial {n1 n0 : ℕ} (direction : Direction)
    (candidate observed : Outcome n1 n0) : Polynomial ℚ :=
  let mc := candidate.1.val + candidate.2.val
  let mo := observed.1.val + observed.2.val
  eventPolynomial n1 n0 mc (tailSet n1 n0 mc candidate.1.val direction) *
    eventPolynomial n1 n0 mo (Support.valid n1 n0 mo) -
  eventPolynomial n1 n0 mo (tailSet n1 n0 mo observed.1.val direction) *
    eventPolynomial n1 n0 mc (Support.valid n1 n0 mc)

theorem comparisonPolynomial_eval {n1 n0 : ℕ} (direction : Direction)
    (candidate observed : Outcome n1 n0) (psi : ℝ) :
    realEval (comparisonPolynomial direction candidate observed) psi =
      numerator n1 n0 (candidate.1.val + candidate.2.val) candidate.1.val direction psi *
        normalizer n1 n0 (observed.1.val + observed.2.val) psi -
      numerator n1 n0 (observed.1.val + observed.2.val) observed.1.val direction psi *
        normalizer n1 n0 (candidate.1.val + candidate.2.val) psi := by
  simp only [comparisonPolynomial, realEval, Polynomial.map_sub, Polynomial.map_mul,
    Polynomial.eval_sub, Polynomial.eval_mul]
  change realEval _ psi * realEval _ psi - realEval _ psi * realEval _ psi = _
  simp only [eventPolynomial_eval, numerator, normalizer]

theorem mask_iff_polynomial {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (candidate observed : Outcome n1 n0) :
    candidate ∈ mask direction psi observed ↔
      realEval (comparisonPolynomial direction candidate observed) psi ≤ 0 := by
  classical
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [comparisonPolynomial_eval]
  exact comparison_iff positive direction candidate observed

theorem zero_comparison_permanent_tie {n1 n0 : ℕ} {psi : ℝ} (positive : 0 < psi)
    (direction : Direction) (candidate observed : Outcome n1 n0)
    (zero : comparisonPolynomial direction candidate observed = 0) :
    statistic direction psi candidate = statistic direction psi observed := by
  have equality :
      numerator n1 n0 (candidate.1.val + candidate.2.val) candidate.1.val direction psi *
        normalizer n1 n0 (observed.1.val + observed.2.val) psi =
      numerator n1 n0 (observed.1.val + observed.2.val) observed.1.val direction psi *
        normalizer n1 n0 (candidate.1.val + candidate.2.val) psi := by
    apply sub_eq_zero.mp
    rw [← comparisonPolynomial_eval, zero]
    simp [realEval]
  exact (div_eq_div_iff (normalizer_pos (outcome_margin candidate) positive).ne'
    (normalizer_pos (outcome_margin observed) positive).ne').mpr equality

/-- Each nonzero comparator has finitely many positive real breakpoints. -/
theorem finite_comparison_events {n1 n0 : ℕ} (direction : Direction)
    (candidate observed : Outcome n1 n0)
    (nonzero : comparisonPolynomial direction candidate observed ≠ 0) :
    Set.Finite {psi : ℝ | 0 < psi ∧
      realEval (comparisonPolynomial direction candidate observed) psi = 0} := by
  have finite := Polynomial.finite_setOfPred_isRoot
    (Polynomial.map_ne_zero (f := Rat.castHom ℝ) nonzero)
  exact finite.subset (fun _ h => h.2)

/-- Rational evaluation casts exactly to the real polynomial, with no tolerance. -/
theorem rational_eval_coercion (p : Polynomial ℚ) (psi : ℚ) :
    ((p.eval psi : ℚ) : ℝ) = realEval p psi := by
  simpa only [realEval, Rat.coe_castHom] using
    (Polynomial.eval_map_apply (f := Rat.castHom ℝ) (p := p) psi).symm

noncomputable def rationalStatistic {n1 n0 : ℕ} (direction : Direction) (psi : ℚ)
    (o : Outcome n1 n0) : ℚ :=
  (eventPolynomial n1 n0 (o.1.val + o.2.val)
    (tailSet n1 n0 (o.1.val + o.2.val) o.1.val direction)).eval psi /
  (eventPolynomial n1 n0 (o.1.val + o.2.val)
    (Support.valid n1 n0 (o.1.val + o.2.val))).eval psi

theorem rational_statistic_coercion {n1 n0 : ℕ} (direction : Direction) (psi : ℚ)
    (o : Outcome n1 n0) :
    (rationalStatistic direction psi o : ℝ) = statistic direction psi o := by
  unfold rationalStatistic statistic tail numerator normalizer
  rw [Rat.cast_div, rational_eval_coercion, rational_eval_coercion,
    eventPolynomial_eval, eventPolynomial_eval]

theorem rational_mask_agreement {n1 n0 : ℕ} (direction : Direction) (psi : ℚ)
    (candidate observed : Outcome n1 n0) :
    rationalStatistic direction psi candidate ≤ rationalStatistic direction psi observed ↔
      candidate ∈ mask direction (psi : ℝ) observed := by
  classical
  simp only [mask, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← rational_statistic_coercion, ← rational_statistic_coercion]
  exact_mod_cast Iff.rfl

/-- The actual nuisance-specific principal set is precisely the Fisher mask. -/
theorem principal_eq_mask {n1 n0 : ℕ} {psi q : ℝ} (positive : 0 < psi)
    (nuisance : q ∈ Set.Icc (0 : ℝ) 1) (direction : Direction)
    (observed : Outcome n1 n0) :
    OrderedPValue.principal (ORNull.mass n1 n0 psi q positive nuisance)
      (statistic direction psi) observed = mask direction psi observed := rfl

theorem fixed_nuisance_superuniform {n1 n0 : ℕ} {psi q cutoff : ℝ}
    (positive : 0 < psi) (nuisance : q ∈ Set.Icc (0 : ℝ) 1)
    (nonnegative : 0 ≤ cutoff) (direction : Direction) :
    (ORNull.mass n1 n0 psi q positive nuisance).eventMass
      (Finset.univ.filter fun observed =>
        (ORNull.mass n1 n0 psi q positive nuisance).eventMass
          (mask direction psi observed) ≤ cutoff) ≤ cutoff := by
  classical
  exact OrderedPValue.superuniform (ORNull.mass n1 n0 psi q positive nuisance)
    (statistic direction psi) cutoff nonnegative

/-- The union over the actual finite outcome space is finite as well. -/
theorem finite_all_comparison_events {n1 n0 : ℕ} (direction : Direction)
    (observed : Outcome n1 n0) :
    Set.Finite {psi : ℝ | 0 < psi ∧ ∃ candidate : Outcome n1 n0,
      comparisonPolynomial direction candidate observed ≠ 0 ∧
      realEval (comparisonPolynomial direction candidate observed) psi = 0} := by
  classical
  let events := fun candidate : Outcome n1 n0 =>
    {psi : ℝ | comparisonPolynomial direction candidate observed ≠ 0 ∧
      0 < psi ∧ realEval (comparisonPolynomial direction candidate observed) psi = 0}
  have finite : ∀ candidate, (events candidate).Finite := by
    intro candidate
    by_cases h : comparisonPolynomial direction candidate observed = 0
    · simp [events, h]
    · exact (finite_comparison_events direction candidate observed h).subset (fun _ hx => hx.2)
  apply (Set.finite_iUnion finite).subset
  rintro psi ⟨positive, candidate, nonzero, root⟩
  exact Set.mem_iUnion.mpr ⟨candidate, nonzero, positive, root⟩

theorem polynomial_sign_constant (p : Polynomial ℚ) {cell : Set ℝ}
    (connected : IsPreconnected cell)
    (no_zero : ∀ psi ∈ cell, realEval p psi ≠ 0)
    {left right : ℝ} (hl : left ∈ cell) (hr : right ∈ cell) :
    realEval p left ≤ 0 ↔ realEval p right ≤ 0 := by
  have continuous : ContinuousOn (realEval p) cell :=
    (p.map (Rat.castHom ℝ)).continuous.continuousOn
  have step : ∀ {x y : ℝ}, x ∈ cell → y ∈ cell → realEval p x ≤ 0 → realEval p y ≤ 0 := by
    intro x y hx hy nonpositive
    by_contra positive
    obtain ⟨z, hz, zero⟩ := connected.intermediate_value hx hy continuous
      (show (0 : ℝ) ∈ Set.Icc (realEval p x) (realEval p y) from
        ⟨nonpositive, (lt_of_not_ge positive).le⟩)
    exact no_zero z hz zero
  exact ⟨step hl hr, step hr hl⟩

/-- No-root connected cells have the actual same inclusive mask throughout.
Permanent ties are retained separately; no representative-sampling assumption
or continuity across an ordering event enters this statement. -/
theorem chamber_mask_eq {n1 n0 : ℕ} (direction : Direction) (observed : Outcome n1 n0)
    {cell : Set ℝ} (connected : IsPreconnected cell)
    (guards : ∀ candidate : Outcome n1 n0,
      comparisonPolynomial direction candidate observed = 0 ∨
      ∀ psi ∈ cell, realEval (comparisonPolynomial direction candidate observed) psi ≠ 0)
    {left right : ℝ} (left_positive : 0 < left) (right_positive : 0 < right)
    (hl : left ∈ cell) (hr : right ∈ cell) :
    mask direction left observed = mask direction right observed := by
  classical
  ext candidate
  rw [mask_iff_polynomial left_positive, mask_iff_polynomial right_positive]
  rcases guards candidate with tie | no_zero
  · simp [tie, realEval]
  · exact polynomial_sign_constant _ connected no_zero hl hr

/-- U0 B.18's unreduced cross product, with its required negative orientation. -/
theorem signedBreakpointAnchor (psi : ℝ) :
    realEval (comparisonPolynomial .less
      ((1, 3) : Outcome 4 4) ((0, 2) : Outcome 4 4)) psi =
      -2 * psi * (3 * psi ^ 3 - 23 * psi - 8) := by
  rw [comparisonPolynomial_eval]
  have s2 : FNCH.Support.valid 4 4 2 = {0, 1, 2} := by decide
  have s4 : FNCH.Support.valid 4 4 4 = {0, 1, 2, 3, 4} := by decide
  have t13 : tailSet 4 4 4 1 .less = {0, 1} := by decide
  have t02 : tailSet 4 4 2 0 .less = {0} := by decide
  have choose42 : Nat.choose 4 2 = 6 := by decide
  norm_num [numerator, normalizer, t13, t02, s2, s4, choose42,
    FNCH.Recurrence.unnormalizedWeight]
  ring

end ExactCIs.Unconditional.BoschlooOrdering
