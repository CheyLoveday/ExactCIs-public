/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SturmVariation

/-! # From local Sturm variations to exact distinct real-root counts -/
namespace ExactCIs.Unconditional.SturmRootCount

open Filter Topology SturmVariation

noncomputable def past (roots : Finset ℝ) (x : ℝ) : ℤ :=
  ∑ r ∈ roots, if r ≤ x then 1 else 0

theorem past_locally (roots : Finset ℝ) (x : ℝ) :
    ∀ᶠ y in 𝓝 x, past roots y + (if x ∈ roots ∧ y < x then 1 else 0) = past roots x := by
  classical
  have stable : ∀ᶠ y in 𝓝 x, ∀ r ∈ roots, r ≠ x → (r ≤ y ↔ r ≤ x) := by
    rw [Filter.eventually_all_finset]
    intro r _
    by_cases hr : r = x
    · exact Filter.Eventually.of_forall (by simp [hr])
    · rcases lt_or_gt_of_ne hr with hr | hr
      · filter_upwards [eventually_gt_nhds hr] with y hy
        simp [hy.le, hr.le]
      · filter_upwards [eventually_lt_nhds hr] with y hy
        simp [hy.not_ge, hr.not_ge]
  filter_upwards [stable] with y hy
  have terms : ∀ r ∈ roots,
      (if r ≤ y then (1 : ℤ) else 0) + (if r = x ∧ y < x then 1 else 0) =
        if r ≤ x then 1 else 0 := by
    intro r hr
    by_cases eq : r = x
    · subst r
      by_cases hxy : y < x <;> simp [hxy, le_of_not_gt, not_le_of_gt]
    · simp [eq, hy r hr eq]
  have sum := Finset.sum_congr rfl terms
  simp only [Finset.sum_add_distrib] at sum
  have delta : (∑ r ∈ roots, if r = x ∧ y < x then (1 : ℤ) else 0) =
      if x ∈ roots ∧ y < x then 1 else 0 := by
    by_cases hxy : y < x <;> simp [hxy]
  simpa only [past, delta] using sum

theorem past_difference (roots : Finset ℝ) {a b : ℝ} (hab : a ≤ b) :
    past roots b - past roots a = ((roots.filter (fun r => a < r ∧ r ≤ b)).card : ℤ) := by
  classical
  unfold past
  rw [← Finset.sum_sub_distrib]
  have terms : ∀ r ∈ roots,
      (if r ≤ b then (1 : ℤ) else 0) - (if r ≤ a then 1 else 0) =
        if a < r ∧ r ≤ b then 1 else 0 := by
    intro r _
    by_cases hra : r ≤ a
    · simp [hra, hra.trans hab, not_lt.mpr hra]
    · by_cases hrb : r ≤ b <;> simp [hra, hrb, lt_of_not_ge hra]
  rw [Finset.sum_congr rfl terms]
  simp

/-- The global counting theorem, with explicit half-open endpoint ownership.
No ordering, connectedness of the accepted set, or simple-root assumption is
hidden: the chain conditions and first derivative force the counted roots to
be simple. Repeated roots must first use a checked root-set representative. -/
theorem count_roots_Ioc (p : Polynomial ℝ) (ps : List (ℝ → ℝ))
    (nonzero : p ≠ 0)
    (chain : Chain (p.eval :: p.derivative.eval :: ps))
    {a b : ℝ} (hab : a ≤ b) :
    variationAt (p.eval :: p.derivative.eval :: ps) a -
      variationAt (p.eval :: p.derivative.eval :: ps) b =
      (p.roots.toFinset.filter (fun r => a < r ∧ r ≤ b)).card := by
  classical
  let roots := p.roots.toFinset
  let vs := variationAt (p.eval :: p.derivative.eval :: ps)
  have membership : ∀ x, x ∈ roots ↔ p.eval x = 0 := by
    intro x
    simp only [roots, Multiset.mem_toFinset, Polynomial.mem_roots nonzero, Polynomial.IsRoot]
  have locally : IsLocallyConstant (fun x => (vs x : ℤ) + past roots x) := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases root : p.eval x = 0
    · have drop := root_drop chain (fun y => p.hasDerivAt y) root
      filter_upwards [drop, past_locally roots x] with y hv hr
      have present := (membership x).mpr root
      simp only [present, true_and] at hr
      change (vs y : ℤ) + past roots y = (vs x : ℤ) + past roots x
      change vs y = vs x + if y < x then 1 else 0 at hv
      rw [hv]
      push_cast
      split_ifs at * <;> linarith
    · have stable := locally_constant_of_head chain root
      filter_upwards [stable, past_locally roots x] with y hv hr
      have absent : x ∉ roots := by simpa only [membership] using root
      simp only [absent, false_and, ite_false, add_zero] at hr
      change (vs y : ℤ) + past roots y = (vs x : ℤ) + past roots x
      change vs y = vs x at hv
      rw [hv, hr]
  have equality := locally.apply_eq_of_preconnectedSpace a b
  have count := past_difference roots hab
  change (vs a : ℤ) + past roots a = (vs b : ℤ) + past roots b at equality
  change vs a - vs b = (roots.filter (fun r => a < r ∧ r ≤ b)).card
  omega

end ExactCIs.Unconditional.SturmRootCount
