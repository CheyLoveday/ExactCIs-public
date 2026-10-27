/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.StructuralLimits

/-! # Leading powers of the actual finite-effect Fisher tails

Greater tails are expanded at zero. Less tails are expanded in reciprocal
effect at infinity. Positive continuous leading factors distinguish different
orders and give one neighbourhood for all outcomes of the finite sample space.
-/
namespace ExactCIs.Unconditional.EndpointOrdering

open ProductBinomial BoschlooOrdering FNCH Filter Topology

noncomputable def coeff (n1 n0 m k : ℕ) : ℝ :=
  (n1.choose k : ℝ) * n0.choose (m - k)

def exponent (direction : Direction) (n1 k : ℕ) : ℕ :=
  match direction with | .greater => k | .less => n1 - k

def edge (direction : Direction) (n1 n0 m : ℕ) : ℕ :=
  match direction with | .greater => m - n0 | .less => min n1 m

def order {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0) : ℕ :=
  match direction with
  | .greater => min o.1.val (n0 - o.2.val)
  | .less => min o.2.val (n1 - o.1.val)

noncomputable def reduced (direction : Direction) (n1 n0 m shift : ℕ)
    (event : Finset ℕ) (t : ℝ) : ℝ :=
  ∑ k ∈ event, coeff n1 n0 m k * t ^ (exponent direction n1 k - shift)

noncomputable def factor {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0) (t : ℝ) : ℝ :=
  reduced direction n1 n0 (o.1.val + o.2.val) (exponent direction n1 o.1.val)
    (tailSet n1 n0 (o.1.val + o.2.val) o.1.val direction) t /
  reduced direction n1 n0 (o.1.val + o.2.val)
    (exponent direction n1 (edge direction n1 n0 (o.1.val + o.2.val)))
    (Support.valid n1 n0 (o.1.val + o.2.val)) t

theorem coeff_pos {n1 n0 m k : ℕ} (hk : k ∈ Support.valid n1 n0 m) :
    0 < coeff n1 n0 m k := by
  have h := Support.mem_valid_iff.mp hk
  unfold coeff
  exact mul_pos (by exact_mod_cast Nat.choose_pos h.1)
    (by exact_mod_cast Nat.choose_pos (by omega : m - k ≤ n0))

theorem edge_supported {n1 n0 m : ℕ} (hm : m ≤ n1 + n0) (direction : Direction) :
    edge direction n1 n0 m ∈ Support.valid n1 n0 m := by
  rw [Support.mem_valid_iff]
  cases direction <;> simp only [edge] <;> omega

theorem edge_le {n1 n0 m k : ℕ} (hk : k ∈ Support.valid n1 n0 m) (direction : Direction) :
    exponent direction n1 (edge direction n1 n0 m) ≤ exponent direction n1 k := by
  have h := Support.mem_valid_iff.mp hk
  cases direction <;> simp only [edge, exponent] <;> omega

theorem start_le {n1 n0 m x k : ℕ} {direction : Direction}
    (hk : k ∈ tailSet n1 n0 m x direction) :
    exponent direction n1 x ≤ exponent direction n1 k := by
  cases direction <;> simp only [tailSet, Finset.mem_filter, exponent] at hk ⊢ <;> omega

theorem order_eq {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0) :
    order direction o = exponent direction n1 o.1.val -
      exponent direction n1 (edge direction n1 n0 (o.1.val + o.2.val)) := by
  have := o.1.isLt; have := o.2.isLt
  cases direction <;> simp only [order, exponent, edge] <;> omega

theorem reduced_pos_zero {n1 n0 m shift k : ℕ} {event : Finset ℕ}
    (direction : Direction) (subset : event ⊆ Support.valid n1 n0 m)
    (member : k ∈ event) (zero : exponent direction n1 k = shift) :
    0 < reduced direction n1 n0 m shift event 0 := by
  apply Finset.sum_pos'
  · intro j hj
    exact mul_nonneg (coeff_pos (subset hj)).le (pow_nonneg (by norm_num) _)
  · refine ⟨k, member, ?_⟩
    simpa [zero] using coeff_pos (subset member)

theorem factor_positive {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0) :
    0 < factor direction o 0 := by
  have self : o.1.val ∈ tailSet n1 n0 (o.1.val + o.2.val) o.1.val direction := by
    cases direction <;> simp [tailSet, outcome_supported o]
  exact div_pos
    (reduced_pos_zero direction (tailSet_subset _ _ _ _ _) self rfl)
    (reduced_pos_zero direction (fun _ h => h)
      (edge_supported (outcome_margin o) direction) rfl)

theorem factor_continuous {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0) :
    ContinuousAt (factor direction o) 0 := by
  unfold factor
  apply ContinuousAt.div
  · unfold reduced; fun_prop
  · unfold reduced; fun_prop
  · exact (reduced_pos_zero direction (fun _ h => h)
      (edge_supported (outcome_margin o) direction) rfl).ne'

theorem sum_factor (direction : Direction) (n1 n0 m shift : ℕ) (event : Finset ℕ)
    (bound : ∀ k ∈ event, shift ≤ exponent direction n1 k) (t : ℝ) :
    (∑ k ∈ event, coeff n1 n0 m k * t ^ exponent direction n1 k) =
      t ^ shift * reduced direction n1 n0 m shift event t := by
  rw [reduced, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [← mul_assoc, mul_comm (t ^ shift), mul_assoc, ← pow_add,
    Nat.add_sub_of_le (bound k hk)]

theorem ratio_factor {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0)
    {t : ℝ} (positive : 0 < t) :
    (∑ k ∈ tailSet n1 n0 (o.1.val + o.2.val) o.1.val direction,
      coeff n1 n0 (o.1.val + o.2.val) k * t ^ exponent direction n1 k) /
    (∑ k ∈ Support.valid n1 n0 (o.1.val + o.2.val),
      coeff n1 n0 (o.1.val + o.2.val) k * t ^ exponent direction n1 k) =
      t ^ order direction o * factor direction o t := by
  rw [sum_factor direction _ _ _ (exponent direction n1 o.1.val) _
    (fun _ h => start_le h), sum_factor direction _ _ _
    (exponent direction n1 (edge direction n1 n0 (o.1.val + o.2.val))) _
    (fun _ h => edge_le h direction)]
  rw [order_eq]
  have bound := edge_le (outcome_supported o) direction
  rw [← Nat.sub_add_cancel bound, pow_add]
  unfold factor
  field_simp
  simp only [Nat.sub_add_cancel bound]

/-- Reciprocal-effect conversion keeps the common positive power intact. -/
theorem reverse_term {n1 n0 m k : ℕ} (hk : k ≤ n1) {psi : ℝ} (positive : 0 < psi) :
    coeff n1 n0 m k * psi ^ k =
      psi ^ n1 * (coeff n1 n0 m k * (psi⁻¹) ^ (n1 - k)) := by
  rw [inv_pow, ← Nat.sub_add_cancel hk, pow_add]
  field_simp
  simp only [Nat.add_sub_cancel]

theorem statistic_factor {n1 n0 : ℕ} (direction : Direction) (o : Outcome n1 n0)
    {psi : ℝ} (positive : 0 < psi) :
    statistic direction psi o =
      (if direction = .greater then psi else psi⁻¹) ^ order direction o *
        factor direction o (if direction = .greater then psi else psi⁻¹) := by
  cases direction with
  | greater =>
    simpa [statistic, tail, numerator, normalizer, Recurrence.unnormalizedWeight,
      coeff, exponent] using ratio_factor .greater o positive
  | less =>
    have sum_reverse : ∀ event : Finset ℕ,
        event ⊆ Support.valid n1 n0 (o.1.val + o.2.val) →
        (∑ k ∈ event, coeff n1 n0 (o.1.val + o.2.val) k * psi ^ k) =
        psi ^ n1 * ∑ k ∈ event,
          coeff n1 n0 (o.1.val + o.2.val) k * (psi⁻¹) ^ (n1 - k) := by
      intro event subset
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      exact reverse_term (Support.mem_valid_iff.mp (subset hk)).1 positive
    unfold statistic tail numerator normalizer Recurrence.unnormalizedWeight
    change (∑ k ∈ _, coeff n1 n0 _ k * psi ^ k) /
      (∑ k ∈ _, coeff n1 n0 _ k * psi ^ k) = _
    rw [sum_reverse _ (tailSet_subset _ _ _ _ _), sum_reverse _ (fun _ h => h),
      mul_div_mul_left _ _ (pow_ne_zero _ positive.ne')]
    simpa [exponent] using ratio_factor .less o (inv_pos.mpr positive)

/-- Distinct leading orders force the correct strict comparison near zero in
this coordinate. Equality orders need not be resolved by this lemma. -/
theorem eventually_ordered {n1 n0 : ℕ} (direction : Direction)
    (candidate observed : Outcome n1 n0)
    (lower : order direction candidate < order direction observed) :
    ∀ᶠ t in 𝓝 (0 : ℝ), 0 < t →
      t ^ order direction observed * factor direction observed t <
        t ^ order direction candidate * factor direction candidate t := by
  have continuous : ContinuousAt (fun t => factor direction candidate t -
      t ^ (order direction observed - order direction candidate) * factor direction observed t) 0 :=
    (factor_continuous direction candidate).sub
      ((continuousAt_id.pow _).mul (factor_continuous direction observed))
  have at_zero : 0 < factor direction candidate 0 -
      (0 : ℝ) ^ (order direction observed - order direction candidate) *
        factor direction observed 0 := by
    simpa [Nat.sub_ne_zero_of_lt lower] using factor_positive direction candidate
  filter_upwards [continuous.eventually (lt_mem_nhds at_zero)] with t ht positive
  have power := pow_pos positive (order direction candidate)
  have exp : order direction observed = order direction candidate +
      (order direction observed - order direction candidate) := by omega
  rw [exp, pow_add]
  nlinarith

/-- One common reciprocal/ordinary coordinate neighbourhood covers every
candidate, not a separately chosen effect for each comparison. -/
theorem eventual_stratum {n1 n0 : ℕ} (direction : Direction) (observed : Outcome n1 n0) :
    ∃ delta : ℝ, 0 < delta ∧ delta ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ delta →
      ∀ candidate : Outcome n1 n0,
        t ^ order direction candidate * factor direction candidate t ≤
          t ^ order direction observed * factor direction observed t →
        order direction observed ≤ order direction candidate := by
  have all : ∀ᶠ t in 𝓝 (0 : ℝ), ∀ candidate : Outcome n1 n0,
      order direction candidate < order direction observed → 0 < t →
      t ^ order direction observed * factor direction observed t <
        t ^ order direction candidate * factor direction candidate t := by
    rw [Filter.eventually_all]
    intro candidate
    by_cases h : order direction candidate < order direction observed
    · filter_upwards [eventually_ordered direction candidate observed h] with t ht
      exact fun _ => ht
    · exact Filter.Eventually.of_forall (by simp [h])
  obtain ⟨epsilon, ep, ball⟩ := Metric.eventually_nhds_iff.mp all
  refine ⟨min 1 (epsilon / 2), lt_min zero_lt_one (by positivity), min_le_left _ _, ?_⟩
  intro t positive small candidate selected
  have distance : dist t 0 < epsilon := by
    rw [Real.dist_eq, sub_zero, abs_of_pos positive]
    have := small.trans (min_le_right (1 : ℝ) (epsilon / 2))
    linarith
  by_contra wrong
  exact (not_lt_of_ge selected) (ball distance candidate (lt_of_not_ge wrong) positive)

end ExactCIs.Unconditional.EndpointOrdering
