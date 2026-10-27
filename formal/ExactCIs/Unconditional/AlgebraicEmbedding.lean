/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootCountCertificate

/-! # Checked selection of one real embedding

A rational open isolator owns exactly one real root. Neither irreducibility
nor a global quotient-ring field structure is assumed.
-/
namespace ExactCIs.Unconditional.AlgebraicEmbedding

open RootCertificate

def check (d : Coefficients) (l u : ℚ) (c : RootCountCertificate.Certificate) : Bool :=
  decide (l < u) && decide (value d l ≠ 0) && decide (value d u ≠ 0) &&
    RootCountCertificate.check d c && decide (RootCountCertificate.count c l u = 1)

theorem check_sound {d : Coefficients} {l u : ℚ} {c : RootCountCertificate.Certificate}
    (checked : check d l u c = true) :
    ∃! x : ℝ, x ∈ Set.Ioo (l : ℝ) u ∧ eval d x = 0 := by
  have h : l < u ∧ value d l ≠ 0 ∧ value d u ≠ 0 ∧
      RootCountCertificate.check d c = true ∧ RootCountCertificate.count c l u = 1 := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  have count := RootCountCertificate.count_sound h.2.2.2.1 h.1.le
  rw [h.2.2.2.2] at count
  obtain ⟨x, single⟩ := Set.ncard_eq_one.mp count.symm
  have member : (l : ℝ) < x ∧ x ≤ (u : ℝ) ∧ eval d x = 0 := by
    have : x ∈ ({x} : Set ℝ) := Set.mem_singleton x
    rw [← single] at this
    exact this
  have upper : x < (u : ℝ) := by
    apply lt_of_le_of_ne member.2.1
    intro equality
    have hv : (value d u : ℝ) = 0 := by rw [value_coercion, ← equality, member.2.2]
    exact h.2.2.1 (Rat.cast_eq_zero.mp hv)
  refine ⟨x, ⟨⟨member.1, upper⟩, member.2.2⟩, ?_⟩
  rintro y ⟨hy, root⟩
  have mem : y ∈ {z : ℝ | (l : ℝ) < z ∧ z ≤ (u : ℝ) ∧ eval d z = 0} :=
    ⟨hy.1, hy.2.le, root⟩
  simpa only [single, Set.mem_singleton_iff] using mem

end ExactCIs.Unconditional.AlgebraicEmbedding
