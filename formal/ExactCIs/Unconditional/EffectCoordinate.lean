/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Table
import Mathlib

/-! # Exact compact coordinates for finite effects and tagged infinity

The inverse beta map is monotone only on its specified finite domain. No
finite real value, including a large sentinel, represents the infinity tag.
-/
namespace ExactCIs.Unconditional.EffectCoordinate

abbrev Compact := {s : ℝ // s ∈ Set.Icc (0 : ℝ) 1}

noncomputable def finiteCompact (x : ℝ) : ℝ := x / (1 + x)
noncomputable def beta (s : ℝ) : ℝ := s / (1 - s)

theorem finiteCompact_mem {x : ℝ} (nonnegative : 0 ≤ x) :
    finiteCompact x ∈ Set.Ico (0 : ℝ) 1 := by
  have positive : 0 < 1 + x := by linarith
  exact ⟨div_nonneg nonnegative positive.le, (div_lt_one positive).mpr (by linarith)⟩

theorem beta_finiteCompact {x : ℝ} (nonnegative : 0 ≤ x) : beta (finiteCompact x) = x := by
  have h : 1 + x ≠ 0 := ne_of_gt (by linarith : 0 < 1 + x)
  unfold beta finiteCompact
  field_simp
  ring

theorem beta_nonnegative {s : ℝ} (inside : s ∈ Set.Ico (0 : ℝ) 1) : 0 ≤ beta s :=
  div_nonneg inside.1 (sub_pos.mpr inside.2).le

theorem finiteCompact_beta {s : ℝ} (inside : s ∈ Set.Ico (0 : ℝ) 1) :
    finiteCompact (beta s) = s := by
  have hd : 1 - s ≠ 0 := (sub_pos.mpr inside.2).ne'
  have h : 1 + beta s ≠ 0 := ne_of_gt (by linarith [beta_nonnegative inside])
  unfold finiteCompact beta at *
  field_simp
  ring

theorem finiteCompact_strictMonoOn : StrictMonoOn finiteCompact (Set.Ici (0 : ℝ)) := by
  intro x hx y hy order
  have x_nonnegative : 0 ≤ x := hx
  have y_nonnegative : 0 ≤ y := hy
  change x / (1 + x) < y / (1 + y)
  rw [div_lt_div_iff₀ (by linarith : 0 < 1 + x) (by linarith : 0 < 1 + y)]
  nlinarith

theorem beta_strictMonoOn : StrictMonoOn beta (Set.Ico (0 : ℝ) 1) := by
  intro s hs t ht order
  change s / (1 - s) < t / (1 - t)
  rw [div_lt_div_iff₀ (sub_pos.mpr hs.2) (sub_pos.mpr ht.2)]
  nlinarith

noncomputable def compact (e : EffectState) : ℝ :=
  match e with
  | .finite x _ => finiteCompact x
  | .positiveInfinity => 1

theorem compact_mem (e : EffectState) : compact e ∈ Set.Icc (0 : ℝ) 1 := by
  cases e with
  | finite x hx => exact ⟨(finiteCompact_mem hx).1, (finiteCompact_mem hx).2.le⟩
  | positiveInfinity => exact ⟨zero_le_one, le_rfl⟩

noncomputable def effect (s : Compact) : EffectState :=
  if s.val = 1 then .positiveInfinity
  else .finite (beta s) (div_nonneg s.property.1 (sub_nonneg.mpr s.property.2))

theorem compact_effect (s : Compact) : compact (effect s) = (s : ℝ) := by
  unfold effect
  split
  · rename_i one
    exact one.symm
  · rename_i not_one
    exact finiteCompact_beta ⟨s.property.1, lt_of_le_of_ne s.property.2 not_one⟩

theorem effect_compact (e : EffectState) : effect ⟨compact e, compact_mem e⟩ = e := by
  cases e with
  | positiveInfinity => simp [effect, compact]
  | finite x hx =>
    have not_one : finiteCompact x ≠ 1 := (finiteCompact_mem hx).2.ne
    simp only [compact, effect, not_one, ite_false, beta_finiteCompact hx]

theorem compact_injective : Function.Injective compact := by
  intro a b equal
  have ha := effect_compact a
  have hb := effect_compact b
  have same : (⟨compact a, compact_mem a⟩ : Compact) = ⟨compact b, compact_mem b⟩ :=
    Subtype.ext equal
  rw [same] at ha
  exact ha.symm.trans hb

theorem finite_not_infinity (x : ℝ) (nonnegative : 0 ≤ x) :
    compact (.finite x nonnegative) < compact .positiveInfinity := (finiteCompact_mem nonnegative).2

theorem rational_beta (s : ℚ) : ((s / (1 - s) : ℚ) : ℝ) = beta (s : ℝ) := by
  simp only [Rat.cast_div, Rat.cast_sub, Rat.cast_one, beta]

theorem rational_compact (x : ℚ) : ((x / (1 + x) : ℚ) : ℝ) = finiteCompact (x : ℝ) := by
  simp only [Rat.cast_div, Rat.cast_add, Rat.cast_one, finiteCompact]

end ExactCIs.Unconditional.EffectCoordinate
