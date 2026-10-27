/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.EffectCoordinate
import CarfSpine.IntervalHull

/-! # Finite beta-space hull bounds with an explicit distance from infinity

The old T1-min theorem requires a globally monotone real transport. The true
beta map has a pole; use a monotone clipped extension agreeing at every relevant
point, rather than silently discharging a false global premise.
-/
namespace ExactCIs.Unconditional.FiniteHull

open Set EffectCoordinate

noncomputable def clip (u x : ℝ) : ℝ := max 0 (min u x)
noncomputable def transport (u x : ℝ) : ℝ := beta (clip u x)

theorem clip_mem {u : ℝ} (nonnegative : 0 ≤ u) (x : ℝ) : clip u x ∈ Icc (0 : ℝ) u :=
  ⟨le_max_left _ _, max_le nonnegative (min_le_left _ _)⟩

theorem transport_eq {u x : ℝ} (inside : x ∈ Icc (0 : ℝ) u) : transport u x = beta x := by
  simp only [transport, clip, min_eq_right inside.2, max_eq_right inside.1]

theorem transport_monotone {u : ℝ} (inside : u ∈ Ico (0 : ℝ) 1) : Monotone (transport u) := by
  intro x y order
  apply beta_strictMonoOn.monotoneOn
    ⟨(clip_mem inside.1 x).1, (clip_mem inside.1 x).2.trans_lt inside.2⟩
    ⟨(clip_mem inside.1 y).1, (clip_mem inside.1 y).2.trans_lt inside.2⟩
  exact max_le_max le_rfl (min_le_min le_rfl order)

theorem extrema_mem {S : Set ℝ} {u : ℝ} (nonempty : S.Nonempty) (subset : S ⊆ Icc (0 : ℝ) u) :
    sInf S ∈ Icc (0 : ℝ) u ∧ sSup S ∈ Icc (0 : ℝ) u := by
  have member := nonempty
  obtain ⟨x, hx⟩ := member
  have below : BddBelow S := bddBelow_Icc.mono subset
  have above : BddAbove S := bddAbove_Icc.mono subset
  exact ⟨⟨le_csInf nonempty (fun _ hy => (subset hy).1),
      (csInf_le below hx).trans (subset hx).2⟩,
    ⟨(subset hx).1.trans (le_csSup above hx), csSup_le nonempty (fun _ hy => (subset hy).2)⟩⟩

/-- An actual beta-space fringe check bounds global hull excess. The outer
extent is strictly below compact infinity; disconnected components are allowed. -/
theorem t1min_finite {I A O : Set ℝ} {u epsilon : ℝ}
    (finite_extent : u ∈ Ico (0 : ℝ) 1) (outer_domain : O ⊆ Icc (0 : ℝ) u)
    (inner : I ⊆ A) (outer : A ⊆ O) (nonempty : I.Nonempty)
    (lower_fringe : beta (sInf I) - beta (sInf O) ≤ epsilon)
    (upper_fringe : beta (sSup O) - beta (sSup I) ≤ epsilon) :
    (∀ a ∈ A, beta (sInf O) ≤ beta a ∧ beta a ≤ beta (sSup O)) ∧
    (0 ≤ beta (sInf A) - beta (sInf O) ∧ beta (sInf A) - beta (sInf O) ≤ epsilon) ∧
    (0 ≤ beta (sSup O) - beta (sSup A) ∧ beta (sSup O) - beta (sSup A) ≤ epsilon) := by
  have i_extents := extrema_mem nonempty (inner.trans (outer.trans outer_domain))
  have a_extents := extrema_mem (nonempty.mono inner) (outer.trans outer_domain)
  have o_extents := extrema_mem (nonempty.mono (inner.trans outer)) outer_domain
  have lower : transport u (sInf I) - transport u (sInf O) ≤ epsilon := by
    simpa only [transport_eq i_extents.1, transport_eq o_extents.1] using lower_fringe
  have upper : transport u (sSup O) - transport u (sSup I) ≤ epsilon := by
    simpa only [transport_eq o_extents.2, transport_eq i_extents.2] using upper_fringe
  have result := Exactcis.Spine.t1min (transport_monotone finite_extent) outer inner nonempty
    (bddBelow_Icc.mono outer_domain) (bddAbove_Icc.mono outer_domain) lower upper
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    simpa only [transport_eq o_extents.1, transport_eq o_extents.2,
      transport_eq (outer_domain (outer ha))] using result.1 a ha
  · simpa only [transport_eq a_extents.1, transport_eq o_extents.1] using result.2.1
  · simpa only [transport_eq a_extents.2, transport_eq o_extents.2] using result.2.2

end ExactCIs.Unconditional.FiniteHull
