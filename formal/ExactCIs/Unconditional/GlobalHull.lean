/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.EffectOrder
import ExactCIs.Unconditional.FiniteHull
import ExactCIs.Unconditional.Structural

/-! # Concrete U0 T1 endpoint premises and extended hull guarantee

Sets have the compact effect subtype as carrier. Finite branches consume the
actual beta-space fringe checks. Structural branches return their exact tag;
no infinity-minus-infinity expression is formed. Components need not match.
-/
namespace ExactCIs.Unconditional.GlobalHull

open Set EffectCoordinate

noncomputable def realImage (S : Set Compact) : Set ℝ := Subtype.val '' S
noncomputable def lower (S : Set Compact) : ℝ := sInf (realImage S)
noncomputable def upper (S : Set Compact) : ℝ := sSup (realImage S)

theorem image_domain (S : Set Compact) : realImage S ⊆ Icc (0 : ℝ) 1 := by
  rintro _ ⟨s, _, rfl⟩
  exact s.property

theorem image_mono {S T : Set Compact} (subset : S ⊆ T) : realImage S ⊆ realImage T :=
  Set.image_mono subset

theorem extrema_domain (S : Set Compact) : lower S ∈ Icc (0 : ℝ) 1 ∧ upper S ∈ Icc (0 : ℝ) 1 := by
  by_cases nonempty : S.Nonempty
  · exact FiniteHull.extrema_mem (nonempty.image Subtype.val) (image_domain S)
  · have empty : S = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    simp [lower, upper, realImage, empty]

noncomputable def lowerCompact (S : Set Compact) : Compact := ⟨lower S, (extrema_domain S).1⟩
noncomputable def upperCompact (S : Set Compact) : Compact := ⟨upper S, (extrema_domain S).2⟩

noncomputable def hull (S : Set Compact) : Set EffectOrder.BetaEffect :=
  Icc (Structural.effectOrderIso (lowerCompact S)) (Structural.effectOrderIso (upperCompact S))

def endpoint : Structural.Endpoint → Compact
  | .zero => ⟨0, le_rfl, zero_le_one⟩
  | .infinity => ⟨1, zero_le_one, le_rfl⟩

inductive LowerBranch (I O : Set Compact) (epsilon : ℝ) where
  | finite (outer_positive : 0 < lower O) (inner_finite : lower I < 1)
      (fringe : beta (lower I) - beta (lower O) ≤ epsilon)
  | structural (e : Structural.Endpoint) (included : endpoint e ∈ I)
      (outer_exact : lower O = (endpoint e : ℝ)) (inner_exact : lower I = (endpoint e : ℝ))

inductive UpperBranch (I O : Set Compact) (epsilon : ℝ) where
  | finite (inner_positive : 0 < upper I) (outer_finite : upper O < 1)
      (fringe : beta (upper O) - beta (upper I) ≤ epsilon)
  | structural (e : Structural.Endpoint) (included : endpoint e ∈ I)
      (outer_exact : upper O = (endpoint e : ℝ)) (inner_exact : upper I = (endpoint e : ℝ))

/-- The five fields are the concrete U0 B.16.4 T1 endpoint contract. -/
structure T1EndpointPremises (A I O : Set Compact) (epsilon : ℝ) where
  epsilon_nonnegative : 0 ≤ epsilon
  inner_nonempty : I.Nonempty
  inner_outer : I ⊆ A ∧ A ⊆ O
  lower_branch : LowerBranch I O epsilon
  upper_branch : UpperBranch I O epsilon

inductive LowerGuarantee (A O : Set Compact) (epsilon : ℝ) : Prop where
  | finite (outer_positive : 0 < lower O) (ideal_finite : lower A < 1)
      (excess : 0 ≤ beta (lower A) - beta (lower O) ∧
        beta (lower A) - beta (lower O) ≤ epsilon)
  | structural (e : Structural.Endpoint) (included : endpoint e ∈ A)
      (outer_exact : lower O = (endpoint e : ℝ)) (ideal_exact : lower A = (endpoint e : ℝ))
      (zero_excess_bound : 0 ≤ epsilon)

inductive UpperGuarantee (A O : Set Compact) (epsilon : ℝ) : Prop where
  | finite (ideal_positive : 0 < upper A) (outer_finite : upper O < 1)
      (excess : 0 ≤ beta (upper O) - beta (upper A) ∧
        beta (upper O) - beta (upper A) ≤ epsilon)
  | structural (e : Structural.Endpoint) (included : endpoint e ∈ A)
      (outer_exact : upper O = (endpoint e : ℝ)) (ideal_exact : upper A = (endpoint e : ℝ))
      (zero_excess_bound : 0 ≤ epsilon)

structure HullGuarantee (A O : Set Compact) (epsilon : ℝ) : Prop where
  contains_ideal_hull : hull A ⊆ hull O
  lower : LowerGuarantee A O epsilon
  upper : UpperGuarantee A O epsilon

theorem extrema_order {A I O : Set Compact} (nonempty : I.Nonempty)
    (inner : I ⊆ A) (outer : A ⊆ O) :
    lower O ≤ lower A ∧ lower A ≤ lower I ∧ upper I ≤ upper A ∧ upper A ≤ upper O := by
  have inonempty := nonempty.image Subtype.val
  have anonempty := (nonempty.mono inner).image Subtype.val
  have abelow : BddBelow (realImage A) := bddBelow_Icc.mono (image_domain A)
  have obelow : BddBelow (realImage O) := bddBelow_Icc.mono (image_domain O)
  have aabove : BddAbove (realImage A) := bddAbove_Icc.mono (image_domain A)
  have oabove : BddAbove (realImage O) := bddAbove_Icc.mono (image_domain O)
  exact ⟨csInf_le_csInf obelow anonempty (image_mono outer),
    csInf_le_csInf abelow inonempty (image_mono inner),
    csSup_le_csSup aabove inonempty (image_mono inner),
    csSup_le_csSup oabove anonempty (image_mono outer)⟩

theorem t1MinHull {A I O : Set Compact} {epsilon : ℝ}
    (premises : T1EndpointPremises A I O epsilon) : HullGuarantee A O epsilon := by
  have ordered := extrema_order premises.inner_nonempty
    premises.inner_outer.1 premises.inner_outer.2
  have contains : hull A ⊆ hull O := by
    intro x hx
    have lo : Structural.effectOrderIso (lowerCompact O) ≤
        Structural.effectOrderIso (lowerCompact A) :=
      Structural.effectOrderIso.monotone ordered.1
    have hi : Structural.effectOrderIso (upperCompact A) ≤
        Structural.effectOrderIso (upperCompact O) :=
      Structural.effectOrderIso.monotone ordered.2.2.2
    exact ⟨lo.trans hx.1, hx.2.trans hi⟩
  refine ⟨contains, ?_, ?_⟩
  · cases premises.lower_branch with
    | finite positive finite fringe =>
      have finite_a : lower A < 1 := ordered.2.1.trans_lt finite
      have finite_o : lower O < 1 := ordered.1.trans_lt finite_a
      have first : beta (lower O) ≤ beta (lower A) := beta_strictMonoOn.monotoneOn
        ⟨(extrema_domain O).1.1, finite_o⟩ ⟨(extrema_domain A).1.1, finite_a⟩ ordered.1
      have second : beta (lower A) ≤ beta (lower I) := beta_strictMonoOn.monotoneOn
        ⟨(extrema_domain A).1.1, finite_a⟩ ⟨(extrema_domain I).1.1, finite⟩ ordered.2.1
      exact LowerGuarantee.finite positive finite_a ⟨by linarith, by linarith⟩
    | structural e included outer_exact inner_exact =>
      have ideal_exact : lower A = (endpoint e : ℝ) := le_antisymm
        (by rw [← inner_exact]; exact ordered.2.1)
        (by rw [← outer_exact]; exact ordered.1)
      exact LowerGuarantee.structural e (premises.inner_outer.1 included)
        outer_exact ideal_exact premises.epsilon_nonnegative
  · cases premises.upper_branch with
    | finite positive finite fringe =>
      have positive_a : 0 < upper A := positive.trans_le ordered.2.2.1
      have finite_a : upper A < 1 := ordered.2.2.2.trans_lt finite
      have finite_i : upper I < 1 := ordered.2.2.1.trans_lt finite_a
      have first : beta (upper I) ≤ beta (upper A) := beta_strictMonoOn.monotoneOn
        ⟨(extrema_domain I).2.1, finite_i⟩ ⟨(extrema_domain A).2.1, finite_a⟩ ordered.2.2.1
      have second : beta (upper A) ≤ beta (upper O) := beta_strictMonoOn.monotoneOn
        ⟨(extrema_domain A).2.1, finite_a⟩ ⟨(extrema_domain O).2.1, finite⟩ ordered.2.2.2
      exact UpperGuarantee.finite positive_a finite ⟨by linarith, by linarith⟩
    | structural e included outer_exact inner_exact =>
      have ideal_exact : upper A = (endpoint e : ℝ) := le_antisymm
        (by rw [← outer_exact]; exact ordered.2.2.2)
        (by rw [← inner_exact]; exact ordered.2.2.1)
      exact UpperGuarantee.structural e (premises.inner_outer.1 included)
        outer_exact ideal_exact premises.epsilon_nonnegative

theorem premises_nonempty {A I O : Set Compact} {epsilon : ℝ}
    (premises : T1EndpointPremises A I O epsilon) : A.Nonempty :=
  premises.inner_nonempty.mono premises.inner_outer.1

theorem empty_has_no_premises (I O : Set Compact) (epsilon : ℝ) :
    ¬ Nonempty (T1EndpointPremises ∅ I O epsilon) := by
  rintro ⟨premises⟩
  exact Set.not_nonempty_empty (premises_nonempty premises)

theorem full_inner_forces_full {A I O : Set Compact} {epsilon : ℝ}
    (premises : T1EndpointPremises A I O epsilon) (full : I = univ) : A = univ := by
  exact Set.eq_univ_of_univ_subset (full ▸ premises.inner_outer.1)

theorem full_extrema : lower (univ : Set Compact) = 0 ∧ upper (univ : Set Compact) = 1 := by
  have image : realImage (univ : Set Compact) = Icc (0 : ℝ) 1 := by
    ext x
    constructor
    · intro hx
      exact image_domain univ hx
    · intro hx
      exact ⟨⟨x, hx⟩, Set.mem_univ _, rfl⟩
  simp only [lower, upper, image, csInf_Icc zero_le_one, csSup_Icc zero_le_one, and_self]

end ExactCIs.Unconditional.GlobalHull
