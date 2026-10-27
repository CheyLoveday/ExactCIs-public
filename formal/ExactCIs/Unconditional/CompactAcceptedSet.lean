/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooTopology
import ExactCIs.Unconditional.EffectCoordinate
import ExactCIs.Unconditional.EndpointLimits
import ExactCIs.Unconditional.CompleteDomainCoverage

/-! # Closedness of actual acceptance on the complete compact effect domain

Interior closedness uses actual inclusive-mask semicontinuity. Structural
rejection neighborhoods use the nuisance-uniform endpoint bounds, not a
continuous probability link at the two singular compact-square corners.
-/
namespace ExactCIs.Unconditional.CompactAcceptedSet

open Set EffectCoordinate ProductBinomial

attribute [local instance] Classical.propDecidable

def accepted {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) : Set ℝ :=
  {s | s ∈ Icc (0 : ℝ) 1 ∧
    if s = 0 then Structural.Accepted .zero r observed
    else if s = 1 then Structural.Accepted .infinity r observed
    else BoschlooValidity.Accepted (beta s) r observed}

theorem local_closed {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ)
    {a b : ℝ} (lower : 0 < a) (upper : b < 1) :
    IsClosed (accepted observed r ∩ Icc a b) := by
  let f (s : ↥(Icc a b)) : BoschlooTopology.Positive :=
    ⟨beta s, div_pos (lower.trans_le s.property.1) (sub_pos.mpr (s.property.2.trans_lt upper))⟩
  have continuous : Continuous f := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.div (continuous_const.sub continuous_subtype_val)
      (fun s => (sub_pos.mpr (s.property.2.trans_lt upper)).ne')
  have closed : IsClosed {s : ↥(Icc a b) | BoschlooValidity.Accepted (beta s) r observed} :=
    (BoschlooTopology.accepted_closed_positive observed r).preimage continuous
  have compact := closed.isCompact.image continuous_subtype_val
  have equal : Subtype.val '' {s : ↥(Icc a b) | BoschlooValidity.Accepted (beta s) r observed} =
      accepted observed r ∩ Icc a b := by
    ext s
    constructor
    · rintro ⟨t, ht, rfl⟩
      have positive : 0 < (t : ℝ) := lower.trans_le t.property.1
      have below : (t : ℝ) < 1 := t.property.2.trans_lt upper
      exact ⟨⟨⟨positive.le, below.le⟩, by
        simpa only [Set.mem_ofPred_eq, if_neg positive.ne', if_neg below.ne] using ht⟩,
        t.property⟩
    · rintro ⟨hs, inside⟩
      have positive : 0 < s := lower.trans_le inside.1
      have below : s < 1 := inside.2.trans_lt upper
      exact ⟨⟨s, inside⟩, by
        simpa only [Set.mem_ofPred_eq, if_neg positive.ne', if_neg below.ne] using hs.2, rfl⟩
  rw [equal] at compact
  exact compact.isClosed

theorem zero_mem {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) :
    0 ∈ accepted observed r ↔ Structural.Accepted .zero r observed := by simp [accepted]

theorem one_mem {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) :
    1 ∈ accepted observed r ↔ Structural.Accepted .infinity r observed := by simp [accepted]

theorem zero_not_closure_of_rejected {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (rejected : ¬ Structural.Accepted .zero r observed) :
    0 ∉ closure (accepted observed r) := by
  have positive : 0 < r := by
    by_contra h
    have zero : r = 0 := le_antisymm (le_of_not_gt h) level.1
    exact rejected (zero ▸ Structural.zero_level_accepted .zero observed)
  have unsupported : ¬ Structural.Supported .zero observed := by
    intro supported
    apply rejected
    simpa [Structural.Accepted, Structural.pair, supported] using And.intro level.2 level.2
  obtain ⟨delta, delta_positive, exclude⟩ :=
    EndpointLimits.zero_excludes_neighbourhood observed unsupported positive
  have cut : finiteCompact delta ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos delta_positive (by linarith), (finiteCompact_mem delta_positive.le).2⟩
  intro member
  obtain ⟨s, hs, accepted_s⟩ := mem_closure_iff.mp member
    (Iio (finiteCompact delta)) isOpen_Iio cut.1
  have domain := accepted_s.1
  by_cases zero : s = 0
  · exact rejected ((zero_mem observed r).mp (zero ▸ accepted_s))
  have interior : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨lt_of_le_of_ne domain.1 (Ne.symm zero), hs.trans cut.2⟩
  have bound : beta s ≤ delta := by
    rw [← beta_finiteCompact delta_positive.le]
    exact beta_strictMonoOn.monotoneOn ⟨interior.1.le, interior.2⟩ ⟨cut.1.le, cut.2⟩ hs.le
  have actual : BoschlooValidity.Accepted (beta s) r observed := by
    simpa only [if_neg zero, if_neg interior.2.ne] using accepted_s.2
  exact exclude (beta s) (div_pos interior.1 (sub_pos.mpr interior.2)) bound actual

theorem one_not_closure_of_rejected {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (rejected : ¬ Structural.Accepted .infinity r observed) :
    1 ∉ closure (accepted observed r) := by
  have positive : 0 < r := by
    by_contra h
    have zero : r = 0 := le_antisymm (le_of_not_gt h) level.1
    exact rejected (zero ▸ Structural.zero_level_accepted .infinity observed)
  have unsupported : ¬ Structural.Supported .infinity observed := by
    intro supported
    apply rejected
    simpa [Structural.Accepted, Structural.pair, supported] using And.intro level.2 level.2
  obtain ⟨M, large, exclude⟩ :=
    EndpointLimits.infinity_excludes_neighbourhood observed unsupported positive
  have M_positive : 0 < M := zero_lt_one.trans large
  have cut : finiteCompact M ∈ Ioo (0 : ℝ) 1 :=
    ⟨div_pos M_positive (by linarith), (finiteCompact_mem M_positive.le).2⟩
  intro member
  obtain ⟨s, hs, accepted_s⟩ := mem_closure_iff.mp member
    (Ioi (finiteCompact M)) isOpen_Ioi cut.2
  have domain := accepted_s.1
  by_cases one : s = 1
  · exact rejected ((one_mem observed r).mp (one ▸ accepted_s))
  have interior : s ∈ Ioo (0 : ℝ) 1 :=
    ⟨cut.1.trans hs, lt_of_le_of_ne domain.2 one⟩
  have bound : M ≤ beta s := by
    rw [← beta_finiteCompact M_positive.le]
    exact beta_strictMonoOn.monotoneOn ⟨cut.1.le, cut.2⟩ ⟨interior.1.le, interior.2⟩ hs.le
  have actual : BoschlooValidity.Accepted (beta s) r observed := by
    simpa only [if_neg interior.1.ne', if_neg one] using accepted_s.2
  exact exclude (beta s) bound actual

theorem accepted_closed {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) : IsClosed (accepted observed r) := by
  apply isClosed_of_closure_subset
  intro x member
  have domain : x ∈ Icc (0 : ℝ) 1 :=
    closure_minimal (fun _ hx => hx.1) isClosed_Icc member
  by_cases zero : x = 0
  · subst x
    apply (zero_mem observed r).mpr
    by_contra rejected
    exact zero_not_closure_of_rejected observed level rejected member
  by_cases one : x = 1
  · subst x
    apply (one_mem observed r).mpr
    by_contra rejected
    exact one_not_closure_of_rejected observed level rejected member
  have positive : 0 < x := lt_of_le_of_ne domain.1 (Ne.symm zero)
  have below : x < 1 := lt_of_le_of_ne domain.2 one
  have lower : 0 < x / 2 := by linarith
  have upper : (x + 1) / 2 < 1 := by linarith
  have center : x ∈ Ioo (x / 2) ((x + 1) / 2) := ⟨by linarith, by linarith⟩
  have near := isOpen_Ioo.inter_closure ⟨center, member⟩
  have subset : Ioo (x / 2) ((x + 1) / 2) ∩ accepted observed r ⊆
      accepted observed r ∩ Icc (x / 2) ((x + 1) / 2) :=
    fun _ hy => ⟨hy.2, ⟨hy.1.1.le, hy.1.2.le⟩⟩
  have closed := local_closed observed r lower upper
  exact (closed.closure_eq ▸ closure_mono subset near).1

theorem accepted_compact {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) : IsCompact (accepted observed r) :=
  isCompact_Icc.of_isClosed_subset (accepted_closed observed level) (fun _ hx => hx.1)

/-- The compact definition is exactly the existing extended-domain acceptance
predicate, including the two direct structural tags. -/
theorem effect_agreement {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) (s : Compact) :
    (s : ℝ) ∈ accepted observed r ↔ CompleteDomainCoverage.Accepted (effect s) r observed := by
  by_cases zero : (s : ℝ) = 0
  · simp [accepted, CompleteDomainCoverage.Accepted, effect, zero, beta]
  by_cases one : (s : ℝ) = 1
  · simp [accepted, CompleteDomainCoverage.Accepted, effect, one]
  have positive : 0 < beta (s : ℝ) :=
    div_pos (lt_of_le_of_ne s.property.1 (Ne.symm zero))
      (sub_pos.mpr (lt_of_le_of_ne s.property.2 one))
  have lower : 0 ≤ (s : ℝ) := s.property.1
  have upper : (s : ℝ) ≤ 1 := s.property.2
  simp [accepted, CompleteDomainCoverage.Accepted, effect, zero, one, positive.ne', lower, upper]

theorem extrema_accepted {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (nonempty : (accepted observed r).Nonempty) :
    sInf (accepted observed r) ∈ accepted observed r ∧
      sSup (accepted observed r) ∈ accepted observed r :=
  ⟨(accepted_compact observed level).sInf_mem nonempty,
    (accepted_compact observed level).sSup_mem nonempty⟩

theorem lower_zero_iff {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (nonempty : (accepted observed r).Nonempty) :
    sInf (accepted observed r) = 0 ↔ Structural.Accepted .zero r observed := by
  constructor
  · intro zero
    apply (zero_mem observed r).mp
    simpa only [zero] using (extrema_accepted observed level nonempty).1
  · intro included
    apply le_antisymm
    · exact csInf_le (accepted_compact observed level).bddBelow ((zero_mem observed r).mpr included)
    · exact le_csInf nonempty (fun _ hx => hx.1.1)

theorem upper_one_iff {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (nonempty : (accepted observed r).Nonempty) :
    sSup (accepted observed r) = 1 ↔ Structural.Accepted .infinity r observed := by
  constructor
  · intro one
    apply (one_mem observed r).mp
    simpa only [one] using (extrema_accepted observed level nonempty).2
  · intro included
    apply le_antisymm
    · exact csSup_le nonempty (fun _ hx => hx.1.2)
    · exact le_csSup (accepted_compact observed level).bddAbove ((one_mem observed r).mpr included)

theorem finite_upper_of_infinity_rejected {n1 n0 : ℕ} (observed : Outcome n1 n0) {r : ℝ}
    (level : r ∈ Icc (0 : ℝ) 1) (nonempty : (accepted observed r).Nonempty)
    (rejected : ¬ Structural.Accepted .infinity r observed) :
    sSup (accepted observed r) < 1 := by
  apply lt_of_le_of_ne (extrema_accepted observed level nonempty).2.1.2
  intro one
  exact rejected ((upper_one_iff observed level nonempty).mp one)

end ExactCIs.Unconditional.CompactAcceptedSet
