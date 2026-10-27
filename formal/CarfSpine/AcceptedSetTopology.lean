import CarfSpine.InclusiveMaskTopology

/-!
# Accepted-set topology: closed directional sets, compact two-sided set

Spine module `AcceptedSetTopology` (devplan 22 §11, §1). With the u.s.c.
chain in place, the five blocking theorems of the devplan 22 §1 list are:

1. `inclusiveMaskProbability_upperSemicontinuous` (InclusiveMaskTopology)
2. `directionalPValue_upperSemicontinuous` (here — named composite)
3. `directionalAcceptedSet_isClosed` (here)
4. `twoSidedAcceptedSet_isCompact` (here)
5. `fixedMaskDirectionalPValue_continuous` (InclusiveMaskTopology)

Consequences the hull layer consumes: accept-at-tangency is structurally
natural (u.s.c. has upward jumps, not downward holes); rejected points form
an open set; `inf A`/`sup A` are attained whenever `A` is nonempty.
-/

namespace Exactcis.Spine

open Set

/-- L-H piece 5: the accepted set of an upper-semicontinuous p-value map is
closed. -/
theorem acceptedSet_isClosed_of_upperSemicontinuous {X : Type*}
    [TopologicalSpace X] {p : X → ℝ} (hp : UpperSemicontinuous p) (α : ℝ) :
    IsClosed {x | α ≤ p x} :=
  hp.isClosed_preimage α

/-- Blocking theorem 2 (named composite): the directional p-value
`x ↦ sup_{q ∈ [0,1]} Σ_o 1[(x,q) ∈ S_o]·m_o(x,q)` of the moving inclusive
mask is upper semicontinuous in the statistic. -/
theorem directionalPValue_upperSemicontinuous {X : Type*}
    [TopologicalSpace X] {mo : ℕ} (S : Fin mo → Set (X × ℝ))
    (hS : ∀ o, IsClosed (S o)) (mass : Fin mo → X × ℝ → ℝ)
    (hmass : ∀ o, Continuous (mass o)) (hmass0 : ∀ o p, 0 ≤ mass o p) :
    UpperSemicontinuous fun x : X => sSup
      ((fun q => ∑ o : Fin mo, (S o).indicator (mass o) (x, q)) ''
        Set.Icc (0 : ℝ) 1) :=
  usc_sSup_image_of_compact
    (f := fun x q => ∑ o : Fin mo, (S o).indicator (mass o) (x, q))
    (inclusiveMaskProbability_upperSemicontinuous S hS mass hmass hmass0)

/-- L-H composite: for the full model — closed per-outcome acceptance
regions in (statistic × nuisance) space, jointly continuous nonnegative
outcome masses, supremum over the compact nuisance interval — the
directional accepted set `{s | sup_q p(s,q) ≥ α}` is closed. -/
theorem directionalAcceptedSet_isClosed {X : Type*} [TopologicalSpace X]
    {mo : ℕ} (S : Fin mo → Set (X × ℝ)) (hS : ∀ o, IsClosed (S o))
    (mass : Fin mo → X × ℝ → ℝ) (hmass : ∀ o, Continuous (mass o))
    (hmass0 : ∀ o p, 0 ≤ mass o p) (α : ℝ) :
    IsClosed {x : X | α ≤ sSup
      ((fun q => ∑ o : Fin mo, (S o).indicator (mass o) (x, q)) ''
        Set.Icc (0 : ℝ) 1)} :=
  acceptedSet_isClosed_of_upperSemicontinuous
    (directionalPValue_upperSemicontinuous S hS mass hmass hmass0) α

/-- Blocking theorem 4: the two-sided accepted set — the intersection of
the two directional accepted sets with the compact effect domain `[0,1]` —
is compact. This is what attains `inf A` and `sup A` for the hull layer. -/
theorem twoSidedAcceptedSet_isCompact {p₁ p₂ : ℝ → ℝ}
    (h₁ : UpperSemicontinuous p₁) (h₂ : UpperSemicontinuous p₂)
    (α₁ α₂ : ℝ) :
    IsCompact
      (Set.Icc (0 : ℝ) 1 ∩ ({s | α₁ ≤ p₁ s} ∩ {s | α₂ ≤ p₂ s})) :=
  isCompact_Icc.of_isClosed_subset
    (isClosed_Icc.inter
      ((h₁.isClosed_preimage α₁).inter (h₂.isClosed_preimage α₂)))
    Set.inter_subset_left

end Exactcis.Spine
