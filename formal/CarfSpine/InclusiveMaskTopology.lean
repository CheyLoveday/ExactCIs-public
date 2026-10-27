import Mathlib.Topology.Semicontinuity.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.FunProp

/-!
# Inclusive-mask topology: the upper-semicontinuity chain

Spine module `InclusiveMaskTopology` (devplan 22 §11, §1): the moving
inclusive-mask probability is upper semicontinuous, and the supremum over
the compact nuisance interval preserves upper semicontinuity.

Chain: indicator of a closed set with continuous nonnegative mass is u.s.c.
(mathlib only has the constant-value version, so the variable-value version
is proved here); a finite sum of u.s.c. terms is u.s.c.
(`upperSemicontinuous_sum`, mathlib); the sup over the compact nuisance
interval of a jointly u.s.c. function is u.s.c. in the statistic (missing
from mathlib — proved here via
`IsCompact.eventually_forall_of_forall_eventually`).

Also here: `fixedMaskDirectionalPValue_continuous` — on a mask-stable
stratum the objective is *jointly continuous* (no indicator jumps), and
then the directional p-value `x ↦ sup_q f x q` is fully continuous, not
merely u.s.c. This is the fifth blocking theorem of the devplan 22 §1
list; the lower-semicontinuous half is proved directly from attainment and
the order topology, the upper half is `usc_sSup_image_of_compact`.
-/

namespace Exactcis.Spine

open Set Filter Topology

/-- L-H piece 1+2: the indicator of a closed set with a *continuous
nonnegative* value function is upper semicontinuous. Mathlib's
`IsClosed.upperSemicontinuous_indicator` covers constant values only. -/
theorem upperSemicontinuous_indicator_of_continuous {X : Type*}
    [TopologicalSpace X] {S : Set X} (hS : IsClosed S) {c : X → ℝ}
    (hc : Continuous c) (hc0 : ∀ x, 0 ≤ c x) :
    UpperSemicontinuous (S.indicator c) := by
  intro x y hy
  have hind_le : ∀ z, S.indicator c z ≤ c z := fun z => by
    by_cases hz : z ∈ S
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]; exact hc0 z
  by_cases hx : x ∈ S
  · rw [Set.indicator_of_mem hx] at hy
    filter_upwards [(hc.tendsto x).eventually_lt_const hy] with z hz
    exact lt_of_le_of_lt (hind_le z) hz
  · rw [Set.indicator_of_notMem hx] at hy
    filter_upwards [hS.isOpen_compl.mem_nhds hx] with z hz
    rw [Set.indicator_of_notMem hz]
    exact hy

/-- L-H piece 3: the inclusive-mask probability — a finite sum over outcomes
of (closed acceptance region indicator) × (continuous nonnegative mass) —
is upper semicontinuous in the statistic/nuisance argument. -/
theorem inclusiveMaskProbability_upperSemicontinuous {X : Type*}
    [TopologicalSpace X] {mo : ℕ} (S : Fin mo → Set X)
    (hS : ∀ o, IsClosed (S o)) (mass : Fin mo → X → ℝ)
    (hmass : ∀ o, Continuous (mass o)) (hmass0 : ∀ o x, 0 ≤ mass o x) :
    UpperSemicontinuous (fun x => ∑ o : Fin mo, (S o).indicator (mass o) x) :=
  upperSemicontinuous_sum fun o _ =>
    upperSemicontinuous_indicator_of_continuous (hS o) (hmass o) (hmass0 o)

/-- L-H piece 4 (the lemma missing from mathlib): the pointwise supremum
over the compact nuisance interval `[0,1]` of a *jointly* upper
semicontinuous function is upper semicontinuous in the statistic. -/
theorem usc_sSup_image_of_compact {X : Type*} [TopologicalSpace X]
    (f : X → ℝ → ℝ)
    (hf : UpperSemicontinuous fun p : X × ℝ => f p.1 p.2) :
    UpperSemicontinuous fun x => sSup (f x '' Set.Icc (0 : ℝ) 1) := by
  intro x y hy
  obtain ⟨y', hy₁, hy₂⟩ := exists_between hy
  -- every slice value sits under the slice sup, which is < y'
  have hslice : ∀ q ∈ Set.Icc (0 : ℝ) 1, f x q < y' := by
    intro q hq
    have husc : UpperSemicontinuous fun q' : ℝ => f x q' := by
      intro q y' hqy
      have hcont : Continuous fun q' : ℝ => ((x, q') : X × ℝ) := by fun_prop
      exact (hcont.tendsto q).eventually (hf (x, q) y' hqy)
    have hbdd : BddAbove (f x '' Set.Icc (0 : ℝ) 1) :=
      (husc.upperSemicontinuousOn _).bddAbove_of_isCompact isCompact_Icc
    exact lt_of_le_of_lt (le_csSup hbdd ⟨q, hq, rfl⟩) hy₁
  have hev : ∀ q ∈ Set.Icc (0 : ℝ) 1,
      ∀ᶠ p : X × ℝ in nhds (x, q), f p.1 p.2 < y' :=
    fun q hq => hf (x, q) y' (hslice q hq)
  filter_upwards
    [isCompact_Icc.eventually_forall_of_forall_eventually
      (P := fun z w => f z w < y') hev] with z hz
  have hle : sSup (f z '' Set.Icc (0 : ℝ) 1) ≤ y' := by
    refine csSup_le ((Set.nonempty_Icc.mpr zero_le_one).image _) ?_
    rintro _ ⟨q, hq, rfl⟩
    exact (hz q hq).le
  exact lt_of_le_of_lt hle hy₂

/-! ## Fixed-mask continuity (the fifth §1 blocking theorem) -/

/-- On a mask-stable stratum the objective is jointly continuous and the
directional p-value `x ↦ sup_{q ∈ [0,1]} f x q` is **continuous** — the
u.s.c. half is `usc_sSup_image_of_compact` (continuity implies joint
u.s.c.), and the l.s.c. half follows from attainment under the order
topology. This is `fixedMaskDirectionalPValue_continuous` from the
devplan 22 §1 blocking list. -/
theorem fixedMaskDirectionalPValue_continuous {X : Type*}
    [TopologicalSpace X] (f : X → ℝ → ℝ)
    (hf : Continuous fun p : X × ℝ => f p.1 p.2) :
    Continuous fun x => sSup (f x '' Set.Icc (0 : ℝ) 1) := by
  rw [continuous_iff_continuousAt]
  intro x
  rw [ContinuousAt, tendsto_order]
  constructor
  · -- l.s.c. side: y < sup at x ⇒ eventually y < sup at z
    intro y hy
    have hne : (f x '' Set.Icc (0 : ℝ) 1).Nonempty :=
      (Set.nonempty_Icc.mpr zero_le_one).image _
    obtain ⟨_, ⟨q, hq, rfl⟩, hyv⟩ := exists_lt_of_lt_csSup hne hy
    have hcq : Continuous fun z => f z q :=
      hf.comp (continuous_id.prodMk continuous_const)
    filter_upwards [(hcq.tendsto x).eventually_const_lt hyv] with z hz
    have hbdd : BddAbove (f z '' Set.Icc (0 : ℝ) 1) :=
      (isCompact_Icc.image_of_continuousOn
        ((hf.comp (continuous_const.prodMk continuous_id)).continuousOn)).bddAbove
    exact lt_of_lt_of_le hz (le_csSup hbdd ⟨q, hq, rfl⟩)
  · -- u.s.c. side: sup at x < y ⇒ eventually sup at z < y
    intro y hy
    exact usc_sSup_image_of_compact f hf.upperSemicontinuous x y hy

end Exactcis.Spine
