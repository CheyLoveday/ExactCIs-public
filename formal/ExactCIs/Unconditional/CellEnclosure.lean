/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalHull
import ExactCIs.Unconditional.CompactAcceptedSet

/-! # Concrete scientific leaf guarantees and complete inner/outer enclosures

The mathematical partition owns every compact point exactly once. Accepted
claims retain effect-dependent nuisance witnesses in both directions; rejected
claims use one fixed direction. A boundary claim enters only the outer set.
These typed mathematical records are not a byte parser or an adaptive generator.
-/
namespace ExactCIs.Unconditional.CellEnclosure

open Set ProductBinomial EffectCoordinate

attribute [local instance] Classical.propDecidable

inductive State where
  | accepted | rejectedGreater | rejectedLess | boundary | unresolved
  | structuralAccepted (endpoint : Structural.Endpoint)
  | structuralRejected (endpoint : Structural.Endpoint)
  deriving DecidableEq

def innerClass : State → Bool
  | .accepted | .structuralAccepted _ => true
  | _ => false

def outerClass : State → Bool
  | .rejectedGreater | .rejectedLess | .structuralRejected _ => false
  | _ => true

def actual {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) : Set Compact :=
  {s | CompleteDomainCoverage.Accepted (effect s) r observed}

theorem actual_finite {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) (s : Compact)
    (interior : (s : ℝ) ∈ Ioo (0 : ℝ) 1) :
    s ∈ actual observed r ↔ BoschlooValidity.Accepted (beta s) r observed := by
  rw [actual, Set.mem_ofPred_eq]
  apply (CompactAcceptedSet.effect_agreement observed r s).symm.trans
  constructor
  · intro included
    simpa only [if_neg interior.1.ne', if_neg interior.2.ne] using included.2
  · intro included
    exact ⟨s.property, by simpa only [if_neg interior.1.ne', if_neg interior.2.ne] using included⟩

theorem actual_structural {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ)
    (e : Structural.Endpoint) :
    GlobalHull.endpoint e ∈ actual observed r ↔ Structural.Accepted e r observed := by
  rw [actual, Set.mem_ofPred_eq]
  cases e with
  | zero =>
    have agreement := CompactAcceptedSet.effect_agreement observed r (GlobalHull.endpoint .zero)
    exact agreement.symm.trans (CompactAcceptedSet.zero_mem observed r)
  | infinity =>
    have agreement := CompactAcceptedSet.effect_agreement observed r (GlobalHull.endpoint .infinity)
    exact agreement.symm.trans (CompactAcceptedSet.one_mem observed r)

inductive CellDecisionGuarantee {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ)
    (C : Set Compact) : State → Prop
  | accepted (interior : ∀ s ∈ C, (s : ℝ) ∈ Ioo (0 : ℝ) 1)
      (greater : ∀ s ∈ C, ∃ q ∈ Icc (0 : ℝ) 1,
        r ≤ ORNull.objective (BoschlooOrdering.mask .greater (beta s) observed) (beta s) q)
      (less : ∀ s ∈ C, ∃ q ∈ Icc (0 : ℝ) 1,
        r ≤ ORNull.objective (BoschlooOrdering.mask .less (beta s) observed) (beta s) q) :
      CellDecisionGuarantee observed r C .accepted
  | rejectedGreater (interior : ∀ s ∈ C, (s : ℝ) ∈ Ioo (0 : ℝ) 1)
      (strict : ∀ s ∈ C, ∀ q ∈ Icc (0 : ℝ) 1,
        ORNull.objective (BoschlooOrdering.mask .greater (beta s) observed) (beta s) q < r) :
      CellDecisionGuarantee observed r C .rejectedGreater
  | rejectedLess (interior : ∀ s ∈ C, (s : ℝ) ∈ Ioo (0 : ℝ) 1)
      (strict : ∀ s ∈ C, ∀ q ∈ Icc (0 : ℝ) 1,
        ORNull.objective (BoschlooOrdering.mask .less (beta s) observed) (beta s) q < r) :
      CellDecisionGuarantee observed r C .rejectedLess
  | boundary : CellDecisionGuarantee observed r C .boundary
  | unresolved : CellDecisionGuarantee observed r C .unresolved
  | structuralAccepted (e : Structural.Endpoint) (cell : C = {GlobalHull.endpoint e})
      (checked : Structural.Accepted e r observed) :
      CellDecisionGuarantee observed r C (.structuralAccepted e)
  | structuralRejected (e : Structural.Endpoint) (cell : C = {GlobalHull.endpoint e})
      (checked : ¬ Structural.Accepted e r observed) :
      CellDecisionGuarantee observed r C (.structuralRejected e)

theorem inner_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    {C : Set Compact} {state : State} (guarantee : CellDecisionGuarantee observed r C state)
    (selected : innerClass state = true) : C ⊆ actual observed r := by
  intro s member
  cases guarantee with
  | accepted interior greater less =>
    have positive : 0 < beta (s : ℝ) :=
      div_pos (interior s member).1 (sub_pos.mpr (interior s member).2)
    apply (actual_finite observed r s (interior s member)).mpr
    exact ⟨(NuisanceSupremum.accept_iff positive _).mpr (greater s member),
      (NuisanceSupremum.accept_iff positive _).mpr (less s member)⟩
  | structuralAccepted e cell checked =>
    have equal : s = GlobalHull.endpoint e := by simpa only [cell, mem_singleton_iff] using member
    rw [equal]
    exact (actual_structural observed r e).mpr checked
  | rejectedGreater _ _ | rejectedLess _ _ | boundary | unresolved | structuralRejected _ _ _ =>
    simp [innerClass] at selected

theorem rejected_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    {C : Set Compact} {state : State} (guarantee : CellDecisionGuarantee observed r C state)
    (selected : outerClass state ≠ true) : ∀ s ∈ C, s ∉ actual observed r := by
  intro s member included
  cases guarantee with
  | rejectedGreater interior strict =>
    have positive : 0 < beta (s : ℝ) :=
      div_pos (interior s member).1 (sub_pos.mpr (interior s member).2)
    obtain ⟨q, hq, attained⟩ := NuisanceSupremum.attained positive
      (BoschlooOrdering.mask .greater (beta s) observed)
    have bound : BoschlooValidity.value .greater (beta s) observed < r := by
      change NuisanceSupremum.value _ _ < r
      rw [← attained]
      exact strict s member q hq
    exact not_le_of_gt bound ((actual_finite observed r s (interior s member)).mp included).1
  | rejectedLess interior strict =>
    have positive : 0 < beta (s : ℝ) :=
      div_pos (interior s member).1 (sub_pos.mpr (interior s member).2)
    obtain ⟨q, hq, attained⟩ := NuisanceSupremum.attained positive
      (BoschlooOrdering.mask .less (beta s) observed)
    have bound : BoschlooValidity.value .less (beta s) observed < r := by
      change NuisanceSupremum.value _ _ < r
      rw [← attained]
      exact strict s member q hq
    exact not_le_of_gt bound ((actual_finite observed r s (interior s member)).mp included).2
  | structuralRejected e cell checked =>
    have equal : s = GlobalHull.endpoint e := by simpa only [cell, mem_singleton_iff] using member
    apply checked
    exact (actual_structural observed r e).mp (equal ▸ included)
  | accepted _ _ _ | boundary | unresolved | structuralAccepted _ _ _ =>
    simp [outerClass] at selected

structure Partition {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℝ) where
  size : ℕ
  cell : Fin size → Set Compact
  state : Fin size → State
  guarantee : ∀ i, CellDecisionGuarantee observed r (cell i) (state i)
  ownership : ∀ s : Compact, ∃! i, s ∈ cell i

def inner {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ} (p : Partition observed r) : Set Compact :=
  {s | ∃ i, s ∈ p.cell i ∧ innerClass (p.state i) = true}

def outer {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ} (p : Partition observed r) : Set Compact :=
  {s | ∃ i, s ∈ p.cell i ∧ outerClass (p.state i) = true}

theorem inner_outer {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ} (p : Partition observed r) :
    inner p ⊆ actual observed r ∧ actual observed r ⊆ outer p := by
  constructor
  · rintro s ⟨i, member, selected⟩
    exact inner_sound (p.guarantee i) selected member
  · intro s member
    obtain ⟨i, owner, _⟩ := p.ownership s
    have selected : outerClass (p.state i) = true := by
      by_contra rejected
      exact rejected_sound (p.guarantee i) rejected s owner member
    exact ⟨i, owner, selected⟩

theorem same_owner {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ} (p : Partition observed r)
    {s : Compact} {i j : Fin p.size} (hi : s ∈ p.cell i) (hj : s ∈ p.cell j) : i = j := by
  obtain ⟨k, _, unique⟩ := p.ownership s
  exact (unique i hi).trans (unique j hj).symm

theorem boundary_excluded_from_inner {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    (p : Partition observed r) (i : Fin p.size) (boundary : p.state i = .boundary) :
    ∀ s ∈ p.cell i, s ∉ inner p := by
  rintro s member ⟨j, other, selected⟩
  have equal := same_owner p member other
  subst j
  simp [boundary, innerClass] at selected

theorem boundary_retained_in_outer {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    (p : Partition observed r) (i : Fin p.size) (boundary : p.state i = .boundary) :
    p.cell i ⊆ outer p := by
  intro s member
  exact ⟨i, member, by simp [boundary, outerClass]⟩

structure SuccessCertificate {n1 n0 : ℕ} (observed : Outcome n1 n0) (r epsilon : ℝ) where
  partition : Partition observed r
  no_unresolved : ∀ i, partition.state i ≠ .unresolved
  epsilon_nonnegative : 0 ≤ epsilon
  inner_nonempty : (inner partition).Nonempty
  lower : GlobalHull.LowerBranch (inner partition) (outer partition) epsilon
  upper : GlobalHull.UpperBranch (inner partition) (outer partition) epsilon

theorem success_hull {n1 n0 : ℕ} {observed : Outcome n1 n0} {r epsilon : ℝ}
    (c : SuccessCertificate observed r epsilon) :
    GlobalHull.HullGuarantee (actual observed r) (outer c.partition) epsilon := by
  apply GlobalHull.t1MinHull
  exact ⟨c.epsilon_nonnegative, c.inner_nonempty, inner_outer c.partition, c.lower, c.upper⟩

theorem success_nonempty {n1 n0 : ℕ} {observed : Outcome n1 n0} {r epsilon : ℝ}
    (c : SuccessCertificate observed r epsilon) : (actual observed r).Nonempty :=
  c.inner_nonempty.mono (inner_outer c.partition).1

/-- Full scientific success consumes ownership, every leaf guarantee, the
explicit no-unresolved guard and both endpoint branches. -/
theorem success_complete {n1 n0 : ℕ} {observed : Outcome n1 n0} {r epsilon : ℝ}
    (c : SuccessCertificate observed r epsilon) :
    (∀ s : Compact, ∃! i, s ∈ c.partition.cell i) ∧
    (∀ i, c.partition.state i ≠ .unresolved) ∧
    (inner c.partition ⊆ actual observed r ∧ actual observed r ⊆ outer c.partition) ∧
    GlobalHull.HullGuarantee (actual observed r) (outer c.partition) epsilon :=
  ⟨c.partition.ownership, c.no_unresolved, inner_outer c.partition, success_hull c⟩

theorem empty_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    (p : Partition observed r) (all_rejected : ∀ i, outerClass (p.state i) = false) :
    actual observed r = ∅ := by
  apply Set.eq_empty_of_subset_empty
  intro s member
  obtain ⟨i, _, selected⟩ := (inner_outer p).2 member
  rw [all_rejected i] at selected
  exact Bool.noConfusion selected

theorem full_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℝ}
    (p : Partition observed r) (all_accepted : ∀ i, innerClass (p.state i) = true) :
    actual observed r = univ := by
  apply Set.eq_univ_of_forall
  intro s
  obtain ⟨i, owner, _⟩ := p.ownership s
  exact (inner_outer p).1 ⟨i, owner, all_accepted i⟩

theorem empty_forbids_success {n1 n0 : ℕ} {observed : Outcome n1 n0} {r epsilon : ℝ}
    (empty : actual observed r = ∅) : ¬ Nonempty (SuccessCertificate observed r epsilon) := by
  rintro ⟨c⟩
  have ne := success_nonempty c
  rw [empty] at ne
  exact Set.not_nonempty_empty ne

/-- Replacing each uniquely owned parent by a complete unique child partition
preserves the global ownership invariant, including every split point. -/
theorem refinement_preserves_ownership {X ι : Type*} (cell : ι → Set X)
    (owned : ∀ x : X, ∃! i, x ∈ cell i) (J : ι → Type*)
    (child : ∀ i, J i → Set X) (within : ∀ i j, child i j ⊆ cell i)
    (covered : ∀ i x, x ∈ cell i → ∃! j, x ∈ child i j) :
    ∀ x : X, ∃! ij : Sigma J, x ∈ child ij.1 ij.2 := by
  intro x
  obtain ⟨i, member, unique⟩ := owned x
  obtain ⟨j, included, child_unique⟩ := covered i x member
  refine ⟨⟨i, j⟩, included, ?_⟩
  rintro ⟨k, l⟩ hl
  have equal := unique k (within k l hl)
  subst k
  have same := child_unique l hl
  subst l
  rfl

end ExactCIs.Unconditional.CellEnclosure
