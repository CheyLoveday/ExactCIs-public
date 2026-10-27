/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerAnchor

/-! # Constructing all five T1 premises from checked candidate anchors

Finite checks use rational enclosures of accepted anchors and the original
beta-space excess. Structural checks require exact endpoint ownership and exact
reported bounds. No T1 premise is a field of the candidate payload.
-/
namespace ExactCIs.Unconditional.GlobalCheckerHull

open Set ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition
open GlobalCheckerEnclosure GlobalCheckerAnchor EffectCoordinate GlobalHull

theorem interval_extrema {lo hi : ℚ} (bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) :
    lower (interval lo hi) = (lo : ℝ) ∧ upper (interval lo hi) = (hi : ℝ) := by
  have ordered : (lo : ℝ) ≤ hi := by exact_mod_cast bounds.2.1
  have image : realImage (interval lo hi) = Icc (lo : ℝ) hi := by
    ext x
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact hs
    · intro hx
      have domain : x ∈ Icc (0 : ℝ) 1 :=
        ⟨(by exact_mod_cast bounds.1 : (0 : ℝ) ≤ lo).trans hx.1,
          hx.2.trans (by exact_mod_cast bounds.2.2)⟩
      exact ⟨⟨x, domain⟩, hx, rfl⟩
  simp only [lower, upper, image, csInf_Icc ordered, csSup_Icc ordered, and_self]

theorem lower_le_member {I : Set Compact} {s : Compact} (member : s ∈ I) : lower I ≤ s :=
  csInf_le (bddBelow_Icc.mono (image_domain I)) ⟨s, member, rfl⟩

theorem member_le_upper {I : Set Compact} {s : Compact} (member : s ∈ I) : (s : ℝ) ≤ upper I :=
  le_csSup (bddAbove_Icc.mono (image_domain I)) ⟨s, member, rfl⟩

theorem lower_anchor {I : Set Compact} {lo hi alo ahi epsilon : ℚ}
    (bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1)
    (anchor : ∃ s ∈ I, (s : ℝ) ∈ Icc (alo : ℝ) ahi)
    (positive : 0 < lo) (finite : ahi < 1)
    (fringe : ahi / (1 - ahi) - lo / (1 - lo) ≤ epsilon) :
    I.Nonempty ∧ Nonempty (LowerBranch I (interval lo hi) epsilon) := by
  obtain ⟨s, member, enclosed⟩ := anchor
  have finite' : (ahi : ℝ) < 1 := by exact_mod_cast finite
  have order : lower I ≤ (ahi : ℝ) := (lower_le_member member).trans enclosed.2
  have nonnegative : (0 : ℝ) ≤ ahi := s.property.1.trans enclosed.2
  have transported : beta (lower I) ≤ beta (ahi : ℝ) := beta_strictMonoOn.monotoneOn
    ⟨(extrema_domain I).1.1, order.trans_lt finite'⟩ ⟨nonnegative, finite'⟩ order
  have fringe' : beta (ahi : ℝ) - beta (lo : ℝ) ≤ (epsilon : ℝ) := by
    dsimp [beta]
    exact_mod_cast fringe
  refine ⟨⟨s, member⟩, ⟨LowerBranch.finite ?_ (order.trans_lt finite') ?_⟩⟩
  · rw [(interval_extrema bounds).1]
    exact_mod_cast positive
  · rw [(interval_extrema bounds).1]
    linarith

theorem upper_anchor {I : Set Compact} {lo hi alo ahi epsilon : ℚ}
    (bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) (contained : I ⊆ interval lo hi)
    (anchor : ∃ s ∈ I, (s : ℝ) ∈ Icc (alo : ℝ) ahi)
    (positive : 0 < alo) (finite : hi < 1)
    (fringe : hi / (1 - hi) - alo / (1 - alo) ≤ epsilon) :
    I.Nonempty ∧ Nonempty (UpperBranch I (interval lo hi) epsilon) := by
  obtain ⟨s, member, enclosed⟩ := anchor
  have positive' : (0 : ℝ) < alo := by exact_mod_cast positive
  have finite' : (hi : ℝ) < 1 := by exact_mod_cast finite
  have order : (alo : ℝ) ≤ upper I := enclosed.1.trans (member_le_upper member)
  have upper_bound : upper I ≤ (hi : ℝ) :=
    csSup_le (show (realImage I).Nonempty from ⟨s, s, member, rfl⟩)
      (by rintro x ⟨t, ht, rfl⟩; exact (contained ht).2)
  have transported : beta (alo : ℝ) ≤ beta (upper I) := beta_strictMonoOn.monotoneOn
    ⟨positive'.le, order.trans_lt (upper_bound.trans_lt finite')⟩
    ⟨(extrema_domain I).2.1, upper_bound.trans_lt finite'⟩ order
  have fringe' : beta (hi : ℝ) - beta (alo : ℝ) ≤ (epsilon : ℝ) := by
    dsimp [beta]
    exact_mod_cast fringe
  refine ⟨⟨s, member⟩, ⟨UpperBranch.finite (positive'.trans_le order) ?_ ?_⟩⟩
  · rw [(interval_extrema bounds).2]
    exact finite'
  · rw [(interval_extrema bounds).2]
    linarith

def endpointRat : Structural.Endpoint → ℚ
  | .zero => 0
  | .infinity => 1

theorem endpointRat_cast (e : Structural.Endpoint) :
    (endpointRat e : ℝ) = (endpoint e : ℝ) := by cases e <;> simp [endpointRat, endpoint]

theorem structural_member {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {e : Structural.Endpoint} (checked : Structural.check e r observed = true) :
    endpoint e ∈ acceptedCells observed r chain := by
  cases e
  · exact Or.inl (Or.inl ⟨checked, rfl⟩)
  · exact Or.inl (Or.inr ⟨checked, rfl⟩)

theorem lower_structural {I : Set Compact} {lo hi : ℚ} {epsilon : ℝ} {e : Structural.Endpoint}
    (bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) (contained : I ⊆ interval lo hi)
    (member : endpoint e ∈ I) (aligned : lo = endpointRat e) :
    I.Nonempty ∧ Nonempty (LowerBranch I (interval lo hi) epsilon) := by
  have lower_bound : (lo : ℝ) ≤ lower I :=
    le_csInf (show (realImage I).Nonempty from ⟨endpoint e, endpoint e, member, rfl⟩)
      (by rintro x ⟨t, ht, rfl⟩; exact (contained ht).1)
  have lower_exact : lower I = (endpoint e : ℝ) := le_antisymm (lower_le_member member)
    (by simpa only [aligned, endpointRat_cast] using lower_bound)
  exact ⟨⟨endpoint e, member⟩, ⟨.structural e member
    (by rw [(interval_extrema bounds).1, aligned, endpointRat_cast]) lower_exact⟩⟩

theorem upper_structural {I : Set Compact} {lo hi : ℚ} {epsilon : ℝ} {e : Structural.Endpoint}
    (bounds : 0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) (contained : I ⊆ interval lo hi)
    (member : endpoint e ∈ I) (aligned : hi = endpointRat e) :
    I.Nonempty ∧ Nonempty (UpperBranch I (interval lo hi) epsilon) := by
  have upper_bound : upper I ≤ (hi : ℝ) :=
    csSup_le (show (realImage I).Nonempty from ⟨endpoint e, endpoint e, member, rfl⟩)
      (by rintro x ⟨t, ht, rfl⟩; exact (contained ht).2)
  have upper_exact : upper I = (endpoint e : ℝ) := le_antisymm
    (by simpa only [aligned, endpointRat_cast] using upper_bound) (member_le_upper member)
  exact ⟨⟨endpoint e, member⟩, ⟨.structural e member
    (by rw [(interval_extrema bounds).2, aligned, endpointRat_cast]) upper_exact⟩⟩

inductive Branch where
  | structural (endpoint : Structural.Endpoint)
  | finite (anchor : Anchor) (enclosureLower enclosureUpper : ℚ)

def lowerCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r lo epsilon : ℚ)
    (chain : Chain) : Branch → Bool
  | .structural e => Structural.check e r observed && decide (lo = endpointRat e)
  | .finite anchor alo ahi => match resolve chain anchor with
    | none => false
    | some p => decide (alo ≤ p.lower ∧ p.upper ≤ ahi ∧ 0 < lo ∧ ahi < 1 ∧
        ahi / (1 - ahi) - lo / (1 - lo) ≤ epsilon)

def upperCheck {n1 n0 : ℕ} (observed : Outcome n1 n0) (r hi epsilon : ℚ)
    (chain : Chain) : Branch → Bool
  | .structural e => Structural.check e r observed && decide (hi = endpointRat e)
  | .finite anchor alo ahi => match resolve chain anchor with
    | none => false
    | some p => decide (alo ≤ p.lower ∧ p.upper ≤ ahi ∧ 0 < alo ∧ hi < 1 ∧
        hi / (1 - hi) - alo / (1 - alo) ≤ epsilon)

theorem lowerCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r lo hi epsilon : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness} {branch : Branch}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (outer : outerCheck observed r lo hi chain = true)
    (checked : lowerCheck observed r lo epsilon chain branch = true) :
    (acceptedCells observed r chain).Nonempty ∧
      Nonempty (LowerBranch (acceptedCells observed r chain) (interval lo hi) epsilon) := by
  have bounds := outerCheck_sound leaves outer
  have contained := (sandwich leaves).1.trans ((sandwich leaves).2.trans bounds.2)
  cases branch with
  | structural e =>
    have h := Bool.and_eq_true_iff.mp checked
    exact lower_structural bounds.1 contained (structural_member h.1) (of_decide_eq_true h.2)
  | finite anchor alo ahi =>
    cases resolved : resolve chain anchor with
    | none => simp [lowerCheck, resolved] at checked
    | some p =>
      have h : alo ≤ p.lower ∧ p.upper ≤ ahi ∧ 0 < lo ∧ ahi < 1 ∧
          ahi / (1 - ahi) - lo / (1 - lo) ≤ epsilon := by
        simpa only [lowerCheck, resolved, decide_eq_true_eq] using checked
      exact lower_anchor bounds.1 (enclosed_anchor leaves resolved ⟨h.1, h.2.1⟩)
        h.2.2.1 h.2.2.2.1 h.2.2.2.2

theorem upperCheck_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r lo hi epsilon : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness} {branch : Branch}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (outer : outerCheck observed r lo hi chain = true)
    (checked : upperCheck observed r hi epsilon chain branch = true) :
    (acceptedCells observed r chain).Nonempty ∧
      Nonempty (UpperBranch (acceptedCells observed r chain) (interval lo hi) epsilon) := by
  have bounds := outerCheck_sound leaves outer
  have contained := (sandwich leaves).1.trans ((sandwich leaves).2.trans bounds.2)
  cases branch with
  | structural e =>
    have h := Bool.and_eq_true_iff.mp checked
    exact upper_structural bounds.1 contained (structural_member h.1) (of_decide_eq_true h.2)
  | finite anchor alo ahi =>
    cases resolved : resolve chain anchor with
    | none => simp [upperCheck, resolved] at checked
    | some p =>
      have h : alo ≤ p.lower ∧ p.upper ≤ ahi ∧ 0 < alo ∧ hi < 1 ∧
          hi / (1 - hi) - alo / (1 - alo) ≤ epsilon := by
        simpa only [upperCheck, resolved, decide_eq_true_eq] using checked
      exact upper_anchor bounds.1 contained (enclosed_anchor leaves resolved ⟨h.1, h.2.1⟩)
        h.2.2.1 h.2.2.2.1 h.2.2.2.2

def check {n1 n0 : ℕ} (observed : Outcome n1 n0) (r epsilon lo hi : ℚ)
    (chain : Chain) (lower upper : Branch) : Bool :=
  decide (0 ≤ epsilon) && outerCheck observed r lo hi chain &&
    lowerCheck observed r lo epsilon chain lower && upperCheck observed r hi epsilon chain upper

theorem check_sound {n1 n0 : ℕ} {observed : Outcome n1 n0} {r epsilon lo hi : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness} {lb ub : Branch}
    (leaves : GlobalCheckerPartition.check observed r chain order = true)
    (checked : check observed r epsilon lo hi chain lb ub = true) :
    HullGuarantee (CellEnclosure.actual observed r) (interval lo hi) epsilon := by
  have parts : 0 ≤ epsilon ∧ outerCheck observed r lo hi chain = true ∧
      lowerCheck observed r lo epsilon chain lb = true ∧
      upperCheck observed r hi epsilon chain ub = true := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
  have lower := lowerCheck_sound leaves parts.2.1 parts.2.2.1
  have upper := upperCheck_sound leaves parts.2.1 parts.2.2.2
  apply t1MinHull
  exact ⟨by exact_mod_cast parts.1, lower.1,
    ⟨(sandwich leaves).1, (sandwich leaves).2.trans (outerCheck_sound leaves parts.2.1).2⟩,
    Classical.choice lower.2, Classical.choice upper.2⟩

end ExactCIs.Unconditional.GlobalCheckerHull
