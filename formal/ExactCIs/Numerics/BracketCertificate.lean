import Mathlib

/-! Abstract real bracket certificates, independent of floating evaluation. -/

namespace ExactCIs.Numerics

/-- A closed real bracket with endpoint signs oriented from nonpositive to
nonnegative. -/
structure Bracket (f : ℝ → ℝ) where
  left : ℝ
  right : ℝ
  ordered : left ≤ right
  left_nonpositive : f left ≤ 0
  right_nonnegative : 0 ≤ f right

namespace Bracket

/-- The real midpoint of a retained bracket. -/
noncomputable def midpoint (bracket : Bracket f) : ℝ :=
  (bracket.left + bracket.right) / 2

/-- Continuity and opposite endpoint signs produce a root in the closed
bracket. -/
theorem root_exists {f : ℝ → ℝ} (bracket : Bracket f)
    (continuous : ContinuousOn f (Set.Icc bracket.left bracket.right)) :
    ∃ root ∈ Set.Icc bracket.left bracket.right, f root = 0 := by
  have zero_in_image : 0 ∈ f '' Set.Icc bracket.left bracket.right :=
    intermediate_value_Icc bracket.ordered continuous
      ⟨bracket.left_nonpositive, bracket.right_nonnegative⟩
  rcases zero_in_image with ⟨root, root_in, root_zero⟩
  exact ⟨root, root_in, root_zero⟩

/-- Every point retained inside a bracket is within half its width of the
midpoint. The conclusion has no function-scale term. -/
theorem midpoint_error {left right root : ℝ} (root_in : root ∈ Set.Icc left right) :
    |root - (left + right) / 2| ≤ (right - left) / 2 := by
  rw [abs_le]
  constructor <;> linarith [root_in.1, root_in.2]

/-- A root retained by a certificate inherits the midpoint error bound. -/
theorem retained_root_midpoint_error {f : ℝ → ℝ} (bracket : Bracket f) {root : ℝ}
    (root_in : root ∈ Set.Icc bracket.left bracket.right) :
    |root - bracket.midpoint| ≤ (bracket.right - bracket.left) / 2 := by
  exact midpoint_error root_in

/-- The second bracket is a retained refinement of the first. -/
def Refines {f : ℝ → ℝ} (outer inner : Bracket f) : Prop :=
  outer.left ≤ inner.left ∧ inner.right ≤ outer.right

/-- Refinement cannot increase certified bracket width. -/
theorem width_nonincreasing {f : ℝ → ℝ} {outer inner : Bracket f}
    (refines : Refines outer inner) :
    inner.right - inner.left ≤ outer.right - outer.left := by
  dsimp [Refines] at refines
  linarith [refines.1, refines.2]

end Bracket

/-- A finite search limit is operational metadata, distinct from the two
mathematical structural endpoints. -/
inductive DomainBoundary where
  | structuralZero
  | structuralInfinity
  | finiteSearchSentinel (value : ℝ)

/-- Whether a boundary tag is a mathematical endpoint rather than an operational
search sentinel. -/
def DomainBoundary.isMathematicalEndpoint : DomainBoundary → Prop
  | .structuralZero => True
  | .structuralInfinity => True
  | .finiteSearchSentinel _ => False

theorem finite_sentinel_not_mathematical_endpoint (value : ℝ) :
    ¬ DomainBoundary.isMathematicalEndpoint (.finiteSearchSentinel value) := by
  simp [DomainBoundary.isMathematicalEndpoint]

end ExactCIs.Numerics
