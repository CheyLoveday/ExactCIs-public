import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Threshold tangency: the L-A bridge and the certificate normal form

Spine module 0 (foundation). Ratified convention (ledger L37 /
ExactCIs-public#41, preflight P10):

  accept ⟺ sup_q H(q) ≥ α ⟺ ∃ q, H(q) ≥ α
  reject ⟺ sup_q H(q) < α ⟺ ∀ q, H(q) < α

Contents:
* `exists_ge_iff_le_sSup`, `forall_lt_iff_sSup_lt`, `accept_at_tangency` —
  the L-A lemmas joining the sup-form and exists-form decisions, including
  exactly at tangency `sup = α`.
* `accept_normalForm_iff`, `reject_normalForm_iff` — **the certificate
  normal-form bridge** (open question resolved): the `H ≥ 0` certificate
  form and the `H ≥ α` form are interchangeable by shifting the objective,
  so pinning the normal form (#48 comment; review §9 item 4) is a
  restatement of the spec, not new proof work. Both directions are proved
  by two applications of the L-A bridge — no `sSup` arithmetic is needed.
-/

namespace Exactcis.Spine

open Set

/-- L-A, accept form: `∃ q ∈ [0,1], f q ≥ α` iff `α ≤ sup f([0,1])`.
The forward direction needs only boundedness of the image; the backward
direction is attainment: a compact set contains its supremum. -/
theorem exists_ge_iff_le_sSup {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (α : ℝ) :
    (∃ q ∈ Set.Icc (0 : ℝ) 1, α ≤ f q) ↔ α ≤ sSup (f '' Set.Icc 0 1) := by
  have hK : IsCompact (f '' Set.Icc (0 : ℝ) 1) :=
    isCompact_Icc.image_of_continuousOn hf
  have hne : (f '' Set.Icc (0 : ℝ) 1).Nonempty :=
    (Set.nonempty_Icc.mpr zero_le_one).image f
  constructor
  · rintro ⟨q, hq, hfq⟩
    exact hfq.trans (le_csSup hK.bddAbove ⟨q, hq, rfl⟩)
  · intro h
    obtain ⟨q, hq, hfq⟩ := hK.sSup_mem hne
    exact ⟨q, hq, by rw [hfq]; exact h⟩

/-- L-A, strict dual (reject form): `∀ q ∈ [0,1], f q < α` iff
`sup f([0,1]) < α`. This is the contrapositive of `exists_ge_iff_le_sSup`. -/
theorem forall_lt_iff_sSup_lt {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (α : ℝ) :
    (∀ q ∈ Set.Icc (0 : ℝ) 1, f q < α) ↔ sSup (f '' Set.Icc 0 1) < α := by
  rw [← not_iff_not]
  push Not
  exact exists_ge_iff_le_sSup hf α

/-- L-A tangency corollary: at exact tangency `sup = α` the decision is
ACCEPT — a witness `q` with `f q ≥ α` exists because the sup is attained. -/
theorem accept_at_tangency {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) {α : ℝ}
    (htan : sSup (f '' Set.Icc 0 1) = α) :
    ∃ q ∈ Set.Icc (0 : ℝ) 1, α ≤ f q :=
  (exists_ge_iff_le_sSup hf α).mpr htan.ge

/-! ## The certificate normal form (`H ≥ 0` vs `H ≥ α`) -/

/-- Normal-form bridge, accept side: the `α`-threshold decision on `f` is
the `0`-threshold decision on the shifted objective `f - α`. Hence the
`H ≥ 0` certificate normal form is the instantiation of the `H ≥ α` form
at the shifted objective, and adopting either is a restatement. -/
theorem accept_normalForm_iff {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (α : ℝ) :
    α ≤ sSup (f '' Set.Icc 0 1) ↔
      0 ≤ sSup ((fun q => f q - α) '' Set.Icc 0 1) := by
  have hshift : ContinuousOn (fun q => f q - α) (Set.Icc 0 1) :=
    hf.sub continuousOn_const
  rw [← exists_ge_iff_le_sSup hf α, ← exists_ge_iff_le_sSup hshift 0]
  simp [sub_nonneg]

/-- Normal-form bridge, reject side: strict dual of
`accept_normalForm_iff`. -/
theorem reject_normalForm_iff {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc 0 1)) (α : ℝ) :
    sSup (f '' Set.Icc 0 1) < α ↔
      sSup ((fun q => f q - α) '' Set.Icc 0 1) < 0 :=
  lt_iff_lt_of_le_iff_le (accept_normalForm_iff hf α)

end Exactcis.Spine
