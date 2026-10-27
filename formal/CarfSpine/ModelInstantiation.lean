import CarfSpine.AcceptedSetTopology
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Model instantiation: the unconditional 2×2 binomial model meets the spine

Discharges the M1/M2 topology flags (devplan 24 §2, spine README): every
spine theorem so far was stated over abstract carriers; this module binds
the topology chain to the actual unconditional two-binomial model.

Binding: compactified effect `s ∈ [0,1]` with odds ratio `ψ = s/(1-s)`;
nuisance `q = p₂ ∈ [0,1]`; treatment-arm probability
`p₁(s,q) = ψq/(1-q+ψq) = s·q / ((1-s)(1-q) + s·q)`; outcome `(y₁,y₂)` mass
the product of the two binomial pmfs.

**The finding this lane exists to surface**: the cleared denominator
`D(s,q) = (1-s)(1-q) + s·q` is *not* positive on all of `[0,1]²` — it
vanishes exactly at the corners `(0,1)` and `(1,0)` (`denom_corner_zero`),
and `p₁` is genuinely discontinuous there
(`p1_not_continuousAt_corner`, machine-checked: along `q = 1` the limit is
`1`, while `p₁(0,1) = 0`). So devplan 22 §2's "after positive denominators
are cleared" holds on interior effect strata only, and no mass-continuity
hypothesis of the spine can be discharged on all of `[0,1]²`. The
instantiation theorems are therefore stated on a closed interior stratum
`s ∈ [a,b] ⊂ (0,1)` — matching the spec's own structure: `s = 0, 1` are
the structural endpoints (`β = 0, ∞`) that the contract handles by
explicit structural-endpoint certificates, not by the generic topology
chain (spine README; devplan 25 §T6).

On the stratum everything instantiates: the link lands in `[0,1]`
(`denom_pos`, `p1_mem_Icc`); the joint outcome mass satisfies exactly the
hypotheses the spine composites consume (`stratumMass_continuous`,
`stratumMass_nonneg`; the nuisance is clamped to `[0,1]`, which changes
nothing on the evaluated domain — `stratumMass_eq_jointMass`); and the
four §1 topology conclusions become statements about *this* model
(`boschloo_directionalPValue_upperSemicontinuous`,
`boschloo_directionalAcceptedSet_isClosed`,
`boschloo_twoSidedAcceptedSet_isCompact`, `boschloo_fixedMask_continuous`).
`orderingMaskRegion_isClosed` supplies the closed-mask hypothesis once the
ordering-comparison polynomials land.

Still open after this module (deliberately): the concrete
ordering/statistic layer (the `g_{d,y}` polynomials and cutoff structure)
and the certificate checkers — the C-ACC/C-REJ soundness flags. Those are
algebra, not topology.
-/

namespace Exactcis.Spine

open Set Filter Topology

/-! ## The link function and its domain -/

/-- Cleared denominator of the odds-ratio link:
`D(s,q) = (1-s)(1-q) + s·q`. -/
def denom (s q : ℝ) : ℝ := (1 - s) * (1 - q) + s * q

/-- Treatment-arm probability under the compactified odds-ratio link. -/
noncomputable def p1 (s q : ℝ) : ℝ := s * q / denom s q

/-- `D > 0` on interior effect values `0 < s < 1` for every nuisance
`q ∈ [0,1]`. Sharp: see `denom_corner_zero`. -/
theorem denom_pos {s q : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < denom s q := by
  unfold denom
  rcases eq_or_lt_of_le hq0 with h | h
  · have hq : q = 0 := h.symm
    subst hq
    have hrw : (1 - s) * (1 - (0 : ℝ)) + s * 0 = 1 - s := by ring
    rw [hrw]
    linarith
  · have h2 : 0 < s * q := mul_pos hs0 h
    have h1 : 0 ≤ (1 - s) * (1 - q) :=
      mul_nonneg (by linarith) (by linarith)
    linarith

/-- The corner degeneracy, machine-checked: the cleared denominator
vanishes at `(s,q) = (0,1)` and `(1,0)`. -/
theorem denom_corner_zero : denom 0 1 = 0 ∧ denom 1 0 = 0 := by
  constructor <;> · unfold denom; norm_num

/-- On the interior stratum the link lands in `[0,1]`. -/
theorem p1_mem_Icc {s q : ℝ} (hs0 : 0 < s) (hs1 : s < 1)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : p1 s q ∈ Set.Icc (0 : ℝ) 1 := by
  have hD := denom_pos hs0 hs1 hq0 hq1
  constructor
  · exact div_nonneg (mul_nonneg hs0.le hq0) hD.le
  · rw [p1, div_le_one hD]
    have h1 : 0 ≤ (1 - s) * (1 - q) :=
      mul_nonneg (by linarith) (by linarith)
    unfold denom
    linarith

/-- **Refutation of naive full-square continuity** (the instantiation-lane
finding): `p₁` is not continuous at the corner `(0,1)`. Along the path
`q = 1` the value is identically `1` for `s > 0`, while `p₁(0,1) = 0`.
Hence the spine's mass hypotheses cannot hold on all of `[0,1]²`; interior
strata plus the structural-endpoint conventions are the correct domain. -/
theorem p1_not_continuousAt_corner :
    ¬ ContinuousAt (fun p : ℝ × ℝ => p1 p.1 p.2) ((0 : ℝ), (1 : ℝ)) := by
  intro h
  have hval : p1 0 1 = 0 := by simp [p1]
  have hγ : Tendsto (fun t : ℝ => ((t, 1) : ℝ × ℝ)) (𝓝[>] (0 : ℝ))
      (𝓝 ((0 : ℝ), (1 : ℝ))) :=
    ((continuous_id.prodMk continuous_const).tendsto 0).mono_left
      nhdsWithin_le_nhds
  have hpath : Tendsto (fun t : ℝ => p1 t 1) (𝓝[>] (0 : ℝ))
      (𝓝 (p1 0 1)) := Filter.Tendsto.comp h hγ
  have heq : (fun t : ℝ => p1 t 1) =ᶠ[𝓝[>] (0 : ℝ)] fun _ => (1 : ℝ) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    have hD : denom t 1 = t := by unfold denom; ring
    have hp : p1 t 1 = t / t := by unfold p1; rw [hD, mul_one]
    rw [hp, div_self (ne_of_gt ht)]
  have hone : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] (0 : ℝ))
      (𝓝 (p1 0 1)) := hpath.congr' heq
  have h01 : p1 0 1 = 1 := tendsto_nhds_unique hone tendsto_const_nhds
  rw [hval] at h01
  exact zero_ne_one h01

/-! ## Binomial mass and the clamped nuisance -/

/-- Binomial pmf term (unnormalised conventions are irrelevant here; this
is the standard pmf). -/
noncomputable def binMass (n y : ℕ) (p : ℝ) : ℝ :=
  (n.choose y : ℝ) * p ^ y * (1 - p) ^ (n - y)

theorem binMass_nonneg (n y : ℕ) {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    0 ≤ binMass n y p :=
  mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (pow_nonneg h0 _))
    (pow_nonneg (by linarith) _)

theorem binMass_continuous (n y : ℕ) :
    Continuous fun p : ℝ => binMass n y p := by
  unfold binMass
  fun_prop

/-- Clamp to `[0,1]`: extends the mass continuously and nonnegatively to
the whole real nuisance line, agreeing with the identity on `[0,1]` (the
only region the `sSup` over `Icc 0 1` ever evaluates). -/
noncomputable def clamp01 (q : ℝ) : ℝ := max 0 (min 1 q)

theorem clamp01_mem_Icc (q : ℝ) : clamp01 q ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

theorem clamp01_eq_self {q : ℝ} (h : q ∈ Set.Icc (0 : ℝ) 1) :
    clamp01 q = q := by
  have h1 : min 1 q = q := min_eq_right h.2
  rw [clamp01, h1, max_eq_right h.1]

theorem clamp01_continuous : Continuous clamp01 :=
  continuous_const.max (continuous_const.min continuous_id)

/-! ## The stratum mass -/

variable {a b : ℝ}

/-- Interior bounds for a point of the stratum. -/
theorem stratum_mem (ha : 0 < a) (hb : b < 1) (x : ↥(Set.Icc a b)) :
    0 < (x : ℝ) ∧ (x : ℝ) < 1 :=
  ⟨ha.trans_le x.2.1, lt_of_le_of_lt x.2.2 hb⟩

/-- Joint outcome mass on the interior stratum, with the nuisance clamped
so continuity and nonnegativity hold on all of `↥[a,b] × ℝ` — exactly the
hypothesis shape the spine composites consume. -/
noncomputable def stratumMass (n₁ n₂ y₁ y₂ : ℕ)
    (x : ↥(Set.Icc a b) × ℝ) : ℝ :=
  binMass n₁ y₁ (p1 (x.1 : ℝ) (clamp01 x.2)) * binMass n₂ y₂ (clamp01 x.2)

/-- On the nominal nuisance domain the clamp is invisible: the banked
object is the intended joint mass. -/
theorem stratumMass_eq_jointMass (n₁ n₂ y₁ y₂ : ℕ)
    (x : ↥(Set.Icc a b)) {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    stratumMass n₁ n₂ y₁ y₂ (x, q)
      = binMass n₁ y₁ (p1 (x : ℝ) q) * binMass n₂ y₂ q := by
  unfold stratumMass
  rw [clamp01_eq_self hq]

theorem stratumMass_continuous (ha : 0 < a) (hb : b < 1)
    (n₁ n₂ y₁ y₂ : ℕ) :
    Continuous (stratumMass (a := a) (b := b) n₁ n₂ y₁ y₂) := by
  have hs : Continuous fun x : ↥(Set.Icc a b) × ℝ => (x.1 : ℝ) :=
    continuous_subtype_val.comp continuous_fst
  have hq : Continuous fun x : ↥(Set.Icc a b) × ℝ => clamp01 x.2 :=
    clamp01_continuous.comp continuous_snd
  have hD : Continuous fun x : ↥(Set.Icc a b) × ℝ =>
      denom (x.1 : ℝ) (clamp01 x.2) := by
    unfold denom
    exact ((continuous_const.sub hs).mul (continuous_const.sub hq)).add
      (hs.mul hq)
  have hDne : ∀ x : ↥(Set.Icc a b) × ℝ,
      denom (x.1 : ℝ) (clamp01 x.2) ≠ 0 := fun x =>
    (denom_pos (stratum_mem ha hb x.1).1 (stratum_mem ha hb x.1).2
      (clamp01_mem_Icc x.2).1 (clamp01_mem_Icc x.2).2).ne'
  have hp1 : Continuous fun x : ↥(Set.Icc a b) × ℝ =>
      p1 (x.1 : ℝ) (clamp01 x.2) := by
    unfold p1
    exact (hs.mul hq).div hD hDne
  unfold stratumMass
  exact ((binMass_continuous n₁ y₁).comp hp1).mul
    ((binMass_continuous n₂ y₂).comp hq)

theorem stratumMass_nonneg (ha : 0 < a) (hb : b < 1)
    (n₁ n₂ y₁ y₂ : ℕ) (x : ↥(Set.Icc a b) × ℝ) :
    0 ≤ stratumMass n₁ n₂ y₁ y₂ x := by
  have hm := stratum_mem ha hb x.1
  have hc := clamp01_mem_Icc x.2
  have hp := p1_mem_Icc hm.1 hm.2 hc.1 hc.2
  exact mul_nonneg (binMass_nonneg _ _ hp.1 hp.2)
    (binMass_nonneg _ _ hc.1 hc.2)

/-! ## Ordering regions -/

/-- An inclusive ordering-comparison region `{g(s) ≤ 0}` lifted to
statistic × nuisance space is closed whenever the comparison function is
continuous — the `S o` hypothesis of the composites, ready for the
concrete ordering polynomials. -/
theorem orderingMaskRegion_isClosed {X : Type*} [TopologicalSpace X]
    {g : X → ℝ} (hg : Continuous g) :
    IsClosed {p : X × ℝ | g p.1 ≤ 0} :=
  isClosed_le (hg.comp continuous_fst) continuous_const

/-! ## The four §1 topology conclusions, for this model -/

/-- Blocking theorem 2, instantiated: the directional p-value of the
unconditional two-binomial model with moving inclusive masks is upper
semicontinuous on any interior effect stratum. -/
theorem boschloo_directionalPValue_upperSemicontinuous
    (ha : 0 < a) (hb : b < 1) (n₁ n₂ : ℕ) {mo : ℕ} (y₁ y₂ : Fin mo → ℕ)
    (S : Fin mo → Set (↥(Set.Icc a b) × ℝ)) (hS : ∀ o, IsClosed (S o)) :
    UpperSemicontinuous fun x : ↥(Set.Icc a b) => sSup
      ((fun q => ∑ o : Fin mo,
        (S o).indicator (stratumMass n₁ n₂ (y₁ o) (y₂ o)) (x, q)) ''
          Set.Icc (0 : ℝ) 1) :=
  directionalPValue_upperSemicontinuous S hS
    (fun o => stratumMass n₁ n₂ (y₁ o) (y₂ o))
    (fun o => stratumMass_continuous ha hb n₁ n₂ (y₁ o) (y₂ o))
    (fun o p => stratumMass_nonneg ha hb n₁ n₂ (y₁ o) (y₂ o) p)

/-- Blocking theorem 3, instantiated: the directional accepted set is
closed in the stratum. -/
theorem boschloo_directionalAcceptedSet_isClosed
    (ha : 0 < a) (hb : b < 1) (n₁ n₂ : ℕ) {mo : ℕ} (y₁ y₂ : Fin mo → ℕ)
    (S : Fin mo → Set (↥(Set.Icc a b) × ℝ)) (hS : ∀ o, IsClosed (S o))
    (α : ℝ) :
    IsClosed {x : ↥(Set.Icc a b) | α ≤ sSup
      ((fun q => ∑ o : Fin mo,
        (S o).indicator (stratumMass n₁ n₂ (y₁ o) (y₂ o)) (x, q)) ''
          Set.Icc (0 : ℝ) 1)} :=
  directionalAcceptedSet_isClosed S hS
    (fun o => stratumMass n₁ n₂ (y₁ o) (y₂ o))
    (fun o => stratumMass_continuous ha hb n₁ n₂ (y₁ o) (y₂ o))
    (fun o p => stratumMass_nonneg ha hb n₁ n₂ (y₁ o) (y₂ o) p) α

/-- Blocking theorem 4, instantiated: the two-sided accepted set — the
intersection of the two directional accepted sets — is compact in the
stratum (the stratum subtype is a compact space). This is what attains
`inf A` and `sup A` for the hull layer, now for the real model. -/
theorem boschloo_twoSidedAcceptedSet_isCompact
    (ha : 0 < a) (hb : b < 1) (n₁ n₂ : ℕ) {mo : ℕ} (y₁ y₂ : Fin mo → ℕ)
    (Sgt Slt : Fin mo → Set (↥(Set.Icc a b) × ℝ))
    (hSgt : ∀ o, IsClosed (Sgt o)) (hSlt : ∀ o, IsClosed (Slt o))
    (αgt αlt : ℝ) :
    IsCompact {x : ↥(Set.Icc a b) |
      (αgt ≤ sSup ((fun q => ∑ o : Fin mo,
        (Sgt o).indicator (stratumMass n₁ n₂ (y₁ o) (y₂ o)) (x, q)) ''
          Set.Icc (0 : ℝ) 1)) ∧
      (αlt ≤ sSup ((fun q => ∑ o : Fin mo,
        (Slt o).indicator (stratumMass n₁ n₂ (y₁ o) (y₂ o)) (x, q)) ''
          Set.Icc (0 : ℝ) 1))} := by
  have h1 := boschloo_directionalAcceptedSet_isClosed ha hb n₁ n₂ y₁ y₂
    Sgt hSgt αgt
  have h2 := boschloo_directionalAcceptedSet_isClosed ha hb n₁ n₂ y₁ y₂
    Slt hSlt αlt
  exact (h1.inter h2).isCompact

/-- Blocking theorem 5, instantiated: on a mask-stable stratum (a fixed
`Finset` of outcomes, no indicator jumps) the directional p-value of this
model is fully continuous. -/
theorem boschloo_fixedMask_continuous (ha : 0 < a) (hb : b < 1)
    (n₁ n₂ : ℕ) {mo : ℕ} (y₁ y₂ : Fin mo → ℕ) (R : Finset (Fin mo)) :
    Continuous fun x : ↥(Set.Icc a b) => sSup
      ((fun q => ∑ o ∈ R, stratumMass n₁ n₂ (y₁ o) (y₂ o) (x, q)) ''
        Set.Icc (0 : ℝ) 1) :=
  fixedMaskDirectionalPValue_continuous
    (f := fun x q => ∑ o ∈ R, stratumMass n₁ n₂ (y₁ o) (y₂ o) (x, q))
    (continuous_finsetSum R fun o _ =>
      stratumMass_continuous ha hb n₁ n₂ (y₁ o) (y₂ o))

end Exactcis.Spine
