import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.ConditionallyCompletePartialOrder.Basic
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Interval hull: the T1-min endpoint-excess theorem

Spine module `IntervalHull` (devplan 22 §11; devplans 24–26, P29).

**T1-min** (derivation A §3.3, confirmed by the cross-attack in devplan 26):
four certified numbers — `sInf O`, `sSup O`, `sInf I`, `sSup I` — with the
inclusions `I ⊆ A ⊆ O` and two fringe comparisons certify the returned hull
`[b (sInf O), b (sSup O)]` to endpoint excess `ε` — with **no component
identification, no matching, and no H4 hypothesis of any kind**. Component
matching is the *refinement strategy* that drives the certified extents
together; it is not the soundness condition of the returned hull.

`b` is the monotone effect-coordinate transport `s ↦ β` (`b = s/(1-s)` in
the model); the fringe hypotheses are stated in the transported (β) scale
exactly as the contract requires (devplan 25 §T6: an `s`-scale fringe of
any width touching `s = 1` is infinite in `β`, so the β-scale phrasing is
load-bearing, not cosmetic).

Attainment of `inf A` is **not** consumed by these inequalities — the
u.s.c./compactness chain (`AcceptedSetTopology`) is spent on the semantics
(attained, genuinely accepted endpoints) and on certificate soundness, not
on the hull arithmetic. Recorded per devplan 24 §"compactness ledger".
-/

namespace Exactcis.Spine

open Set

section T1min

variable {A O I : Set ℝ} {b : ℝ → ℝ} {ε : ℝ}

/-- Hull conservativity: `A ⊆ O` places every accepted point (after the
monotone transport `b`) inside `[b (sInf O), b (sSup O)]`. -/
theorem hull_conservative (hb : Monotone b) (hAO : A ⊆ O)
    (hObelow : BddBelow O) (hOabove : BddAbove O) :
    ∀ a ∈ A, b (sInf O) ≤ b a ∧ b a ≤ b (sSup O) := fun a ha =>
  ⟨hb (csInf_le hObelow (hAO ha)), hb (le_csSup hOabove (hAO ha))⟩

/-- T1-min, lower endpoint: `sInf O ≤ sInf A ≤ sInf I` from the inclusions
alone, and the certified fringe `b (sInf I) - b (sInf O) ≤ ε` then brackets
the transported lower endpoint of `A` to excess `ε`. -/
theorem t1min_lower_endpoint (hb : Monotone b) (hAO : A ⊆ O) (hIA : I ⊆ A)
    (hI : I.Nonempty) (hObelow : BddBelow O)
    (hfringe : b (sInf I) - b (sInf O) ≤ ε) :
    0 ≤ b (sInf A) - b (sInf O) ∧ b (sInf A) - b (sInf O) ≤ ε := by
  have hAne : A.Nonempty := hI.mono hIA
  have h₁ : sInf O ≤ sInf A := csInf_le_csInf hObelow hAne hAO
  have h₂ : sInf A ≤ sInf I :=
    csInf_le_csInf (hObelow.mono hAO) hI hIA
  exact ⟨by linarith [hb h₁], by linarith [hb h₂]⟩

/-- T1-min, upper endpoint: mirror of `t1min_lower_endpoint`. -/
theorem t1min_upper_endpoint (hb : Monotone b) (hAO : A ⊆ O) (hIA : I ⊆ A)
    (hI : I.Nonempty) (hOabove : BddAbove O)
    (hfringe : b (sSup O) - b (sSup I) ≤ ε) :
    0 ≤ b (sSup O) - b (sSup A) ∧ b (sSup O) - b (sSup A) ≤ ε := by
  have hAne : A.Nonempty := hI.mono hIA
  have h₁ : sSup A ≤ sSup O := csSup_le_csSup hOabove hAne hAO
  have h₂ : sSup I ≤ sSup A :=
    csSup_le_csSup (hOabove.mono hAO) hI hIA
  exact ⟨by linarith [hb h₁], by linarith [hb h₂]⟩

/-- **T1-min packaged** (the P29 formalisation target): under

* certificate soundness `I ⊆ A ⊆ O` (H1, H2⁻),
* nonempty certified inner content (H2⁻),
* certified extents (`O` bounded), and
* the two β-scale fringe checks (H3-global) —

the returned hull `[b (sInf O), b (sSup O)]` contains the transport of
every accepted point, and both endpoints are within `ε` of the transported
`inf A` / `sup A`. Five certified numbers, no components, no matching. -/
theorem t1min (hb : Monotone b) (hAO : A ⊆ O) (hIA : I ⊆ A)
    (hI : I.Nonempty) (hObelow : BddBelow O) (hOabove : BddAbove O)
    (hfl : b (sInf I) - b (sInf O) ≤ ε)
    (hfu : b (sSup O) - b (sSup I) ≤ ε) :
    (∀ a ∈ A, b (sInf O) ≤ b a ∧ b a ≤ b (sSup O)) ∧
    (0 ≤ b (sInf A) - b (sInf O) ∧ b (sInf A) - b (sInf O) ≤ ε) ∧
    (0 ≤ b (sSup O) - b (sSup A) ∧ b (sSup O) - b (sSup A) ≤ ε) :=
  ⟨hull_conservative hb hAO hObelow hOabove,
   t1min_lower_endpoint hb hAO hIA hI hObelow hfl,
   t1min_upper_endpoint hb hAO hIA hI hOabove hfu⟩

end T1min

/-! ## Necessity of the fringe hypotheses

The two dropped-hypothesis counterexamples from devplan 24 §9.2 /
devplan 25 §T1, machine-checked: with the left fringe check dropped, the
returned lower endpoint can sit a fixed distance `0.4` below `inf A`
however small `ε` is. (`b = id`; `O = [0, 1/2]`, `I = {1/2}`,
`A = [2/5, 1/2]`.) -/

/-- Dropping H3 (the fringe check) breaks the endpoint bound: the F1
fringe-stacking failure realised inside a single certified component. -/
example :
    ∃ (A O I : Set ℝ), I ⊆ A ∧ A ⊆ O ∧ I.Nonempty ∧ BddBelow O ∧
      sInf A - sInf O = 2/5 := by
  refine ⟨Set.Icc (2/5) (1/2), Set.Icc 0 (1/2), {(1/2 : ℝ)}, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    rw [Set.mem_Icc]
    constructor <;> norm_num
  · exact Set.Icc_subset_Icc (by norm_num) le_rfl
  · exact Set.singleton_nonempty _
  · exact bddBelow_Icc
  · rw [csInf_Icc (by norm_num : (2:ℝ)/5 ≤ 1/2),
      csInf_Icc (by norm_num : (0:ℝ) ≤ 1/2)]
    norm_num

end Exactcis.Spine
