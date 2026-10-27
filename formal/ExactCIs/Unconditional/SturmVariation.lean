/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import Mathlib

/-! # Zero-skipping variations and local Sturm-chain behavior -/
namespace ExactCIs.Unconditional.SturmVariation

open Filter Topology

def changesFrom (previous : SignType) : List SignType → ℕ
  | [] => 0
  | s :: ss => if s = 0 then changesFrom previous ss else
      (if previous = 0 ∨ previous = s then 0 else 1) + changesFrom s ss

def variations (ss : List SignType) : ℕ := changesFrom 0 ss

theorem variations_zero (ss : List SignType) : variations (0 :: ss) = variations ss := by
  simp [variations, changesFrom]

theorem variations_pair (a b : SignType) (ss : List SignType) (hb : b ≠ 0) :
    variations (a :: b :: ss) = (if a = 0 ∨ a = b then 0 else 1) +
      variations (b :: ss) := by
  cases a <;> cases b <;> simp_all [variations, changesFrom]

/-- A possibly zero middle entry between opposite nonzero signs contributes one. -/
theorem variations_opposite (a b c : SignType) (ss : List SignType)
    (opposite : a = -c) (hc : c ≠ 0) :
    variations (a :: b :: c :: ss) = 1 + variations (c :: ss) := by
  cases a <;> cases b <;> cases c <;> simp_all [variations, changesFrom]

noncomputable def variationAt (ps : List (ℝ → ℝ)) (x : ℝ) : ℕ :=
  variations (ps.map (fun p => SignType.sign (p x)))

/-- Continuous chain, a nowhere-zero final entry, and opposite neighbors at
each internal zero. The first entry may have roots. -/
def Chain : List (ℝ → ℝ) → Prop
  | [] => False
  | [p] => Continuous p ∧ ∀ x, p x ≠ 0
  | p :: q :: tail => Continuous p ∧ Chain (q :: tail) ∧
      match tail with
      | [] => True
      | r :: _ => ∀ x, q x = 0 → p x * r x < 0

theorem Chain.continuous_head {p : ℝ → ℝ} {ps : List (ℝ → ℝ)}
    (h : Chain (p :: ps)) : Continuous p := by
  cases ps <;> exact h.1

theorem Chain.tail {p q : ℝ → ℝ} {ps : List (ℝ → ℝ)}
    (h : Chain (p :: q :: ps)) : Chain (q :: ps) := h.2.1

theorem Chain.no_common_root {p q : ℝ → ℝ} {ps : List (ℝ → ℝ)}
    (h : Chain (p :: q :: ps)) {x : ℝ} (hp : p x = 0) : q x ≠ 0 := by
  cases ps with
  | nil => exact h.2.1.2 x
  | cons r rs =>
    intro hq
    have := h.2.2 x hq
    simp [hp] at this

theorem sign_stable {f : ℝ → ℝ} (hf : Continuous f) {x : ℝ} (hx : f x ≠ 0) :
    ∀ᶠ y in 𝓝 x, SignType.sign (f y) = SignType.sign (f x) := by
  have hc := (continuousAt_sign_of_ne_zero hx).comp hf.continuousAt
  exact hc.eventually (isOpen_discrete {SignType.sign (f x)} |>.mem_nhds (by simp))

theorem opposite_signs {a b : ℝ} (h : a * b < 0) :
    SignType.sign a = -SignType.sign b ∧ SignType.sign b ≠ 0 := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · simp [sign_pos ha, sign_neg hb]
  · simp [sign_neg ha, sign_pos hb]

/-- Internal chain zeros do not change the variation count. -/
theorem locally_constant_of_head {p : ℝ → ℝ} {ps : List (ℝ → ℝ)}
    (h : Chain (p :: ps)) {x : ℝ} (hp : p x ≠ 0) :
    ∀ᶠ y in 𝓝 x, variationAt (p :: ps) y = variationAt (p :: ps) x := by
  cases ps with
  | nil =>
    apply Filter.Eventually.of_forall
    intro y
    simp [variationAt, variations, changesFrom]
  | cons q qs =>
    by_cases hq : q x = 0
    · cases qs with
      | nil => exact False.elim (h.2.1.2 x hq)
      | cons r rs =>
        have opp := opposite_signs (h.2.2 x hq)
        have hr : r x ≠ 0 := by simpa using opp.2
        have hrec := locally_constant_of_head h.tail.tail hr
        filter_upwards [hrec, sign_stable h.continuous_head hp,
          sign_stable h.tail.tail.continuous_head hr] with y hy hpy hry
        change variations (SignType.sign (p y) :: SignType.sign (q y) ::
          SignType.sign (r y) :: rs.map (fun f => SignType.sign (f y))) = _
        rw [variations_opposite _ _ _ _ (by simpa [hpy, hry] using opp.1)
          (by simpa [hry] using opp.2)]
        change 1 + variationAt (r :: rs) y = _
        rw [hy]
        exact (variations_opposite _ _ _ _ opp.1 opp.2).symm
    · have hrec := locally_constant_of_head h.tail hq
      filter_upwards [hrec, sign_stable h.continuous_head hp,
        sign_stable h.tail.continuous_head hq] with y hy hpy hqy
      have hxq : SignType.sign (q x) ≠ 0 := by simpa using hq
      have hyq : SignType.sign (q y) ≠ 0 := by simpa [hqy] using hxq
      change variations (SignType.sign (p y) :: SignType.sign (q y) ::
        qs.map (fun f => SignType.sign (f y))) = _
      rw [variations_pair _ _ _ hyq]
      change (if SignType.sign (p y) = 0 ∨ SignType.sign (p y) = SignType.sign (q y)
        then 0 else 1) + variationAt (q :: qs) y = _
      rw [hy, hpy, hqy]
      exact (variations_pair _ _ _ hxq).symm
termination_by ps.length

/-- At a root, the variation is right-continuous and is one larger to its left. -/
theorem root_drop {p q : ℝ → ℝ} {ps : List (ℝ → ℝ)}
    (chain : Chain (p :: q :: ps)) (derivative : ∀ x, HasDerivAt p (q x) x)
    {x : ℝ} (root : p x = 0) :
    ∀ᶠ y in 𝓝 x, variationAt (p :: q :: ps) y =
      variationAt (p :: q :: ps) x + if y < x then 1 else 0 := by
  have hq := chain.no_common_root root
  have hxq : SignType.sign (q x) ≠ 0 := by simpa using hq
  have tailStable := locally_constant_of_head chain.tail hq
  have qStable := sign_stable chain.tail.continuous_head hq
  have atRoot : variationAt (p :: q :: ps) x = variationAt (q :: ps) x := by
    simp [variationAt, root, variations_zero]
  rcases hq.lt_or_gt with negative | positive
  · have near := eventually_nhdsWithin_sign_eq_of_deriv_neg
      (by simpa only [(derivative x).deriv] using negative) root
    filter_upwards [tailStable, qStable, near] with y ht hqy hpy
    change variations (SignType.sign (p y) :: SignType.sign (q y) ::
      ps.map (fun f => SignType.sign (f y))) = _
    rw [variations_pair _ _ _ (by simpa [hqy] using hxq)]
    change (if SignType.sign (p y) = 0 ∨ SignType.sign (p y) = SignType.sign (q y)
      then 0 else 1) + variationAt (q :: ps) y = _
    rw [ht, hqy, hpy, atRoot, sign_neg negative]
    rcases lt_trichotomy y x with hy | hy | hy
    · simp [sign_pos (sub_pos.mpr hy), hy, Nat.add_comm]
    · subst y; simp
    · simp [sign_neg (sub_neg.mpr hy), hy.not_gt]
  · have near := eventually_nhdsWithin_sign_eq_of_deriv_pos
      (by simpa only [(derivative x).deriv] using positive) root
    filter_upwards [tailStable, qStable, near] with y ht hqy hpy
    change variations (SignType.sign (p y) :: SignType.sign (q y) ::
      ps.map (fun f => SignType.sign (f y))) = _
    rw [variations_pair _ _ _ (by simpa [hqy] using hxq)]
    change (if SignType.sign (p y) = 0 ∨ SignType.sign (p y) = SignType.sign (q y)
      then 0 else 1) + variationAt (q :: ps) y = _
    rw [ht, hqy, hpy, atRoot, sign_pos positive]
    rcases lt_trichotomy y x with hy | hy | hy
    · simp [sign_neg (sub_neg.mpr hy), hy, Nat.add_comm]
    · subst y; simp
    · simp [sign_pos (sub_pos.mpr hy), hy.not_gt]

end ExactCIs.Unconditional.SturmVariation
