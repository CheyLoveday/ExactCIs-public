/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SturmVariation

/-! # Existence and chain semantics of finite exact signed remainders -/
namespace ExactCIs.Unconditional.SturmSequence

open Polynomial SturmVariation

noncomputable def realValue (p : Polynomial ℚ) : ℝ → ℝ :=
  (p.map (Rat.castHom ℝ)).eval

theorem realValue_continuous (p : Polynomial ℚ) : Continuous (realValue p) :=
  (p.map (Rat.castHom ℝ)).continuous

/-- Quotient identities retain the minus sign of each signed remainder. -/
inductive Remainders : Polynomial ℚ → Polynomial ℚ → List (Polynomial ℚ) → Prop
  | constant (c : ℚ) (nonzero : c ≠ 0) : Remainders (C c) 0 [C c]
  | step {p q r : Polynomial ℚ} {tail : List (Polynomial ℚ)}
      (quotient : Polynomial ℚ) (identity : p = q * quotient - r)
      (next : Remainders q r tail) : Remainders p q (p :: tail)

theorem Remainders.head {p q : Polynomial ℚ} {ps : List (Polynomial ℚ)}
    (h : Remainders p q ps) : ∃ tail, ps = p :: tail := by
  cases h with
  | constant c hc => exact ⟨[], rfl⟩
  | step quotient identity next => exact ⟨_, rfl⟩

theorem Remainders.shape {p q : Polynomial ℚ} {ps : List (Polynomial ℚ)}
    (h : Remainders p q ps) : (q = 0 ∧ ps = [p]) ∨ ∃ tail, ps = p :: q :: tail := by
  cases h with
  | constant c hc => exact Or.inl ⟨rfl, rfl⟩
  | step quotient identity next =>
    obtain ⟨tail, ht⟩ := next.head
    exact Or.inr ⟨tail, by rw [ht]⟩

theorem Remainders.chain {p q : Polynomial ℚ} {ps : List (Polynomial ℚ)}
    (h : Remainders p q ps) : Chain (ps.map realValue) := by
  induction h with
  | constant c hc =>
    change Continuous (realValue (C c)) ∧ ∀ x, realValue (C c) x ≠ 0
    refine ⟨realValue_continuous _, ?_⟩
    intro x
    simpa [realValue] using (Rat.cast_ne_zero.mpr hc : (c : ℝ) ≠ 0)
  | @step p q r tail quotient identity next ih =>
    rcases next.shape with ⟨_, ht⟩ | ⟨rs, ht⟩
    · rw [ht] at ih ⊢
      exact ⟨realValue_continuous p, ih, trivial⟩
    · rw [ht] at ih ⊢
      refine ⟨realValue_continuous p, ih, ?_⟩
      intro x hq
      have hr := ih.no_common_root hq
      have he : realValue p x = realValue q x * realValue quotient x - realValue r x := by
        rw [identity]
        simp [realValue]
      rw [hq, zero_mul, zero_sub] at he
      rw [he]
      nlinarith [sq_pos_of_ne_zero hr]

theorem constant_remainders {p : Polynomial ℚ} (coprime : IsCoprime p 0) :
    ∃ ps, Remainders p 0 ps := by
  have unit := isCoprime_zero_right.mp coprime
  have hp := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit unit)
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    have : p = 0 := by simpa [hc] using hp
    exact unit.ne_zero this
  rw [hp]
  exact ⟨_, Remainders.constant _ hc⟩

/-- Every coprime rational pair has a finite exact signed remainder witness. -/
theorem exists_remainders (p q : Polynomial ℚ) (coprime : IsCoprime p q) :
    ∃ ps, Remainders p q ps := by
  classical
  have go : ∀ n, ∀ p q : Polynomial ℚ, q.natDegree < n → IsCoprime p q →
      ∃ ps, Remainders p q ps := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro p q hn hpq
      by_cases hq : q = 0
      · subst q; exact constant_remainders hpq
      let r := -(p % q)
      have identity : p = q * (p / q) - r := by
        dsimp [r]
        simpa using (EuclideanDomain.div_add_mod p q).symm
      have next : IsCoprime q r := by
        obtain ⟨a, b, hab⟩ := hpq
        refine ⟨a * (p / q) + b, -a, ?_⟩
        calc
          (a * (p / q) + b) * q + -a * r = a * p + b * q := by
            conv_rhs => rw [identity]
            ring
          _ = 1 := hab
      have witness : ∃ tail, Remainders q r tail := by
        by_cases hr : r = 0
        · simpa [hr] using constant_remainders (by simpa [hr] using next)
        · have degree : r.natDegree < q.natDegree :=
            natDegree_lt_natDegree hr (by simpa [r] using degree_mod_lt p hq)
          exact ih q.natDegree hn q r degree next
      obtain ⟨tail, ht⟩ := witness
      exact ⟨p :: tail, Remainders.step (p / q) identity ht⟩
  exact go (q.natDegree + 1) p q (Nat.lt_succ_self _) coprime

theorem exists_squarefree_representative (p : Polynomial ℚ) (nonzero : p ≠ 0) :
    ∃ s : Polynomial ℚ, ∃ n : ℕ, s.Separable ∧ 0 < n ∧ s ∣ p ∧ p ∣ s ^ n := by
  obtain ⟨s, n, hs, hsp, hps⟩ := exists_squarefree_dvd_pow_of_ne_zero nonzero
  refine ⟨s, n + 1, PerfectField.separable_iff_squarefree.mpr hs,
    Nat.succ_pos _, hsp, ?_⟩
  exact hps.trans (pow_dvd_pow s (Nat.le_succ n))

end ExactCIs.Unconditional.SturmSequence
