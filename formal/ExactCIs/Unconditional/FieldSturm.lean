/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SturmSequence
import Mathlib.FieldTheory.RatFunc.Basic

/-! # Algebraic signed-remainder data over characteristic-zero fields

No ordering or specialization homomorphism on the rational-function field is
assumed. Real root semantics are provided by the guarded specialization layer.
-/
namespace ExactCIs.Unconditional.FieldSturm

open Polynomial

variable {K : Type*} [Field K]

inductive Remainders : Polynomial K → Polynomial K → List (Polynomial K) → Prop
  | constant (c : K) (nonzero : c ≠ 0) : Remainders (C c) 0 [C c]
  | step {p q r : Polynomial K} {tail : List (Polynomial K)}
      (quotient : Polynomial K) (identity : p = q * quotient - r)
      (next : Remainders q r tail) : Remainders p q (p :: tail)

theorem Remainders.head {p q : Polynomial K} {ps : List (Polynomial K)}
    (h : Remainders p q ps) : ∃ tail, ps = p :: tail := by
  cases h with
  | constant c hc => exact ⟨[], rfl⟩
  | step quotient identity next => exact ⟨_, rfl⟩

theorem Remainders.shape {p q : Polynomial K} {ps : List (Polynomial K)}
    (h : Remainders p q ps) : (q = 0 ∧ ps = [p]) ∨ ∃ tail, ps = p :: q :: tail := by
  cases h with
  | constant c hc => exact Or.inl ⟨rfl, rfl⟩
  | step quotient identity next =>
    obtain ⟨tail, ht⟩ := next.head
    exact Or.inr ⟨tail, by rw [ht]⟩

theorem constant_remainders {p : Polynomial K} (coprime : IsCoprime p 0) :
    ∃ ps, Remainders p 0 ps := by
  have unit := isCoprime_zero_right.mp coprime
  have hp := eq_C_of_natDegree_eq_zero (natDegree_eq_zero_of_isUnit unit)
  have hc : p.coeff 0 ≠ 0 := by
    intro hc
    have : p = 0 := by simpa [hc] using hp
    exact unit.ne_zero this
  rw [hp]
  exact ⟨_, Remainders.constant _ hc⟩

theorem exists_remainders (p q : Polynomial K) (coprime : IsCoprime p q) :
    ∃ ps, Remainders p q ps := by
  classical
  have go : ∀ n, ∀ p q : Polynomial K, q.natDegree < n → IsCoprime p q →
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
      obtain ⟨tail, ht⟩ : ∃ tail, Remainders q r tail := by
        by_cases hr : r = 0
        · simpa [hr] using constant_remainders (by simpa [hr] using next)
        · have degree : r.natDegree < q.natDegree :=
            natDegree_lt_natDegree hr (by simpa [r] using degree_mod_lt p hq)
          exact ih q.natDegree hn q r degree next
      exact ⟨p :: tail, Remainders.step (p / q) identity ht⟩
  exact go (q.natDegree + 1) p q (Nat.lt_succ_self _) coprime

variable [CharZero K]

theorem exists_squarefree_representative (h : Polynomial K) (nonzero : h ≠ 0) :
    ∃ s : Polynomial K, ∃ n : ℕ, s.Separable ∧ 0 < n ∧ s ∣ h ∧ h ∣ s ^ n := by
  obtain ⟨s, n, hs, hsp, hps⟩ := exists_squarefree_dvd_pow_of_ne_zero nonzero
  exact ⟨s, n + 1, PerfectField.separable_iff_squarefree.mpr hs,
    Nat.succ_pos _, hsp, hps.trans (pow_dvd_pow s (Nat.le_succ n))⟩

/-- All algebraic identities needed before clearing effect denominators. -/
theorem exists_root_data (h : Polynomial K) (nonzero : h ≠ 0) :
    ∃ (s quotient powerQuotient a b : Polynomial K) (n : ℕ)
      (ps : List (Polynomial K)),
      0 < n ∧ s.Separable ∧ h = s * quotient ∧ s ^ n = h * powerQuotient ∧
      a * s + b * s.derivative = 1 ∧ Remainders s s.derivative ps := by
  obtain ⟨s, n, hs, hn, ⟨q, hq⟩, ⟨t, ht⟩⟩ :=
    exists_squarefree_representative h nonzero
  obtain ⟨ps, hp⟩ := exists_remainders s s.derivative hs
  have coprime : IsCoprime s s.derivative := hs
  obtain ⟨a, b, hab⟩ := coprime
  exact ⟨s, q, t, a, b, n, ps, hn, hs, hq, ht, hab, hp⟩

end ExactCIs.Unconditional.FieldSturm
