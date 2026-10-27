/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.FractionFieldClearing

/-! # Finite symbolic root data with a common polynomial scale

This construction takes place before real specialization. A real zero of the
denominator or terminal factor remains an exceptional event, not a generic cell.
-/
namespace ExactCIs.Unconditional.SymbolicRootData

open Polynomial FractionFieldClearing

def ExactChain : List Symbolic → List Symbolic → FunctionField → Prop
  | [p], [], c => p = C c ∧ c ≠ 0
  | [_, p], [], c => p = C c ∧ c ≠ 0
  | p :: q :: r :: ps, a :: qs, c => p = q * a - r ∧ ExactChain (q :: r :: ps) qs c
  | _, _, _ => False

theorem ExactChain.terminal_nonzero (ps qs : List Symbolic) (c : FunctionField)
    (chain : ExactChain ps qs c) : c ≠ 0 := by
  cases ps with
  | nil => simp [ExactChain] at chain
  | cons p ps =>
    cases ps with
    | nil => cases qs <;> simp_all [ExactChain]
    | cons q ps =>
      cases ps with
      | nil => cases qs <;> simp_all [ExactChain]
      | cons r ps =>
        cases qs with
        | nil => simp [ExactChain] at chain
        | cons a qs => exact ExactChain.terminal_nonzero (q :: r :: ps) qs c chain.2
termination_by ps.length

theorem exists_exact_chain {p q : Symbolic} {ps : List Symbolic}
    (prs : FieldSturm.Remainders p q ps) : ∃ qs c, ExactChain ps qs c := by
  induction prs with
  | constant c hc => exact ⟨[], c, rfl, hc⟩
  | @step p q r ps a identity next ih =>
    obtain ⟨qs, c, chain⟩ := ih
    rcases next.shape with ⟨_, shape⟩ | ⟨tail, shape⟩
    · rw [shape] at chain ⊢
      cases qs with
      | nil => exact ⟨[], c, chain⟩
      | cons _ _ => simp [ExactChain] at chain
    · rw [shape] at chain ⊢
      exact ⟨a :: qs, c, identity, chain⟩

def ScaledChain (D E : Effect) : List Integral → List Integral → Prop
  | [p], [] => p = C E
  | [_, p], [] => p = C E
  | p :: q :: r :: ps, a :: qs =>
      C D * p = q * a - C D * r ∧ ScaledChain D E (q :: r :: ps) qs
  | _, _ => False

theorem cleared_constant {D : Effect} {P : Integral} {c : FunctionField}
    (cleared : P.map embed = C (embed D) * C c) :
    P = C (P.coeff 0) ∧ embed (P.coeff 0) = embed D * c := by
  have coefficient : embed (P.coeff 0) = embed D * c := by
    have h := congrArg (fun p : Symbolic => p.coeff 0) cleared
    simpa only [coeff_map, ← map_mul, coeff_C, ite_true] using h
  refine ⟨?_, coefficient⟩
  apply FractionFieldClearing.map_injective
  rw [cleared, Polynomial.map_C, coefficient, map_mul]

theorem clear_chain (D E : Effect) (lift : Symbolic → Integral)
    (ps qs : List Symbolic) (c : FunctionField)
    (chain : ExactChain ps qs c)
    (cleared : ∀ p ∈ ps ++ qs, (lift p).map embed = C (embed D) * p)
    (terminal : lift (C c) = C E) :
    ScaledChain D E (ps.map lift) (qs.map lift) := by
  cases ps with
  | nil => simp [ExactChain] at chain
  | cons p ps =>
    cases ps with
    | nil =>
      cases qs with
      | cons _ _ => simp [ExactChain] at chain
      | nil => simpa only [List.map_cons, List.map_nil, ScaledChain, chain.1] using terminal
    | cons q ps =>
      cases ps with
      | nil =>
        cases qs with
        | cons _ _ => simp [ExactChain] at chain
        | nil => simpa only [List.map_cons, List.map_nil, ScaledChain, chain.1] using terminal
      | cons r ps =>
        cases qs with
        | nil => simp [ExactChain] at chain
        | cons a qs =>
          refine ⟨cleared_recurrence (cleared p (by simp)) (cleared q (by simp))
            (cleared r (by simp)) (cleared a (by simp)) chain.1, ?_⟩
          exact clear_chain D E lift (q :: r :: ps) qs c chain.2
            (fun f hf => cleared f (by
              simp only [List.mem_append, List.mem_cons] at hf ⊢; tauto)) terminal
termination_by ps.length

structure Packet (H : Integral) where
  denominator : Effect
  terminal : Effect
  representative : Integral
  quotient : Integral
  powerQuotient : Integral
  bezoutLeft : Integral
  bezoutRight : Integral
  exponent : ℕ
  tail : List Integral
  quotients : List Integral
  denominator_ne_zero : denominator ≠ 0
  terminal_ne_zero : terminal ≠ 0
  exponent_pos : 0 < exponent
  root_identity : C (denominator ^ 2) * H = representative * quotient
  power_identity : C denominator * representative ^ exponent =
    H * (C (denominator ^ exponent) * powerQuotient)
  bezout_identity : bezoutLeft * representative + bezoutRight * representative.derivative =
    C (denominator ^ 2)
  chain : ScaledChain denominator terminal (representative :: tail) quotients
  first : ∀ p ∈ tail.head?, p = representative.derivative

/-- Every nonzero bivariate rational polynomial has finite algebraic root data
whose only common scales and terminal factor are nonzero effect polynomials. -/
theorem exists_packet (H : Integral) (nonzero : H ≠ 0) : Nonempty (Packet H) := by
  classical
  have hH : H.map embed ≠ 0 := fun hz =>
    nonzero (FractionFieldClearing.map_injective (by simpa using hz))
  obtain ⟨s, q, t, a, b, n, ps, hn, hs, hq, ht, hab, prs⟩ :=
    FieldSturm.exists_root_data (H.map embed) hH
  obtain ⟨qs, c, chain⟩ := exists_exact_chain prs
  let family := (ps ++ qs ++ [s, q, t, a, b, C c]).toFinset
  obtain ⟨D, hD, clear⟩ := exists_common_denominator family
  let lift (p : Symbolic) : Integral := if hp : p ∈ family then (clear p hp).choose else 0
  have clearing : ∀ p ∈ family, (lift p).map embed = C (embed D) * p := by
    intro p hp
    simpa only [lift, dif_pos hp] using (clear p hp).choose_spec
  have members (p : Symbolic) (hp : p ∈ [s, q, t, a, b, C c]) : p ∈ family := by
    simp only [family, List.mem_toFinset, List.mem_append]
    tauto
  have hc : c ≠ 0 := ExactChain.terminal_nonzero ps qs c chain
  have last_clear := clearing (C c) (members _ (by simp))
  obtain ⟨last_constant, last_coefficient⟩ := cleared_constant last_clear
  have last_nonzero : (lift (C c)).coeff 0 ≠ 0 := by
    intro zero
    rw [zero, map_zero] at last_coefficient
    exact (mul_ne_zero (fun hz => hD (embed_injective (by simpa using hz))) hc)
      last_coefficient.symm
  obtain ⟨rest, shape⟩ := prs.head
  have head_clear := clearing s (members _ (by simp))
  have first : ∀ p ∈ (rest.map lift).head?, p = (lift s).derivative := by
    rcases prs.shape with ⟨_, single⟩ | ⟨tail, pair⟩
    · have : rest = [] := by simpa only [shape, List.cons.injEq, true_and] using single
      simp [this]
    · have : rest = s.derivative :: tail := by
        simpa only [shape, List.cons.injEq, true_and] using pair
      simp only [this, List.map_cons, List.head?_cons, Option.mem_def, Option.some.injEq]
      intro p hp
      subst p
      apply FractionFieldClearing.map_injective
      rw [clearing _ (by simp only [family, List.mem_toFinset, shape, this,
        List.mem_append, List.mem_cons]; tauto), cleared_derivative head_clear]
  refine ⟨⟨D, (lift (C c)).coeff 0, lift s, lift q, lift t, lift a, lift b,
    n, rest.map lift, qs.map lift, hD, last_nonzero, hn,
    cleared_root_identity head_clear (clearing _ (members _ (by simp))) hq,
    cleared_power_identity head_clear (clearing _ (members _ (by simp))) ht,
    cleared_bezout_identity head_clear (clearing _ (members _ (by simp)))
      (clearing _ (members _ (by simp))) hab, ?_, first⟩⟩
  have result := clear_chain D _ lift ps qs c chain
    (fun p hp => clearing p (by
      simp only [family, List.mem_toFinset, List.mem_append] at *; tauto)) last_constant
  simpa only [shape, List.map_cons] using result

end ExactCIs.Unconditional.SymbolicRootData
