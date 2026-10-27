/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.FieldSturm
import Mathlib.RingTheory.Localization.Integral

/-! # One denominator for finite rational-function polynomial data

The denominator is nonzero as a polynomial. Its real roots remain exceptional
effects and must be excluded before using the cleared identities semantically.
-/
namespace ExactCIs.Unconditional.FractionFieldClearing

open Polynomial

abbrev Effect := Polynomial ℚ
abbrev FunctionField := RatFunc ℚ
abbrev Symbolic := Polynomial FunctionField
abbrev Integral := Polynomial Effect

noncomputable def embed : Effect →+* FunctionField := algebraMap Effect FunctionField

theorem embed_injective : Function.Injective embed := RatFunc.algebraMap_injective ℚ

theorem exists_denominator (p : Symbolic) :
    ∃ D : Effect, D ≠ 0 ∧ ∃ P : Integral, P.map embed = C (embed D) * p := by
  obtain ⟨D, hD, hP⟩ :=
    IsLocalization.integerNormalization_spec (nonZeroDivisors Effect) p
  refine ⟨D, nonZeroDivisors.ne_zero hD,
    IsLocalization.integerNormalization (nonZeroDivisors Effect) p, ?_⟩
  simpa only [embed, ← algebraMap_smul FunctionField D p, smul_eq_C_mul] using hP

/-- A single nonzero scale clears every polynomial in a finite family. -/
theorem exists_common_denominator (ps : Finset Symbolic) :
    ∃ D : Effect, D ≠ 0 ∧ ∀ p ∈ ps, ∃ P : Integral,
      P.map embed = C (embed D) * p := by
  classical
  induction ps using Finset.induction_on with
  | empty => exact ⟨1, one_ne_zero, by simp⟩
  | @insert p ps absent ih =>
    obtain ⟨d, hd, P, hP⟩ := exists_denominator p
    obtain ⟨e, he, rest⟩ := ih
    refine ⟨d * e, mul_ne_zero hd he, ?_⟩
    intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · refine ⟨C e * P, ?_⟩
      simp only [Polynomial.map_mul, Polynomial.map_C, hP, map_mul]
      ring
    · obtain ⟨Q, hQ⟩ := rest q hq
      refine ⟨C d * Q, ?_⟩
      simp only [Polynomial.map_mul, Polynomial.map_C, hQ, map_mul]
      ring

theorem map_injective : Function.Injective (Polynomial.map embed) :=
  Polynomial.map_injective embed embed_injective

/-- Clearing the same scale on successive entries preserves the negative
remainder, with two identical recurrence scales. Their product is a square. -/
theorem cleared_recurrence {D : Effect} {P Q R A : Integral}
    {p q r a : Symbolic}
    (hp : P.map embed = C (embed D) * p)
    (hq : Q.map embed = C (embed D) * q)
    (hr : R.map embed = C (embed D) * r)
    (ha : A.map embed = C (embed D) * a)
    (identity : p = q * a - r) : C D * P = Q * A - C D * R := by
  apply map_injective
  simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C, hp, hq, hr, ha]
  rw [identity]
  ring

/-- The nuisance derivative commutes with a scale depending only on effect. -/
theorem cleared_derivative {D : Effect} {P : Integral} {p : Symbolic}
    (hp : P.map embed = C (embed D) * p) :
    P.derivative.map embed = C (embed D) * p.derivative := by
  rw [← Polynomial.derivative_map, hp]
  simp

theorem cleared_root_identity {D : Effect} {H S Q : Integral} {s q : Symbolic}
    (hs : S.map embed = C (embed D) * s)
    (hq : Q.map embed = C (embed D) * q)
    (identity : H.map embed = s * q) : C (D ^ 2) * H = S * Q := by
  apply map_injective
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, map_pow, hs, hq,
    identity]
  ring

theorem cleared_power_identity {D : Effect} {H S T : Integral} {s t : Symbolic} {n : ℕ}
    (hs : S.map embed = C (embed D) * s)
    (ht : T.map embed = C (embed D) * t)
    (identity : s ^ n = H.map embed * t) :
    C D * S ^ n = H * (C (D ^ n) * T) := by
  apply map_injective
  simp only [Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, map_pow, hs, ht]
  rw [mul_pow, identity]
  ring

theorem cleared_bezout_identity {D : Effect} {S A B : Integral} {s a b : Symbolic}
    (hs : S.map embed = C (embed D) * s)
    (ha : A.map embed = C (embed D) * a)
    (hb : B.map embed = C (embed D) * b)
    (identity : a * s + b * s.derivative = 1) :
    A * S + B * S.derivative = C (D ^ 2) := by
  apply map_injective
  simp only [Polynomial.map_add, Polynomial.map_mul, Polynomial.map_C, Polynomial.map_pow, map_pow,
    hs, ha, hb, cleared_derivative hs]
  calc
    _ = C (embed D) ^ 2 * (a * s + b * s.derivative) := by ring
    _ = _ := by rw [identity, mul_one]

end ExactCIs.Unconditional.FractionFieldClearing
