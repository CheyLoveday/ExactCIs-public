/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.SymbolicRootData
import ExactCIs.Unconditional.BivariateEncoding
import ExactCIs.Unconditional.OpenStrata
import ExactCIs.Unconditional.ParametricRootCertificate

/-! # Existence of accepted parametric packets away from finite exceptions

Encoders below are mathematical choices, not a runtime generation algorithm.
No assertion is made at a zero of either exceptional polynomial.
-/
namespace ExactCIs.Unconditional.ParametricGeneration

open Polynomial AlgebraicSpecialization FractionFieldClearing SymbolicRootData

noncomputable def encode (p : Integral) : Bivariate :=
  (BivariateEncoding.exists_bivariate p).choose

theorem encode_spec (p : Integral) : BivariateEncoding.polynomial (encode p) = p :=
  (BivariateEncoding.exists_bivariate p).choose_spec

noncomputable def coefficients (p : Effect) : RootCertificate.Coefficients :=
  (PolynomialList.exists_coefficients p).choose

theorem coefficients_spec (p : Effect) : PolynomialList.polynomial (coefficients p) = p :=
  (PolynomialList.exists_coefficients p).choose_spec

theorem eval_coefficients (p : Effect) (x : ℝ) :
    RootCertificate.eval (coefficients p) x = BoschlooOrdering.realEval p x := by
  rw [← PolynomialList.polynomial_eval, coefficients_spec]
  simp only [BoschlooOrdering.realEval, Polynomial.eval_map]

/-- Strict nonvanishing on the entire connected closed cell supplies the
checker witness; a sample alone is not the premise. -/
theorem nonzero_witness_complete (d : RootCertificate.Coefficients) (l u : ℚ)
    (order : l ≤ u)
    (no_zero : ∀ x ∈ Set.Icc (l : ℝ) u, RootCertificate.eval d x ≠ 0) :
    ∃ w, StratumSignReplay.nonzeroCheck d l u w = true := by
  have left : (l : ℝ) ∈ Set.Icc (l : ℝ) u := ⟨le_rfl, by exact_mod_cast order⟩
  have eval_eq (x : ℝ) : RootCertificate.eval d x =
      BoschlooOrdering.realEval (PolynomialList.polynomial d) x := by
    rw [← PolynomialList.polynomial_eval]
    simp only [BoschlooOrdering.realEval, Polynomial.eval_map]
  have same (x : ℝ) (hx : x ∈ Set.Icc (l : ℝ) u) :
      RootCertificate.eval d l ≤ 0 ↔ RootCertificate.eval d x ≤ 0 := by
    simpa only [eval_eq] using BoschlooOrdering.polynomial_sign_constant
      (PolynomialList.polynomial d) isPreconnected_Icc
      (fun y hy => by simpa only [← eval_eq] using no_zero y hy) left hx
  rcases lt_or_gt_of_ne (no_zero l left) with negative | positive
  · obtain ⟨c, hc⟩ := OpenStrata.negative_certificate d l u order
      (fun x hx => lt_of_le_of_ne ((same x hx).mp negative.le) (no_zero x hx))
    exact ⟨⟨false, c⟩, by simp [StratumSignReplay.nonzeroCheck,
      StratumSignReplay.signCheck, hc]⟩
  · have signs : ∀ x ∈ Set.Icc (l : ℝ) u,
        RootCertificate.eval (RootCertificate.scale (-1) d) x < 0 := by
      intro x hx
      have hp : 0 < RootCertificate.eval d x :=
        lt_of_not_ge (fun h => not_le.mpr positive ((same x hx).mpr h))
      simpa only [RootCertificate.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
        neg_lt_zero] using hp
    obtain ⟨c, hc⟩ := OpenStrata.negative_certificate _ l u order signs
    exact ⟨⟨true, c⟩, by simp [StratumSignReplay.nonzeroCheck,
      StratumSignReplay.signCheck, hc]⟩

theorem step_accepted (D : Effect) (p q r a : Integral) (l u : ℚ)
    (w : StratumSignReplay.SignWitness) (sign : w.sign = 1)
    (checked : StratumSignReplay.signCheck
      (RootCertificate.mul (coefficients D) (coefficients D)) l u w = true)
    (identity : C D * p = q * a - C D * r) :
    ParametricRootCertificate.stepCheck l u (encode p) (encode q) (encode r)
      ⟨encode a, coefficients D, coefficients D, w⟩ = true := by
  simp only [ParametricRootCertificate.stepCheck, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨BivariateEncoding.identityCheck_complete _ _ ?_, sign⟩, checked⟩
  simp only [BivariateEncoding.polynomial_scale, BivariateEncoding.polynomial_add,
    BivariateEncoding.polynomial_mul, encode_spec, coefficients_spec,
    PolynomialList.polynomial_scale, map_neg, map_one, neg_one_mul]
  simpa only [map_neg, neg_mul, sub_eq_add_neg] using identity

theorem chain_accepted (D E : Effect) (ps qs : List Integral) (l u : ℚ)
    (w : StratumSignReplay.SignWitness) (sign : w.sign = 1)
    (square_checked : StratumSignReplay.signCheck
      (RootCertificate.mul (coefficients D) (coefficients D)) l u w = true)
    (last : StratumSignReplay.NonzeroWitness)
    (last_checked : StratumSignReplay.nonzeroCheck (coefficients E) l u last = true)
    (chain : ScaledChain D E ps qs) :
    ParametricRootCertificate.chainCheck l u (coefficients E) last (ps.map encode)
      (qs.map fun a => ⟨encode a, coefficients D, coefficients D, w⟩) = true := by
  cases ps with
  | nil => simp [ScaledChain] at chain
  | cons p ps =>
    cases ps with
    | nil =>
      cases qs with
      | cons _ _ => simp [ScaledChain] at chain
      | nil =>
        change p = C E at chain
        have identity : StratumSignReplay.identityCheck (encode p) [coefficients E] = true := by
          apply BivariateEncoding.identityCheck_complete
          simpa only [encode_spec, BivariateEncoding.polynomial, coefficients_spec,
            mul_zero, add_zero] using chain
        simp only [List.map_cons, List.map_nil, ParametricRootCertificate.chainCheck,
          identity, last_checked, Bool.true_and]
    | cons q ps =>
      cases ps with
      | nil =>
        cases qs with
        | cons _ _ => simp [ScaledChain] at chain
        | nil =>
          change q = C E at chain
          have identity : StratumSignReplay.identityCheck (encode q) [coefficients E] = true := by
            apply BivariateEncoding.identityCheck_complete
            simpa only [encode_spec, BivariateEncoding.polynomial, coefficients_spec,
              mul_zero, add_zero] using chain
          simp only [List.map_cons, List.map_nil, ParametricRootCertificate.chainCheck,
            identity, last_checked, Bool.true_and]
      | cons r ps =>
        cases qs with
        | nil => simp [ScaledChain] at chain
        | cons a qs =>
          have step := step_accepted D p q r a l u w sign square_checked chain.1
          have rest := chain_accepted D E (q :: r :: ps) qs l u w sign square_checked
            last last_checked chain.2
          simpa only [List.map_cons, ParametricRootCertificate.chainCheck, step,
            Bool.true_and] using rest
termination_by ps.length

theorem packet_accepted (h : Bivariate) (p : Packet (BivariateEncoding.polynomial h))
    (l u : ℚ) (order : l ≤ u)
    (denominator : ∀ x ∈ Set.Icc (l : ℝ) u,
      BoschlooOrdering.realEval p.denominator x ≠ 0)
    (terminal : ∀ x ∈ Set.Icc (l : ℝ) u,
      BoschlooOrdering.realEval p.terminal x ≠ 0) :
    ∃ c : ParametricRootCertificate.Certificate,
      ParametricRootCertificate.check l u h c = true ∧
      c.representative = encode p.representative ∧ c.tail = p.tail.map encode := by
  let d := coefficients p.denominator
  let square := RootCertificate.mul d d
  obtain ⟨dg, hdg⟩ := nonzero_witness_complete d l u order
    (fun x hx => by simpa only [d, eval_coefficients] using denominator x hx)
  obtain ⟨eg, heg⟩ := nonzero_witness_complete (coefficients p.terminal) l u order
    (fun x hx => by simpa only [eval_coefficients] using terminal x hx)
  have negative_square : ∀ x ∈ Set.Icc (l : ℝ) u,
      RootCertificate.eval (RootCertificate.scale (-1) square) x < 0 := by
    intro x hx
    have hd : RootCertificate.eval d x ≠ 0 := by
      simpa only [d, eval_coefficients] using denominator x hx
    simpa only [RootCertificate.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
      square, RootCertificate.eval_mul, ← pow_two, neg_lt_zero] using sq_pos_of_ne_zero hd
  obtain ⟨sc, hsc⟩ := OpenStrata.negative_certificate _ l u order negative_square
  let sw : StratumSignReplay.SignWitness := ⟨1, sc⟩
  let sg : StratumSignReplay.NonzeroWitness := ⟨true, sc⟩
  have hsw : StratumSignReplay.signCheck square l u sw = true := by
    simp [sw, StratumSignReplay.signCheck, hsc]
  have hsg : StratumSignReplay.nonzeroCheck square l u sg = true := hsw
  let c : ParametricRootCertificate.Certificate :=
    ⟨encode p.representative, encode p.quotient,
      encode (C (p.denominator ^ p.exponent) * p.powerQuotient), p.exponent,
      square, d, sg, dg, encode p.bezoutLeft, encode p.bezoutRight, square, sg,
      p.tail.map encode,
      p.quotients.map (fun a => ⟨encode a, d, d, sw⟩), coefficients p.terminal, eg⟩
  have root : StratumSignReplay.identityCheck (scale square h)
      (mul c.representative c.quotient) = true := by
    apply BivariateEncoding.identityCheck_complete
    simpa only [BivariateEncoding.polynomial_scale, BivariateEncoding.polynomial_mul,
      c, encode_spec, square, d, PolynomialList.polynomial_mul, coefficients_spec, ← pow_two]
      using p.root_identity
  have power : StratumSignReplay.identityCheck (scale d (AlgebraicSpecialization.power
      c.representative c.exponent)) (mul h c.powerQuotient) = true := by
    apply BivariateEncoding.identityCheck_complete
    simpa only [BivariateEncoding.polynomial_scale, BivariateEncoding.polynomial_power,
      BivariateEncoding.polynomial_mul, c, encode_spec, d, coefficients_spec]
      using p.power_identity
  have bezout : StratumSignReplay.identityCheck
      (add (mul c.bezoutLeft c.representative)
        (mul c.bezoutRight (AlgebraicSpecialization.derivative c.representative)))
      [square] = true := by
    apply BivariateEncoding.identityCheck_complete
    simpa only [BivariateEncoding.polynomial_add, BivariateEncoding.polynomial_mul,
      BivariateEncoding.polynomial_derivative, BivariateEncoding.polynomial, c, encode_spec,
      square, d, PolynomialList.polynomial_mul, coefficients_spec, ← pow_two,
      mul_zero, add_zero] using p.bezout_identity
  have first : ParametricRootCertificate.firstCheck c = true := by
    cases tail_eq : p.tail with
    | nil => simp [ParametricRootCertificate.firstCheck, c, tail_eq]
    | cons q qs =>
      have derivative := p.first q (by simp [tail_eq])
      simp only [ParametricRootCertificate.firstCheck, c, tail_eq, List.map_cons]
      apply BivariateEncoding.identityCheck_complete
      simpa only [BivariateEncoding.polynomial_derivative, encode_spec] using derivative
  have chain := chain_accepted p.denominator p.terminal (p.representative :: p.tail)
    p.quotients l u sw rfl hsw eg heg p.chain
  refine ⟨c, ?_, rfl, rfl⟩
  simpa only [ParametricRootCertificate.check, c, decide_eq_true_eq, Bool.and_eq_true,
    p.exponent_pos, hsg, hdg, root, power, bezout, first, List.map_cons, d,
    and_true, true_and] using chain

end ExactCIs.Unconditional.ParametricGeneration
