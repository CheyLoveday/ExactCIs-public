/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.AlgebraicRootCertificate
import ExactCIs.Unconditional.CompactPolynomialWidth

/-! # Raw row widths of specialized modular identities

Wire bivariates are canonical and omit trailing empty rows. The frozen modular
identity checker deliberately checks every raw coefficient slot. Rehydration
therefore appends empty quotient rows to the exact reconstructed expression
width. It never drops a supplied row or invents a missing chain witness.
-/
namespace ExactCIs.Unconditional.SpecializedWitnessWidth

open RootCertificate AlgebraicSpecialization

def mulWidth (a b : Nat) : Nat :=
  if a = 0 then 0 else if b = 0 then a else a + b - 1

def powerWidth (a : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => mulWidth a (powerWidth a n)

def chainWidths : List Nat → List Nat → List Nat
  | [], _ => []
  | [p], _ => [max p 1]
  | [_, q], _ => [max q 1]
  | p :: q :: r :: ps, quotient :: qs =>
      max p (max (mulWidth q quotient) r) :: chainWidths (q :: r :: ps) qs
  | _ :: _ :: _ :: _, [] => []

structure Shape where
  representative : Nat
  quotient : Nat
  powerQuotient : Nat
  exponent : Nat
  bezoutLeft : Nat
  bezoutRight : Nat
  tail : List Nat
  quotients : List Nat

def shape (c : AlgebraicRootCertificate.Certificate) : Shape :=
  ⟨c.representative.length, c.quotient.length, c.powerQuotient.length, c.exponent,
    c.bezoutLeft.length, c.bezoutRight.length, c.tail.map List.length,
    c.quotients.map List.length⟩

structure Widths where
  root : Nat
  power : Nat
  bezout : Nat
  chain : List Nat
  derivative : Nat

def widthsFrom (original : Nat) (c : Shape) : Widths := {
  root := max original (mulWidth c.representative c.quotient)
  power := max (powerWidth c.representative c.exponent) (mulWidth original c.powerQuotient)
  bezout := max (max (mulWidth c.bezoutLeft c.representative)
    (mulWidth c.bezoutRight c.representative)) 1
  chain := chainWidths (c.representative :: c.tail) c.quotients
  derivative := match c.tail with | [] => 0 | p :: _ => max p c.representative }

def widths (original : Nat) (c : AlgebraicRootCertificate.Certificate) : Widths :=
  widthsFrom original (shape c)

@[simp] theorem mulWidth_eq (a b : Nat) :
    mulWidth a b = CompactPolynomialWidth.mulWidth a b := rfl

@[simp] theorem powerWidth_eq (a n : Nat) :
    powerWidth a n = CompactPolynomialWidth.powerWidth a n := by
  induction n <;> simp_all [powerWidth, CompactPolynomialWidth.powerWidth]

theorem root_width (h : Bivariate) (c : AlgebraicRootCertificate.Certificate) :
    (widths h.length c).root =
      (AlgebraicSpecialization.add h
        (AlgebraicSpecialization.scale [-1]
          (AlgebraicSpecialization.mul c.representative c.quotient))).length := by
  simp [widths, widthsFrom, shape, CompactPolynomialWidth.add_length,
    CompactPolynomialWidth.scale_length, CompactPolynomialWidth.mul_length]

theorem power_width (h : Bivariate) (c : AlgebraicRootCertificate.Certificate) :
    (widths h.length c).power =
      (AlgebraicSpecialization.add (AlgebraicSpecialization.power c.representative c.exponent)
        (AlgebraicSpecialization.scale [-1]
          (AlgebraicSpecialization.mul h c.powerQuotient))).length := by
  simp [widths, widthsFrom, shape, CompactPolynomialWidth.add_length,
    CompactPolynomialWidth.scale_length, CompactPolynomialWidth.mul_length,
    CompactPolynomialWidth.power_length]

theorem bezout_width (original : Nat) (c : AlgebraicRootCertificate.Certificate) :
    (widths original c).bezout =
      (AlgebraicSpecialization.add
        (AlgebraicSpecialization.add
          (AlgebraicSpecialization.mul c.bezoutLeft c.representative)
          (AlgebraicSpecialization.mul c.bezoutRight
            (AlgebraicSpecialization.derivative c.representative)))
        (AlgebraicSpecialization.scale [-1] [[1]])).length := by
  simp [widths, widthsFrom, shape, CompactPolynomialWidth.add_length,
    CompactPolynomialWidth.scale_length, CompactPolynomialWidth.mul_length,
    CompactPolynomialWidth.derivative_length]

theorem derivative_width (original : Nat) (c : AlgebraicRootCertificate.Certificate)
    (p : Bivariate) (tail : List Bivariate) (first : c.tail = p :: tail) :
    (widths original c).derivative =
      (AlgebraicSpecialization.add p (AlgebraicSpecialization.scale [-1]
        (AlgebraicSpecialization.derivative c.representative))).length := by
  simp [widths, widthsFrom, shape, first, CompactPolynomialWidth.add_length,
    CompactPolynomialWidth.scale_length, CompactPolynomialWidth.derivative_length]

theorem chain_step_width (p q r quotient : Bivariate) (ps qs : List Bivariate) :
    (chainWidths ((p :: q :: r :: ps).map List.length)
      ((quotient :: qs).map List.length)).head? =
      some (AlgebraicSpecialization.add p
        (AlgebraicSpecialization.scale [-1]
          (AlgebraicSpecialization.add (AlgebraicSpecialization.mul q quotient)
            (AlgebraicSpecialization.scale [-1] r)))).length := by
  simp [chainWidths, CompactPolynomialWidth.add_length,
    CompactPolynomialWidth.scale_length, CompactPolynomialWidth.mul_length]

theorem objective_root_width {n1 n0 : Nat} (mask : Finset (ProductBinomial.Outcome n1 n0))
    (r : Rat) (c : AlgebraicRootCertificate.Certificate) :
    (widths (n1 + n0 + 1) c).root =
      (AlgebraicSpecialization.add (CompactPolynomial.objective mask r)
        (AlgebraicSpecialization.scale [-1]
          (AlgebraicSpecialization.mul c.representative c.quotient))).length := by
  rw [← CompactPolynomialWidth.objective_length mask r]
  exact root_width _ _

def pad (width : Nat) (witness : Bivariate) : Bivariate :=
  witness ++ List.replicate (width - witness.length) []

theorem length_pad (width : Nat) (witness : Bivariate) :
    (pad width witness).length = max width witness.length := by
  simp only [pad, List.length_append, List.length_replicate]
  omega

theorem prefix_pad (width : Nat) (witness : Bivariate) : witness <+: pad width witness :=
  ⟨List.replicate (width - witness.length) [], rfl⟩

theorem pad_eq_self_of_long {width : Nat} {witness : Bivariate}
    (long : width ≤ witness.length) : pad width witness = witness := by
  simp [pad, Nat.sub_eq_zero_of_le long]

@[simp] theorem specialize_empty_rows (x : Real) (n : Nat) :
    specialize x (List.replicate n ([] : Coefficients)) = 0 := by
  induction n <;> simp_all [List.replicate_succ, specialize, RootCertificate.eval]

theorem specialize_append_empty_rows (x : Real) (witness : Bivariate) (n : Nat) :
    specialize x (witness ++ List.replicate n []) = specialize x witness := by
  induction witness <;> simp_all [specialize]

@[simp] theorem specialize_pad (x : Real) (width : Nat) (witness : Bivariate) :
    specialize x (pad width witness) = specialize x witness :=
  specialize_append_empty_rows x witness _

end ExactCIs.Unconditional.SpecializedWitnessWidth
