/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.PolynomialList

/-! # Canonical signed rational polynomial data

Zero has no coefficient slots. Normalisation removes only trailing zeroes;
it never changes the sign or scale of a threshold polynomial.
-/
namespace ExactCIs.Unconditional.CanonicalEncoding

open RootCertificate PolynomialList

def trim : Coefficients → Coefficients
  | [] => []
  | c :: cs => let tail := trim cs
              if tail = [] ∧ c = 0 then [] else c :: tail

def Canonical : Coefficients → Prop
  | [] => True
  | c :: cs => Canonical cs ∧ (cs ≠ [] ∨ c ≠ 0)

theorem trim_polynomial (cs : Coefficients) : polynomial (trim cs) = polynomial cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [trim]
    split_ifs with h
    · have zero : polynomial cs = 0 := by rw [← ih, h.1]; rfl
      simp [polynomial, h.2, zero]
    · simp only [polynomial, ih]

theorem trim_canonical (cs : Coefficients) : Canonical (trim cs) := by
  induction cs with
  | nil => trivial
  | cons c cs ih =>
    simp only [trim]
    split_ifs with h
    · trivial
    · exact ⟨ih, by tauto⟩

theorem trim_eq_self {cs : Coefficients} (h : Canonical cs) : trim cs = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [Canonical] at h
    simp only [trim, ih h.1]
    rw [if_neg (by tauto)]

theorem trim_idempotent (cs : Coefficients) : trim (trim cs) = trim cs :=
  trim_eq_self (trim_canonical cs)

theorem canonical_zero {cs : Coefficients} (h : Canonical cs)
    (zero : polynomial cs = 0) : cs = [] := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have allZero := (zero_iff _).mp zero
    have head : c = 0 := allZero c (by simp)
    have tail : polynomial cs = 0 := (zero_iff _).mpr (fun a ha => allZero a (by simp [ha]))
    have empty := ih h.1 tail
    rcases h.2 with nonempty | nonzero
    · exact (nonempty empty).elim
    · exact (nonzero head).elim

theorem canonical_injective {as bs : Coefficients} (ha : Canonical as) (hb : Canonical bs)
    (same : polynomial as = polynomial bs) : as = bs := by
  induction as generalizing bs with
  | nil => exact (canonical_zero hb same.symm).symm
  | cons a as ih =>
    cases bs with
    | nil => exact canonical_zero ha same
    | cons b bs =>
      have head : a = b := by
        have h := congrArg (fun p : Polynomial ℚ => p.coeff 0) same
        simpa [polynomial] using h
      have tail : polynomial as = polynomial bs := by
        apply Polynomial.ext
        intro i
        have h := congrArg (fun p : Polynomial ℚ => p.coeff (i + 1)) same
        simpa [polynomial, Polynomial.coeff_X_mul] using h
      simp only [head, ih ha.1 hb.1 tail]

theorem trim_eq_iff (as bs : Coefficients) :
    trim as = trim bs ↔ polynomial as = polynomial bs := by
  constructor
  · intro h
    simpa only [trim_polynomial] using congrArg polynomial h
  · intro h
    apply canonical_injective (trim_canonical as) (trim_canonical bs)
    simpa only [trim_polynomial] using h

def exactDegree (cs : Coefficients) : Option ℕ :=
  if cs = [] then none else some (cs.length - 1)

theorem last_nonzero {cs : Coefficients} (h : Canonical cs) (hne : cs ≠ []) :
    cs.getD (cs.length - 1) 0 ≠ 0 := by
  induction cs with
  | nil => contradiction
  | cons c cs ih =>
    cases cs with
    | nil => simpa using h.2
    | cons d ds =>
      simpa using ih h.1 (by simp)

theorem exact_degree {cs : Coefficients} (h : Canonical cs) (hne : cs ≠ []) :
    (polynomial cs).degree = (cs.length - 1 : ℕ) := by
  apply Polynomial.degree_eq_of_le_of_coeff_ne_zero
  · rw [Polynomial.degree_le_iff_coeff_zero]
    intro n hn
    rw [coefficient, List.getD_eq_default]
    have hn' : cs.length - 1 < n := by exact_mod_cast hn
    omega
  · rw [coefficient]
    exact last_nonzero h hne

theorem exactDegree_none {cs : Coefficients} (h : Canonical cs) :
    exactDegree cs = none ↔ polynomial cs = 0 := by
  simp only [exactDegree, ite_eq_left_iff, Option.some_ne_none, imp_false, not_not]
  exact ⟨fun he => by rw [he]; rfl, canonical_zero h⟩

theorem exactDegree_some {cs : Coefficients} (h : Canonical cs) {n : ℕ} :
    exactDegree cs = some n ↔ (polynomial cs).degree = n := by
  by_cases he : cs = []
  · subst cs
    simp [exactDegree, polynomial]
  · rw [exactDegree, if_neg he, Option.some.injEq, exact_degree h he]
    exact WithBot.coe_eq_coe.symm

structure Rational where
  numerator : ℤ
  denominator : ℕ
  deriving DecidableEq, Repr

def Rational.value (r : Rational) : ℚ := r.numerator / r.denominator
def encode (q : ℚ) : Rational := ⟨q.num, q.den⟩
def Rational.check (r : Rational) : Bool := decide (encode r.value = r)

theorem encode_value (q : ℚ) : (encode q).value = q := by
  exact Rat.num_div_den q

theorem rational_roundtrip (q : ℚ) : (encode q).check = true := by
  simp [Rational.check, encode_value]

theorem rational_check_sound {r : Rational} (h : r.check = true) :
    0 < r.denominator ∧ encode r.value = r := by
  have eq : encode r.value = r := of_decide_eq_true h
  refine ⟨?_, eq⟩
  rw [← eq]
  exact Rat.den_pos _

theorem rational_unique {a b : Rational} (ha : a.check = true) (hb : b.check = true)
    (same : a.value = b.value) : a = b := by
  rw [← (rational_check_sound ha).2, ← (rational_check_sound hb).2, same]

end ExactCIs.Unconditional.CanonicalEncoding
