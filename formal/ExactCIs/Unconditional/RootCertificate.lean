/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import Mathlib

/-!
# Executable rational identity, interval, and root-witness checks

Ascending rational coefficient lists use Horner evaluation. Bounds apply to
nonnegative closed intervals. Root witnesses also cover repeated roots of the
threshold polynomial. This is a sound certificate layer, not a complete Sturm
counter or a proof of the Python generator.
-/
namespace ExactCIs.Unconditional.RootCertificate

abbrev Coefficients := List ℚ

def value : Coefficients → ℚ → ℚ
  | [], _ => 0
  | c :: cs, x => c + x * value cs x

noncomputable def eval : Coefficients → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => c + x * eval cs x

theorem value_coercion (cs : Coefficients) (x : ℚ) :
    (value cs x : ℝ) = eval cs x := by
  induction cs with
  | nil => simp [value, eval]
  | cons c cs ih => simp [value, eval, ih]

theorem continuous_eval (cs : Coefficients) : Continuous (eval cs) := by
  induction cs with
  | nil => exact continuous_const
  | cons c cs ih => exact continuous_const.add (continuous_id.mul ih)

def add : Coefficients → Coefficients → Coefficients
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: add as bs

def scale (c : ℚ) (as : Coefficients) : Coefficients := as.map (c * ·)

def mul : Coefficients → Coefficients → Coefficients
  | [], _ => []
  | a :: as, bs => add (scale a bs) (0 :: mul as bs)

def power (as : Coefficients) : ℕ → Coefficients
  | 0 => [1]
  | n + 1 => mul as (power as n)

theorem eval_add (as bs : Coefficients) (x : ℝ) :
    eval (add as bs) x = eval as x + eval bs x := by
  induction as generalizing bs with
  | nil => simp [add, eval]
  | cons a as ih =>
    cases bs with
    | nil => simp [add, eval]
    | cons b bs => simp [add, eval, ih]; ring

theorem eval_scale (c : ℚ) (as : Coefficients) (x : ℝ) :
    eval (scale c as) x = c * eval as x := by
  induction as with
  | nil => simp [scale, eval]
  | cons a as ih => simp_all [scale, eval]; ring

theorem eval_mul (as bs : Coefficients) (x : ℝ) :
    eval (mul as bs) x = eval as x * eval bs x := by
  induction as with
  | nil => simp [mul, eval]
  | cons a as ih => rw [mul, eval_add, eval_scale, eval, ih, eval]; ring

theorem eval_power (as : Coefficients) (n : ℕ) (x : ℝ) :
    eval (power as n) x = eval as x ^ n := by
  induction n with
  | zero => simp [power, eval]
  | succ n ih => simp [power, eval_mul, ih, pow_succ, mul_comm]

def identityCheck (as bs : Coefficients) : Bool :=
  (add as (scale (-1) bs)).all (· == 0)

theorem identityCheck_sound {as bs : Coefficients}
    (checked : identityCheck as bs = true) (x : ℝ) : eval as x = eval bs x := by
  have zero : ∀ c ∈ add as (scale (-1) bs), c = 0 := by
    simpa [identityCheck, List.all_eq_true] using checked
  have vanishes : ∀ cs : Coefficients, (∀ c ∈ cs, c = 0) → eval cs x = 0 := by
    intro cs
    induction cs with
    | nil => simp [eval]
    | cons c cs ih =>
      intro hc
      simp [eval, hc c (by simp), ih (fun a ha => hc a (List.mem_cons_of_mem c ha))]
  have := vanishes _ zero
  simp only [eval_add, eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul] at this
  linarith

def bounds : Coefficients → ℚ → ℚ → ℚ × ℚ
  | [], _, _ => (0, 0)
  | c :: cs, l, u =>
    let b := bounds cs l u
    (c + min (l * b.1) (u * b.1), c + max (l * b.2) (u * b.2))

theorem product_bounds {l u a b x y : ℝ} (hl : 0 ≤ l)
    (hx : x ∈ Set.Icc l u) (hy : y ∈ Set.Icc a b) :
    min (l * a) (u * a) ≤ x * y ∧ x * y ≤ max (l * b) (u * b) := by
  have hx0 : 0 ≤ x := hl.trans hx.1
  constructor
  · apply le_trans _ (mul_le_mul_of_nonneg_left hy.1 hx0)
    rcases le_total 0 a with ha | ha
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_right hx.1 ha)
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_right hx.2 ha)
  · apply le_trans (mul_le_mul_of_nonneg_left hy.2 hx0)
    rcases le_total 0 b with hb | hb
    · exact (mul_le_mul_of_nonneg_right hx.2 hb).trans (le_max_right _ _)
    · exact (mul_le_mul_of_nonpos_right hx.1 hb).trans (le_max_left _ _)

theorem bounds_sound (cs : Coefficients) {l u : ℚ} (hl : 0 ≤ l)
    {x : ℝ} (hx : x ∈ Set.Icc (l : ℝ) u) :
    eval cs x ∈ Set.Icc ((bounds cs l u).1 : ℝ) ((bounds cs l u).2 : ℝ) := by
  induction cs with
  | nil => simp [eval, bounds]
  | cons c cs ih =>
    have h := product_bounds (by exact_mod_cast hl) hx ih
    simp only [bounds, eval, Rat.cast_add, Rat.cast_min, Rat.cast_max, Rat.cast_mul,
      Set.mem_Icc] at *
    constructor <;> linarith [h.1, h.2]

def positiveCheck (cs : Coefficients) (l u : ℚ) : Bool :=
  decide (0 ≤ l ∧ l ≤ u ∧ 0 < (bounds cs l u).1)

def negativeCheck (cs : Coefficients) (l u : ℚ) : Bool :=
  decide (0 ≤ l ∧ l ≤ u ∧ (bounds cs l u).2 < 0)

theorem positiveCheck_sound {cs : Coefficients} {l u : ℚ}
    (checked : positiveCheck cs l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) : 0 < eval cs x := by
  have h : 0 ≤ l ∧ l ≤ u ∧ 0 < (bounds cs l u).1 := of_decide_eq_true checked
  exact lt_of_lt_of_le (by exact_mod_cast h.2.2) (bounds_sound cs h.1 hx).1

theorem negativeCheck_sound {cs : Coefficients} {l u : ℚ}
    (checked : negativeCheck cs l u = true) {x : ℝ}
    (hx : x ∈ Set.Icc (l : ℝ) u) : eval cs x < 0 := by
  have h : 0 ≤ l ∧ l ≤ u ∧ (bounds cs l u).2 < 0 := of_decide_eq_true checked
  exact lt_of_le_of_lt (bounds_sound cs h.1 hx).2 (by exact_mod_cast h.2.2)

def rootCheck (cs : Coefficients) (l u : ℚ) : Bool :=
  decide (0 ≤ l ∧ l < u ∧ value cs l < 0 ∧ 0 < value cs u)

theorem rootCheck_sound {cs : Coefficients} {l u : ℚ}
    (checked : rootCheck cs l u = true) :
    ∃ x ∈ Set.Ioo (l : ℝ) u, eval cs x = 0 := by
  have h : 0 ≤ l ∧ l < u ∧ value cs l < 0 ∧ 0 < value cs u :=
    of_decide_eq_true checked
  have left : eval cs l < 0 := by rw [← value_coercion]; exact_mod_cast h.2.2.1
  have right : 0 < eval cs u := by rw [← value_coercion]; exact_mod_cast h.2.2.2
  have order : (l : ℝ) ≤ u := by exact_mod_cast h.2.1.le
  have existsRoot : (0 : ℝ) ∈ eval cs '' Set.Icc (l : ℝ) u :=
    intermediate_value_Icc order (continuous_eval cs).continuousOn ⟨left.le, right.le⟩
  obtain ⟨x, hx, hz⟩ := existsRoot
  refine ⟨x, ⟨?_, ?_⟩, hz⟩
  · exact lt_of_le_of_ne hx.1 (by intro e; rw [e] at left; linarith)
  · exact lt_of_le_of_ne hx.2 (by intro e; rw [← e] at right; linarith)

def derivative : Coefficients → Coefficients
  | [] => []
  | _ :: cs => add cs (0 :: derivative cs)

theorem hasDerivAt_eval (cs : Coefficients) (x : ℝ) :
    HasDerivAt (eval cs) (eval (derivative cs) x) x := by
  induction cs with
  | nil => simpa [eval, derivative] using hasDerivAt_const x (0 : ℝ)
  | cons c cs ih =>
    convert (hasDerivAt_const x (c : ℝ)).add ((hasDerivAt_id x).mul ih) using 1 <;>
      first | rfl | simp [eval, derivative, eval_add]

def isolatorCheck (cs : Coefficients) (l u : ℚ) : Bool :=
  rootCheck cs l u && positiveCheck (derivative cs) l u

theorem isolatorCheck_sound {cs : Coefficients} {l u : ℚ}
    (checked : isolatorCheck cs l u = true) :
    ∃! x, x ∈ Set.Icc (l : ℝ) u ∧ eval cs x = 0 := by
  have checks : rootCheck cs l u = true ∧ positiveCheck (derivative cs) l u = true := by
    simpa only [isolatorCheck, Bool.and_eq_true] using checked
  obtain ⟨rootChecked, derivChecked⟩ := checks
  obtain ⟨x, hx, hz⟩ := rootCheck_sound rootChecked
  have mono : StrictMonoOn (eval cs) (Set.Icc (l : ℝ) u) :=
    strictMonoOn_of_deriv_pos (convex_Icc _ _) (continuous_eval cs).continuousOn
      (fun y hy => by
        rw [(hasDerivAt_eval cs y).deriv]
        exact positiveCheck_sound derivChecked (interior_subset hy))
  refine ⟨x, ⟨⟨hx.1.le, hx.2.le⟩, hz⟩, ?_⟩
  intro y hy
  exact mono.injOn hy.1 ⟨hx.1.le, hx.2.le⟩ (hy.2.trans hz.symm)

def witnessCheck (h d quotient : Coefficients) (l u : ℚ) : Bool :=
  rootCheck d l u && identityCheck h (mul d quotient) && decide (u ≤ 1)

theorem witnessCheck_sound {h d quotient : Coefficients} {l u : ℚ}
    (checked : witnessCheck h d quotient l u = true) :
    ∃ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ eval h x := by
  have checks : (rootCheck d l u = true ∧ identityCheck h (mul d quotient) = true) ∧
      decide (u ≤ 1) = true := by
    simpa only [witnessCheck, Bool.and_eq_true] using checked
  obtain ⟨⟨bracket, identity⟩, cap⟩ := checks
  obtain ⟨x, hx, hz⟩ := rootCheck_sound bracket
  have domain : 0 ≤ l ∧ l < u ∧ value d l < 0 ∧ 0 < value d u :=
    of_decide_eq_true bracket
  refine ⟨x, ⟨le_trans (by exact_mod_cast domain.1) hx.1.le,
    hx.2.le.trans (by exact_mod_cast (of_decide_eq_true cap : u ≤ 1))⟩, ?_⟩
  rw [identityCheck_sound identity x, eval_mul, hz, zero_mul]


/-- An exact rational point, including either endpoint and equality. -/
def pointCheck (cs : Coefficients) (q : ℚ) : Bool :=
  decide (0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ value cs q)

theorem pointCheck_sound {cs : Coefficients} {q : ℚ}
    (checked : pointCheck cs q = true) :
    (q : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧ 0 ≤ eval cs q := by
  have h : 0 ≤ q ∧ q ≤ 1 ∧ 0 ≤ value cs q := of_decide_eq_true checked
  refine ⟨⟨by exact_mod_cast h.1, by exact_mod_cast h.2.1⟩, ?_⟩
  rw [← value_coercion]
  exact_mod_cast h.2.2

theorem negativeCheck_reject {cs : Coefficients}
    (checked : negativeCheck cs 0 1 = true) :
    ¬ ∃ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ eval cs x := by
  rintro ⟨x, hx, sign⟩
  exact (negativeCheck_sound checked (by simpa using hx)).not_ge sign

/-- Completeness for every rational constant, including the zero polynomial. -/
theorem constant_complete (c : ℚ) :
    pointCheck [c] 0 = true ∨ negativeCheck [c] 0 1 = true := by
  rcases le_or_gt 0 c with h | h
  · left; simp [pointCheck, value, h]
  · right; simp [negativeCheck, bounds, h]

end ExactCIs.Unconditional.RootCertificate
