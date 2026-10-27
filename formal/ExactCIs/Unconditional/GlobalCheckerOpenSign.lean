/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerPoint
import ExactCIs.Unconditional.OpenRootCount

/-! # Whole-open-cell signs from data-only endpoint replay

A checked sample supplies the sign only after a complete root count proves
that the entire open interval is root-free. Roots at either endpoint belong
to their singleton cells. Identity zero requires a coefficient identity.
-/
namespace ExactCIs.Unconditional.GlobalCheckerOpenSign

open RootCertificate GlobalCheckerPoint SturmVariation

def count (c : RootCountCertificate.Certificate) (a b : Point)
    (left right : List GlobalCheckerPoint.SignWitness) : Option ℕ := do
  let ls ← signs a (c.representative :: c.tail) left
  let rs ← signs b (c.representative :: c.tail) right
  pure (variations ls - variations rs - if rs.headD 0 = 0 then 1 else 0)

theorem count_sound {p : Coefficients} {c : RootCountCertificate.Certificate}
    (root_checked : RootCountCertificate.check p c = true) {a b : Point}
    {left right : List GlobalCheckerPoint.SignWitness} {n : ℕ}
    (checked : count c a b left right = some n) (ordered : a.value < b.value) :
    n = {x : ℝ | a.value < x ∧ x < b.value ∧ eval p x = 0}.ncard := by
  cases hl : signs a (c.representative :: c.tail) left with
  | none => simp [count, hl] at checked
  | some ls =>
    cases hr : signs b (c.representative :: c.tail) right with
    | none => simp [count, hl, hr] at checked
    | some rs =>
      have result := OpenRootCount.count_open_sound root_checked ordered
      have rootset := AlgebraicCertificate.rootSetCheck_sound
        ((RootCountCertificate.check_iff p c).mp root_checked).1 b.value
      have eq : variations ls - variations rs - (if rs.headD 0 = 0 then 1 else 0) = n := by
        simpa [count, hl, hr] using checked
      rw [← signs_sound hl, ← signs_sound hr] at eq
      simp only [List.map_cons, List.headD_cons, sign_eq_zero_iff, ← rootset] at eq
      exact eq.symm.trans (by simpa only [variationAt, List.map_map,
        Function.comp_def, List.map_cons] using result)

inductive Witness where
  | identityZero
  | rootFree (sign : SignType) (certificate : RootCountCertificate.Certificate)
      (left right : List GlobalCheckerPoint.SignWitness) (sample : ℚ)

def Witness.sign : Witness → SignType
  | .identityZero => 0
  | .rootFree s _ _ _ _ => s

def check (p : Coefficients) (a b : Point) : Witness → Bool
  | .identityZero => identityCheck p []
  | .rootFree s c left right sample =>
      RootCountCertificate.check p c && sampleCheck a b sample &&
      decide (s ≠ 0 ∧ SignType.sign (RootCertificate.value p sample) = s) &&
      decide (count c a b left right = some 0)

theorem root_free_sign_constant {p : Coefficients} {a b x y : ℝ}
    (no_roots : ∀ z ∈ Set.Ioo a b, eval p z ≠ 0)
    (hx : x ∈ Set.Ioo a b) (hy : y ∈ Set.Ioo a b) :
    SignType.sign (eval p x) = SignType.sign (eval p y) := by
  apply isPreconnected_Ioo.constant _ hx hy
  intro z hz
  exact ((continuousAt_sign_of_ne_zero (no_roots z hz)).comp
    (continuous_eval p).continuousAt).continuousWithinAt

theorem check_sound {p : Coefficients} {a b : Point} {w : Witness}
    (checked : check p a b w = true) {x : ℝ} (inside : x ∈ Set.Ioo a.value b.value) :
    SignType.sign (eval p x) = w.sign := by
  cases w with
  | identityZero =>
    rw [show eval p x = 0 from (identityCheck_sound checked x)]
    simp [Witness.sign]
  | rootFree s c left right sample =>
    have parts : RootCountCertificate.check p c = true ∧ sampleCheck a b sample = true ∧
        (s ≠ 0 ∧ SignType.sign (RootCertificate.value p sample) = s) ∧
        count c a b left right = some 0 := by
      simpa only [check, Bool.and_eq_true, decide_eq_true_eq, and_assoc] using checked
    have sample_inside := sampleCheck_sound parts.2.1
    have zero := count_sound parts.1 parts.2.2.2 (inside.1.trans inside.2)
    have finite := (RootCountCertificate.roots_finite parts.1).subset
      (show {z : ℝ | a.value < z ∧ z < b.value ∧ eval p z = 0} ⊆
        {z : ℝ | eval p z = 0} from fun _ hz => hz.2.2)
    have no_roots : ∀ z ∈ Set.Ioo a.value b.value, eval p z ≠ 0 := by
      intro z hz root
      have positive := (Set.ncard_pos finite).mpr ⟨z, hz.1, hz.2, root⟩
      omega
    change SignType.sign (eval p x) = s
    rw [root_free_sign_constant no_roots inside sample_inside,
      ← value_coercion, RootCountCertificate.sign_ratCast]
    exact parts.2.2.1.2

theorem nonzero_sound {p : Coefficients} {a b : Point} {w : Witness}
    (checked : check p a b w = true) (nonzero : w.sign ≠ 0)
    {x : ℝ} (inside : x ∈ Set.Ioo a.value b.value) : eval p x ≠ 0 := by
  intro zero
  have hs := check_sound checked inside
  rw [zero, sign_zero] at hs
  exact nonzero hs.symm

def nonzeroCheck (p : Coefficients) (a b : Point) (w : Witness) : Bool :=
  decide (w.sign ≠ 0) && check p a b w

theorem nonzeroCheck_sound {p : Coefficients} {a b : Point} {w : Witness}
    (checked : nonzeroCheck p a b w = true)
    {x : ℝ} (inside : x ∈ Set.Ioo a.value b.value) : eval p x ≠ 0 := by
  have parts := Bool.and_eq_true_iff.mp checked
  exact nonzero_sound parts.2 (of_decide_eq_true parts.1) inside

def signsCheck (a b : Point) (q : ℚ) :
    List AlgebraicSpecialization.Bivariate → List Witness → Bool
  | [], [] => true
  | p :: ps, w :: ws => check (AlgebraicSignReplay.atRational p q) a b w &&
      signsCheck a b q ps ws
  | _, _ => false

theorem signsCheck_sound {a b : Point} {q : ℚ}
    {ps : List AlgebraicSpecialization.Bivariate} {ws : List Witness}
    (checked : signsCheck a b q ps ws = true) {x : ℝ}
    (inside : x ∈ Set.Ioo a.value b.value) :
    (ps.map fun p => SignType.sign ((AlgebraicSpecialization.specialize x p).eval (q : ℝ))) =
      ws.map Witness.sign := by
  induction ps generalizing ws with
  | nil => cases ws <;> simp_all [signsCheck]
  | cons p ps ih =>
    cases ws with
    | nil => simp [signsCheck] at checked
    | cons w ws =>
      have parts : check (AlgebraicSignReplay.atRational p q) a b w = true ∧
          signsCheck a b q ps ws = true := by
        simpa only [signsCheck, Bool.and_eq_true] using checked
      have hs := check_sound parts.1 inside
      rw [AlgebraicSignReplay.atRational_sound] at hs
      simp only [List.map_cons, hs, ih parts.2]

def nuisanceCount (left right : List Witness) : ℕ :=
  variations (left.map Witness.sign) - variations (right.map Witness.sign)

end ExactCIs.Unconditional.GlobalCheckerOpenSign
