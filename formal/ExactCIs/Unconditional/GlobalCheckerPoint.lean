/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootEventOrder
import ExactCIs.Unconditional.AlgebraicSignReplay

/-! # Data-only points and sign replay for the global checker

Rational and selected algebraic points share one semantic interface. No midpoint
is used as the value of an algebraic point. Every algebraic sign replay checks
the original embedding as well as the sign witness.
-/
namespace ExactCIs.Unconditional.GlobalCheckerPoint

open RootCertificate SelectedRoot

inductive Point where
  | rational (value : ℚ)
  | algebraic (root : Root)
  deriving Repr

def Point.check : Point → Bool
  | .rational _ => true
  | .algebraic a => a.check

noncomputable def Point.value : Point → ℝ
  | .rational q => q
  | .algebraic a => RootEventOrder.value a

def Point.lower : Point → ℚ
  | .rational q => q
  | .algebraic a => a.lower

def Point.upper : Point → ℚ
  | .rational q => q
  | .algebraic a => a.upper

theorem point_bounds {p : Point} (checked : p.check = true) :
    p.value ∈ Set.Icc (p.lower : ℝ) p.upper := by
  cases p with
  | rational q => exact ⟨le_rfl, le_rfl⟩
  | algebraic a =>
    have h := (RootEventOrder.value_means checked).1
    exact ⟨h.1.le, h.2.le⟩

inductive SignWitness where
  | rational
  | algebraic (witness : AlgebraicSignReplay.SignWitness)

def sign (p : Coefficients) : Point → SignWitness → Option SignType
  | .rational q, .rational => some (SignType.sign (RootCertificate.value p q))
  | .algebraic a, .algebraic w =>
      if a.check && AlgebraicSignReplay.signCheck a.definer p a.lower a.upper w
      then some w.sign else none
  | _, _ => none

theorem sign_sound {p : Coefficients} {a : Point} {w : SignWitness} {s : SignType}
    (checked : sign p a w = some s) :
    a.check = true ∧ SignType.sign (eval p a.value) = s := by
  cases a with
  | rational q =>
    cases w with
    | algebraic w => simp [sign] at checked
    | rational =>
      have eq : SignType.sign (RootCertificate.value p q) = s := Option.some.inj checked
      refine ⟨rfl, ?_⟩
      rw [Point.value, ← value_coercion, RootCountCertificate.sign_ratCast, eq]
  | algebraic a =>
    cases w with
    | rational => simp [sign] at checked
    | algebraic w =>
      have parts : (a.check = true ∧
          AlgebraicSignReplay.signCheck a.definer p a.lower a.upper w = true) ∧ w.sign = s := by
        simpa [sign] using checked
      have meaning := RootEventOrder.value_means parts.1.1
      exact ⟨parts.1.1, (AlgebraicSignReplay.signCheck_sound parts.1.2 meaning.2
        ⟨meaning.1.1.le, meaning.1.2.le⟩).trans parts.2⟩

def signs (a : Point) : List Coefficients → List SignWitness → Option (List SignType)
  | [], [] => some []
  | p :: ps, w :: ws => do
      let s ← sign p a w
      let ss ← signs a ps ws
      pure (s :: ss)
  | _, _ => none

theorem signs_sound {a : Point} {ps : List Coefficients} {ws : List SignWitness}
    {ss : List SignType} (checked : signs a ps ws = some ss) :
    ps.map (fun p => SignType.sign (eval p a.value)) = ss := by
  induction ps generalizing ws ss with
  | nil =>
    cases ws with
    | nil => simpa only [signs, Option.some.injEq, List.map_nil] using checked
    | cons _ _ => simp [signs] at checked
  | cons p ps ih =>
    cases ws with
    | nil => simp [signs] at checked
    | cons w ws =>
      cases hs : sign p a w with
      | none => simp [signs, hs] at checked
      | some s =>
        cases ht : signs a ps ws with
        | none => simp [signs, hs, ht] at checked
        | some ts =>
          have eq : s :: ts = ss := by simpa [signs, hs, ht] using checked
          simpa only [List.map_cons, (sign_sound hs).2, ih ht] using eq

theorem sign_getD_sound {p : Coefficients} {a : Point} {w : SignWitness}
    (checked : (sign p a w).isSome = true) :
    SignType.sign (eval p a.value) = (sign p a w).getD 0 := by
  cases hs : sign p a w with
  | none => simp [hs] at checked
  | some s => exact (sign_sound hs).2

theorem specialized_signs {a : Point} {q : ℚ}
    {ps : List AlgebraicSpecialization.Bivariate} {ws : List SignWitness} {ss : List SignType}
    (checked : signs a (ps.map fun p => AlgebraicSignReplay.atRational p q) ws = some ss) :
    ps.map (fun p => SignType.sign ((AlgebraicSpecialization.specialize a.value p).eval (q : ℝ))) =
      ss := by
  simpa only [List.map_map, Function.comp_def, AlgebraicSignReplay.atRational_sound]
    using signs_sound checked

/-- A sample is strictly inside even when an endpoint is algebraic. Weak
isolator inequalities are sufficient because the selected root is interior. -/
def sampleCheck (a b : Point) (q : ℚ) : Bool :=
  a.check && b.check &&
    (match a with
      | .rational x => decide (x < q)
      | .algebraic x => decide (x.upper ≤ q)) &&
    (match b with
      | .rational x => decide (q < x)
      | .algebraic x => decide (q ≤ x.lower))

theorem sampleCheck_sound {a b : Point} {q : ℚ}
    (checked : sampleCheck a b q = true) : (q : ℝ) ∈ Set.Ioo a.value b.value := by
  cases a <;> cases b <;>
    simp only [sampleCheck, Point.check, Bool.and_eq_true, decide_eq_true_eq,
      true_and, and_true] at checked <;> simp only [Point.value]
  case rational.rational x y =>
    exact ⟨by exact_mod_cast checked.1, by exact_mod_cast checked.2⟩
  case rational.algebraic x y =>
    exact ⟨by exact_mod_cast checked.1.2,
      (by exact_mod_cast checked.2 : (q : ℝ) ≤ y.lower).trans_lt
        (RootEventOrder.value_means checked.1.1).1.1⟩
  case algebraic.rational x y =>
    exact ⟨(RootEventOrder.value_means checked.1.1).1.2.trans_le
      (by exact_mod_cast checked.1.2), by exact_mod_cast checked.2⟩
  case algebraic.algebraic x y =>
    exact ⟨(RootEventOrder.value_means checked.1.1.1).1.2.trans_le
      (by exact_mod_cast checked.1.2),
      (by exact_mod_cast checked.2 : (q : ℝ) ≤ y.lower).trans_lt
        (RootEventOrder.value_means checked.1.1.2).1.1⟩

end ExactCIs.Unconditional.GlobalCheckerPoint
