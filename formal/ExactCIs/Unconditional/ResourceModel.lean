/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import Mathlib.Data.Fintype.Basic

/-! # Version 1 vector resource algebra

Dimension indices follow `RESOURCE_MODEL_V1.md` and `resource_model.py` exactly.
An arbitrary thunk is not a certified primitive. Replay refinements must also
exhibit their concrete instrumented bodies. Verification is assigned to formal-code.
-/
namespace ExactCIs.Unconditional.ResourceModel

abbrev Dimension := Fin 15
structure Vector where
  values : Array Nat
  size_eq : values.size = 15

def Vector.get (v : Vector) (d : Dimension) : Nat :=
  v.values[d.val]'(by simpa only [v.size_eq] using d.isLt)

instance : CoeFun Vector (fun _ => Dimension → Nat) := ⟨Vector.get⟩

/-- Construction materializes the fixed-size data array; the result is data,
not a function which the compiler can eta-expand into a delayed recomputation. -/
@[irreducible] def Vector.ofFn (read : Dimension → Nat) : Vector :=
  ⟨Array.ofFn read, Array.size_ofFn⟩

@[simp] theorem Vector.ofFn_apply (read : Dimension → Nat) (d : Dimension) :
    Vector.ofFn read d = read d := by simp [Vector.get, Vector.ofFn]

@[ext] theorem Vector.ext {a b : Vector} (same : ∀ d, a d = b d) : a = b := by
  have values : a.values = b.values := by
    apply Array.ext
    · rw [a.size_eq, b.size_eq]
    · intro i ha hb
      have valid : i < 15 := by simpa only [a.size_eq] using ha
      exact same ⟨i,valid⟩
  cases a with
  | mk av ah => cases b with
    | mk bv bh => dsimp only at values; cases values; rfl

def zero : Vector := Vector.ofFn fun _ => 0
def highWater (d : Dimension) : Bool := d.val == 13 || d.val == 14

/-- Vectors already contain fifteen materialized values, so retaining the
snapshot cannot retain an unevaluated chain of previous counter functions. -/
def cacheVector (v : Vector) : Vector := v

@[simp] theorem cacheVector_eq (v : Vector) : cacheVector v = v := by
  rfl

def bump (used cost : Vector) : Vector := cacheVector (Vector.ofFn fun d =>
  if highWater d then max (used d) (cost d) else used d + cost d)
def totalWork (v : Vector) : Nat :=
  v 1 + v 2 + v 3 + v 4 + v 5 + v 6 + v 7 + v 8 + v 9 + v 11 + v 12

structure Profile where
  caps : Vector
  polynomialOps : Nat
  rootChecks : Nat
  algebraicComparisons : Nat
  leaves : Nat
  totalWork : Nat

def maxCounter : Nat := 9223372036854775807

def ValidProfile (p : Profile) : Prop :=
  (∀ d, p.caps d ≤ maxCounter) ∧ p.polynomialOps ≤ maxCounter ∧
    p.rootChecks ≤ maxCounter ∧ p.algebraicComparisons ≤ maxCounter ∧
    p.leaves ≤ maxCounter ∧ p.totalWork ≤ maxCounter

instance (p : Profile) : Decidable (ValidProfile p) :=
  inferInstanceAs (Decidable
    ((∀ d, p.caps d ≤ maxCounter) ∧ p.polynomialOps ≤ maxCounter ∧
      p.rootChecks ≤ maxCounter ∧ p.algebraicComparisons ≤ maxCounter ∧
      p.leaves ≤ maxCounter ∧ p.totalWork ≤ maxCounter))

def Fits (p : Profile) (v : Vector) : Prop :=
  (∀ d, v d ≤ p.caps d) ∧ v 3 ≤ p.polynomialOps ∧ v 5 ≤ p.rootChecks ∧
    v 6 ≤ p.algebraicComparisons ∧ v 9 ≤ p.leaves ∧ totalWork v ≤ p.totalWork

instance (p : Profile) (v : Vector) : Decidable (Fits p v) :=
  inferInstanceAs (Decidable
    ((∀ d, v d ≤ p.caps d) ∧ v 3 ≤ p.polynomialOps ∧ v 5 ≤ p.rootChecks ∧
      v 6 ≤ p.algebraicComparisons ∧ v 9 ≤ p.leaves ∧ totalWork v ≤ p.totalWork))

def LimitsLE (lower upper : Profile) : Prop :=
  (∀ d, lower.caps d ≤ upper.caps d) ∧ lower.polynomialOps ≤ upper.polynomialOps ∧
    lower.rootChecks ≤ upper.rootChecks ∧
    lower.algebraicComparisons ≤ upper.algebraicComparisons ∧
    lower.leaves ≤ upper.leaves ∧ lower.totalWork ≤ upper.totalWork

instance (lower upper : Profile) : Decidable (LimitsLE lower upper) :=
  inferInstanceAs (Decidable
    ((∀ d, lower.caps d ≤ upper.caps d) ∧ lower.polynomialOps ≤ upper.polynomialOps ∧
      lower.rootChecks ≤ upper.rootChecks ∧
      lower.algebraicComparisons ≤ upper.algebraicComparisons ∧
      lower.leaves ≤ upper.leaves ∧ lower.totalWork ≤ upper.totalWork))

theorem Fits.mono {lower upper : Profile} {used : Vector}
    (limits : LimitsLE lower upper) (fits : Fits lower used) : Fits upper used :=
  ⟨fun d => (fits.1 d).trans (limits.1 d), fits.2.1.trans limits.2.1,
    fits.2.2.1.trans limits.2.2.1, fits.2.2.2.1.trans limits.2.2.2.1,
    fits.2.2.2.2.1.trans limits.2.2.2.2.1, fits.2.2.2.2.2.trans limits.2.2.2.2.2⟩

/-- A caller-supplied profile can narrow every limit, never raise one. -/
def intersect (outer requested : Profile) : Profile where
  caps := Vector.ofFn fun d => min (outer.caps d) (requested.caps d)
  polynomialOps := min outer.polynomialOps requested.polynomialOps
  rootChecks := min outer.rootChecks requested.rootChecks
  algebraicComparisons := min outer.algebraicComparisons requested.algebraicComparisons
  leaves := min outer.leaves requested.leaves
  totalWork := min outer.totalWork requested.totalWork

theorem intersect_le (outer requested : Profile) : LimitsLE (intersect outer requested) outer := by
  refine ⟨?_, Nat.min_le_left _ _, Nat.min_le_left _ _,
    Nat.min_le_left _ _, Nat.min_le_left _ _, Nat.min_le_left _ _⟩
  intro d
  simp only [intersect, Vector.ofFn_apply]
  exact Nat.min_le_left _ _

inductive Event where
  | admitBytes | decodeItem | sampleState | ratAdd | ratSub | ratMul | ratDiv
  | coefficients | rootStep | algebraicCompare | projectionPolynomial
  | projectionRoot | leafTransition | emitBytes | integer | structural | operand | degree
  deriving DecidableEq, Repr

def Event.dimension : Event → Dimension
  | .admitBytes => 0
  | .decodeItem => 1
  | .sampleState => 2
  | .ratAdd | .ratSub | .ratMul | .ratDiv => 3
  | .coefficients => 4
  | .rootStep => 5
  | .algebraicCompare => 6
  | .projectionPolynomial => 7
  | .projectionRoot => 8
  | .leafTransition => 9
  | .emitBytes => 10
  | .integer => 11
  | .structural => 12
  | .operand => 13
  | .degree => 14

def Event.allows (e : Event) (cost : Vector) : Prop :=
  ∀ d, d ≠ e.dimension → highWater d = false → cost d = 0

instance (e : Event) (cost : Vector) : Decidable (e.allows cost) :=
  inferInstanceAs (Decidable (∀ d, d ≠ e.dimension → highWater d = false → cost d = 0))

structure Exhausted where
  event : Event
  previous : Vector
  requested : Vector

inductive FailureCode where
  | invalidInput | syntax | noncanonical | invalidCertificate
  | unsupportedCertificateClass | stalled | internalInvariant | zeroDenominator
  deriving DecidableEq, Repr

inductive Refusal where
  | resource (details : Exhausted)
  | invalidDescriptor
  | semantic (code : FailureCode) (previous : Vector)
  | context (phase : String) (reason : Refusal)

def charge (p : Profile) (event : Event) (cost used : Vector) : Except Refusal Vector :=
  if event.allows cost then
    if Fits p (bump used cost) then .ok (bump used cost)
    else .error (.resource ⟨event, used, cost⟩)
  else .error .invalidDescriptor

theorem charge_sound {p : Profile} {event : Event} {cost used next : Vector}
    (checked : charge p event cost used = .ok next) :
    event.allows cost ∧ next = bump used cost ∧ Fits p next := by
  unfold charge at checked
  split at checked
  · rename_i allowed
    split at checked
    · rename_i fits
      cases Except.ok.inj checked
      exact ⟨allowed, rfl, fits⟩
    · contradiction
  · contradiction

theorem bump_monotone (used cost : Vector) (d : Dimension) :
    used d ≤ bump used cost d := by
  simp only [bump, cacheVector_eq, Vector.ofFn_apply]
  split
  · exact Nat.le_max_left _ _
  · exact Nat.le_add_right _ _

theorem charge_monotone {p : Profile} {event : Event} {cost used next : Vector}
    (checked : charge p event cost used = .ok next) (d : Dimension) : used d ≤ next d := by
  rw [(charge_sound checked).2.1]
  exact bump_monotone used cost d

theorem charge_bounded {p : Profile} {event : Event} {cost used next : Vector}
    (valid : ValidProfile p) (checked : charge p event cost used = .ok next)
    (d : Dimension) : next d ≤ maxCounter :=
  ((charge_sound checked).2.2.1 d).trans (valid.1 d)

abbrev M (α : Type) := Profile → Vector → Except Refusal (α × Vector)

def ret {α : Type} (a : α) : M α := fun _ used => .ok (a, used)
@[inline] def bind {α β : Type} (m : M α) (k : α → M β) : M β := fun p used =>
  match m p used with
  | .error reason => .error reason
  | .ok (a, next) => k a p next

instance : Monad M where
  pure := ret
  bind := bind

def fail {α : Type} (code : FailureCode) : M α := fun _ used =>
  .error (.semantic code used)

/-- Keep the nearest failing phase, without growing an unbounded context stack. -/
def withPhase {α : Type} (phase : String) (m : M α) : M α := fun p used =>
  match m p used with
  | .ok result => .ok result
  | .error (.context inner reason) => .error (.context inner reason)
  | .error reason => .error (.context phase reason)

def perform {α : Type} (event : Event) (cost : Vector) (body : Unit → α) : M α :=
  fun p used => match charge p event cost used with
  | .error reason => .error reason
  | .ok next => .ok (body (), next)

def Safe {α : Type} (m : M α) : Prop :=
  ∀ p used, Fits p used → ∀ a next, m p used = .ok (a, next) → Fits p next
def Refines {α : Type} (m : M α) (value : α) : Prop :=
  ∀ p used a next, m p used = .ok (a, next) → a = value

theorem ret_safe {α : Type} (a : α) : Safe (ret a) := by
  intro p used fits answer next checked
  cases Except.ok.inj checked
  exact fits

theorem ret_refines {α : Type} (a : α) : Refines (ret a) a := by
  intro p used answer next checked
  exact (congrArg Prod.fst (Except.ok.inj checked)).symm

theorem fail_safe {α : Type} (code : FailureCode) : Safe (fail (α := α) code) := by
  intro p used _ answer next checked
  contradiction

theorem fail_refines {α : Type} (code : FailureCode) (value : α) :
    Refines (fail code) value := by
  intro p used answer next checked
  contradiction

theorem withPhase_safe {α : Type} (phase : String) {m : M α}
    (safe : Safe m) : Safe (withPhase phase m) := by
  intro p used fits answer next checked
  unfold withPhase at checked
  cases hm : m p used with
  | error reason => cases reason <;> simp_all
  | ok result =>
    simp only [hm] at checked
    cases Except.ok.inj checked
    exact safe p used fits answer next hm

theorem withPhase_refines {α : Type} (phase : String) {m : M α} {value : α}
    (refines : Refines m value) : Refines (withPhase phase m) value := by
  intro p used answer next checked
  unfold withPhase at checked
  cases hm : m p used with
  | error reason => cases reason <;> simp_all
  | ok result =>
    simp only [hm] at checked
    cases Except.ok.inj checked
    exact refines p used answer next hm

theorem bind_safe {α β : Type} {m : M α} {k : α → M β}
    (first : Safe m) (second : ∀ a, Safe (k a)) : Safe (bind m k) := by
  intro p used fits answer next checked
  unfold bind at checked
  cases hm : m p used with
  | error reason => simp only [hm] at checked; contradiction
  | ok pair =>
    rcases pair with ⟨a, middle⟩
    simp only [hm] at checked
    exact second a p middle (first p used fits a middle hm) answer next checked

theorem bind_refines {α β : Type} {m : M α} {k : α → M β} {a : α} {b : β}
    (first : Refines m a) (second : Refines (k a) b) : Refines (bind m k) b := by
  intro p used answer next checked
  unfold bind at checked
  cases hm : m p used with
  | error reason => simp only [hm] at checked; contradiction
  | ok pair =>
    rcases pair with ⟨value, middle⟩
    simp only [hm] at checked
    have same := first p used value middle hm
    subst value
    exact second p middle answer next checked

theorem perform_safe {α : Type} (event : Event) (cost : Vector) (body : Unit → α) :
    Safe (perform event cost body) := by
  intro p used _ answer next checked
  unfold perform at checked
  cases paid : charge p event cost used with
  | error reason => simp only [paid] at checked; contradiction
  | ok actual =>
    simp only [paid] at checked
    cases Except.ok.inj checked
    exact (charge_sound paid).2.2

theorem perform_refines {α : Type} (event : Event) (cost : Vector) (body : Unit → α) :
    Refines (perform event cost body) (body ()) := by
  intro p used answer next checked
  unfold perform at checked
  cases paid : charge p event cost used with
  | error reason => simp only [paid] at checked; contradiction
  | ok actual =>
    simp only [paid] at checked
    exact (congrArg Prod.fst (Except.ok.inj checked)).symm

theorem perform_refuses_before_body {α : Type} (event : Event) (cost used : Vector)
    (p : Profile) (allowed : event.allows cost) (tooMuch : ¬ Fits p (bump used cost)) :
    ∀ body : Unit → α,
      perform event cost body p used = .error (.resource ⟨event, used, cost⟩) := by
  intro body
  unfold perform
  have refused : charge p event cost used = .error (.resource ⟨event, used, cost⟩) := by
    rw [charge, if_pos allowed, if_neg tooMuch]
  rw [refused]

/-- A primitive's action dimension and its conservative high-water descriptor.
No data operation is performed while this finite descriptor is constructed. -/
def cost (event : Event) (amount : Nat := 1) (bits degree : Nat := 0) : Vector := Vector.ofFn fun d =>
  if d = 13 then bits else if d = 14 then degree
  else if d = event.dimension then amount else 0

theorem cost_allowed (event : Event) (amount bits degree : Nat) :
    event.allows (cost event amount bits degree) := by
  intro d distinct water
  have d13 : d ≠ 13 := by
    intro h
    subst d
    simp [highWater] at water
  have d14 : d ≠ 14 := by
    intro h
    subst d
    simp [highWater] at water
  simp only [cost, Vector.ofFn_apply, if_neg d13, if_neg d14, if_neg distinct]

def tick (event : Event) (amount : Nat := 1) (bits degree : Nat := 0) : M Unit :=
  perform event (cost event amount bits degree) (fun _ => ())

theorem tick_safe (event : Event) (amount bits degree : Nat) :
    Safe (tick event amount bits degree) := perform_safe _ _ _

theorem tick_refines (event : Event) (amount bits degree : Nat) :
    Refines (tick event amount bits degree) () := perform_refines _ _ _

/-- Narrow limits after decoding them. Previously spent work is checked and
threaded unchanged; decoding limits cannot reset the run's vector. -/
def under {α : Type} (lower : Profile) (body : M α) : M α := fun outer used =>
  if LimitsLE lower outer then
    if Fits lower used then body lower used
    else .error (.context "wire_limits" (.resource ⟨.structural, used, zero⟩))
  else .error (.semantic .invalidInput used)

theorem under_safe {α : Type} (lower : Profile) {body : M α}
    (safe : Safe body) : Safe (under lower body) := by
  intro outer used _ answer next checked
  unfold under at checked
  split at checked
  · rename_i narrower
    split at checked
    · rename_i admitted
      exact Fits.mono narrower (safe lower used admitted answer next checked)
    · contradiction
  · contradiction

theorem under_refines {α : Type} (lower : Profile) {body : M α} {value : α}
    (refines : Refines body value) : Refines (under lower body) value := by
  intro outer used answer next checked
  unfold under at checked
  split at checked
  · split at checked
    · exact refines lower used answer next checked
    · contradiction
  · contradiction

theorem under_uses_previous {α : Type} {lower outer : Profile} {body : M α}
    {used : Vector} (admitted : LimitsLE lower outer ∧ Fits lower used) :
    under lower body outer used = body lower used := by
  rw [under, if_pos admitted.1, if_pos admitted.2]

theorem under_refuses_spent {α : Type} {lower outer : Profile} {body : M α}
    {used : Vector} (narrower : LimitsLE lower outer) (tooMuch : ¬ Fits lower used) :
    under lower body outer used =
      .error (.context "wire_limits" (.resource ⟨.structural, used, zero⟩)) := by
  rw [under, if_pos narrower, if_neg tooMuch]

theorem zero_fits (profile : Profile) : Fits profile zero := by
  simp [Fits, zero, totalWork]

/-- Validate the trusted numeric envelope before starting a fresh run. -/
def start {α : Type} (profile : Profile) (body : M α) : Except Refusal (α × Vector) :=
  if ValidProfile profile then body profile zero else .error (.semantic .invalidInput zero)

theorem start_bounded {α : Type} {profile : Profile} {body : M α}
    (safe : Safe body) {answer : α} {next : Vector}
    (checked : start profile body = .ok (answer, next)) :
    ValidProfile profile ∧ Fits profile next ∧ ∀ d, next d ≤ maxCounter := by
  unfold start at checked
  split at checked
  · rename_i valid
    have fits := safe profile zero (zero_fits _) answer next checked
    exact ⟨valid, fits, fun d => (fits.1 d).trans (valid.1 d)⟩
  · contradiction

end ExactCIs.Unconditional.ResourceModel
