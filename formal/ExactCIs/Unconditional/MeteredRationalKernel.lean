/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ResourceModel
import Init.Data.Rat.Lemmas
import Init.Data.Nat.Log2

/-! # Concrete precharged rational/list primitives

Only the four named rational wrappers below delegate rational arithmetic.
Cross-product comparisons expose their two integer products and integer test.
Polynomial recursion and output allocation use the same vector state. The
mathematical bridge to the existing root checker is in MeteredRationalReplay.
The counter units are delegated primitives, not machine instructions.
-/
namespace ExactCIs.Unconditional.MeteredRationalReplay

open ResourceModel

abbrev P := List Rat

def natBits (n : Nat) : Nat := if n = 0 then 0 else n.log2 + 1
def intBits (n : Int) : Nat := natBits n.natAbs
def ratBits (a : Rat) : Nat := max (intBits a.num) (natBits a.den)

def productBits (a b : Int) : Nat :=
  if a = 0 ∨ b = 0 then 0
  else if a = 1 ∨ a = -1 then intBits b
  else if b = 1 ∨ b = -1 then intBits a
  else intBits a + intBits b

def sumBits (a b : Rat) : Nat :=
  max
    (max (productBits a.num b.den) (productBits b.num a.den) + 1)
    (productBits a.den b.den)

def observe (a : Rat) : M Unit := tick .operand 0 (ratBits a)

def scalar {α : Type} (event : Event) (bits : Nat) (body : Unit → α) : M α :=
  perform event (cost event 1 bits) body

def ratAdd (a b : Rat) : M Rat := do
  observe a
  observe b
  scalar .ratAdd (sumBits a b) (fun _ => a + b)

def ratSub (a b : Rat) : M Rat := do
  observe a
  observe b
  scalar .ratSub (sumBits a b) (fun _ => a - b)

def ratMul (a b : Rat) : M Rat := do
  observe a
  observe b
  scalar .ratMul (max (productBits a.num b.num) (productBits a.den b.den)) (fun _ => a * b)

def ratDiv (a b : Rat) : M Rat := do
  observe a
  observe b
  if b.num = 0 then fail .zeroDenominator
  else scalar .ratDiv (max (productBits a.num b.den) (productBits a.den b.num)) (fun _ => a / b)

def intMul (a b : Int) : M Int :=
  scalar .integer (productBits a b) (fun _ => a * b)

def intLE (a b : Int) : M Bool :=
  scalar .integer (max (intBits a) (intBits b)) (fun _ => decide (a ≤ b))

def intLT (a b : Int) : M Bool :=
  scalar .integer (max (intBits a) (intBits b)) (fun _ => decide (a < b))

def intEQ (a b : Int) : M Bool :=
  scalar .integer (max (intBits a) (intBits b)) (fun _ => decide (a = b))

def ratLE (a b : Rat) : M Bool := do
  observe a
  observe b
  let left ← intMul a.num b.den
  let right ← intMul b.num a.den
  intLE left right

def ratLT (a b : Rat) : M Bool := do
  observe a
  observe b
  let left ← intMul a.num b.den
  let right ← intMul b.num a.den
  intLT left right

def ratEQ (a b : Rat) : M Bool := do
  observe a
  observe b
  let left ← intMul a.num b.den
  let right ← intMul b.num a.den
  intEQ left right

def ratOfNat (n : Nat) : M Rat :=
  scalar .integer (max 1 (natBits n)) (fun _ => (n : Rat))

/-- A traversal/dispatch marker precedes evaluation of the suspended branch. -/
def scan {α : Type} (body : Unit → M α) : M α := do
  tick .structural
  body ()

def lengthM {α : Type} (xs : List α) : M Nat := scan fun _ =>
  match xs with
  | [] => ret 0
  | _ :: tail => do
      let n ← lengthM tail
      ret (n + 1)

def cons (a : Rat) (as : P) : M P := do
  let n ← lengthM as
  tick .degree 0 0 n
  perform .coefficients (cost .coefficients 1) (fun _ => a :: as)

theorem observe_safe (a : Rat) : Safe (observe a) := tick_safe _ _ _ _
theorem observe_refines (a : Rat) : Refines (observe a) () := tick_refines _ _ _ _

theorem scalar_safe {α : Type} (event : Event) (bits : Nat) (body : Unit → α) :
    Safe (scalar event bits body) := perform_safe _ _ _
theorem scalar_refines {α : Type} (event : Event) (bits : Nat) (body : Unit → α) :
    Refines (scalar event bits body) (body ()) := perform_refines _ _ _

theorem ratAdd_safe (a b : Rat) : Safe (ratAdd a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ => scalar_safe _ _ _))
theorem ratSub_safe (a b : Rat) : Safe (ratSub a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ => scalar_safe _ _ _))
theorem ratMul_safe (a b : Rat) : Safe (ratMul a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ => scalar_safe _ _ _))

theorem ratAdd_refines (a b : Rat) : Refines (ratAdd a b) (a + b) :=
  bind_refines (observe_refines _) (bind_refines (observe_refines _) (scalar_refines _ _ _))
theorem ratSub_refines (a b : Rat) : Refines (ratSub a b) (a - b) :=
  bind_refines (observe_refines _) (bind_refines (observe_refines _) (scalar_refines _ _ _))
theorem ratMul_refines (a b : Rat) : Refines (ratMul a b) (a * b) :=
  bind_refines (observe_refines _) (bind_refines (observe_refines _) (scalar_refines _ _ _))

theorem ratDiv_safe (a b : Rat) : Safe (ratDiv a b) := by
  apply bind_safe (observe_safe _)
  intro _
  apply bind_safe (observe_safe _)
  intro _
  by_cases h : b.num = 0
  · simpa only [h, ↓reduceIte] using fail_safe (α := Rat) .zeroDenominator
  · simpa only [h, ↓reduceIte] using scalar_safe .ratDiv
      (max (productBits a.num b.den) (productBits a.den b.num)) (fun _ => a / b)

theorem ratDiv_refines (a b : Rat) : Refines (ratDiv a b) (a / b) := by
  apply bind_refines (observe_refines _)
  apply bind_refines (observe_refines _)
  by_cases h : b.num = 0
  · simpa only [h, ↓reduceIte] using fail_refines .zeroDenominator (a / b)
  · simpa only [h, ↓reduceIte] using scalar_refines .ratDiv
      (max (productBits a.num b.den) (productBits a.den b.num)) (fun _ => a / b)

theorem intMul_safe (a b : Int) : Safe (intMul a b) := scalar_safe _ _ _
theorem intMul_refines (a b : Int) : Refines (intMul a b) (a * b) := scalar_refines _ _ _
theorem intLE_safe (a b : Int) : Safe (intLE a b) := scalar_safe _ _ _
theorem intLT_safe (a b : Int) : Safe (intLT a b) := scalar_safe _ _ _
theorem intEQ_safe (a b : Int) : Safe (intEQ a b) := scalar_safe _ _ _
theorem intLE_refines (a b : Int) : Refines (intLE a b) (decide (a ≤ b)) := scalar_refines _ _ _
theorem intLT_refines (a b : Int) : Refines (intLT a b) (decide (a < b)) := scalar_refines _ _ _
theorem intEQ_refines (a b : Int) : Refines (intEQ a b) (decide (a = b)) := scalar_refines _ _ _

theorem ratLE_safe (a b : Rat) : Safe (ratLE a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ =>
    bind_safe (intMul_safe _ _) (fun left => bind_safe (intMul_safe _ _) (fun right =>
      intLE_safe left right))))
theorem ratLT_safe (a b : Rat) : Safe (ratLT a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ =>
    bind_safe (intMul_safe _ _) (fun left => bind_safe (intMul_safe _ _) (fun right =>
      intLT_safe left right))))
theorem ratEQ_safe (a b : Rat) : Safe (ratEQ a b) :=
  bind_safe (observe_safe _) (fun _ => bind_safe (observe_safe _) (fun _ =>
    bind_safe (intMul_safe _ _) (fun left => bind_safe (intMul_safe _ _) (fun right =>
      intEQ_safe left right))))

theorem ratLE_refines (a b : Rat) : Refines (ratLE a b) (decide (a ≤ b)) := by
  have h : Refines (ratLE a b) (decide (a.num * (b.den : Int) ≤ b.num * (a.den : Int))) :=
    bind_refines (observe_refines a) (bind_refines (observe_refines b)
    (bind_refines (intMul_refines a.num b.den)
      (bind_refines (intMul_refines b.num a.den)
        (intLE_refines (a.num * b.den) (b.num * a.den)))))
  simpa only [← Rat.le_iff] using h

theorem ratLT_refines (a b : Rat) : Refines (ratLT a b) (decide (a < b)) := by
  have h : Refines (ratLT a b) (decide (a.num * (b.den : Int) < b.num * (a.den : Int))) :=
    bind_refines (observe_refines a) (bind_refines (observe_refines b)
    (bind_refines (intMul_refines a.num b.den)
      (bind_refines (intMul_refines b.num a.den)
        (intLT_refines (a.num * b.den) (b.num * a.den)))))
  simpa only [← Rat.lt_iff] using h

theorem ratEQ_refines (a b : Rat) : Refines (ratEQ a b) (decide (a = b)) := by
  have equal : a = b ↔ a.num * (b.den : Int) = b.num * (a.den : Int) := by
    constructor
    · intro h; subst b; rfl
    · intro h
      apply Rat.le_antisymm
      · exact (Rat.le_iff _ _).mpr (Int.le_of_eq h)
      · exact (Rat.le_iff _ _).mpr (Int.le_of_eq h.symm)
  have h : Refines (ratEQ a b) (decide (a.num * (b.den : Int) = b.num * (a.den : Int))) :=
    bind_refines (observe_refines a) (bind_refines (observe_refines b)
    (bind_refines (intMul_refines a.num b.den)
      (bind_refines (intMul_refines b.num a.den)
        (intEQ_refines (a.num * b.den) (b.num * a.den)))))
  simpa only [← equal] using h

theorem ratOfNat_safe (n : Nat) : Safe (ratOfNat n) := scalar_safe _ _ _
theorem ratOfNat_refines (n : Nat) : Refines (ratOfNat n) (n : Rat) := scalar_refines _ _ _

theorem scan_safe {α : Type} {body : Unit → M α} (safe : Safe (body ())) :
    Safe (scan body) := bind_safe (tick_safe _ _ _ _) (fun _ => safe)
theorem scan_refines {α : Type} {body : Unit → M α} {value : α}
    (refines : Refines (body ()) value) : Refines (scan body) value :=
  bind_refines (tick_refines _ _ _ _) refines

theorem lengthM_safe {α : Type} (xs : List α) : Safe (lengthM xs) := by
  induction xs with
  | nil => exact scan_safe (ret_safe _)
  | cons x xs ih => exact scan_safe (bind_safe ih (fun _n => ret_safe (_n + 1)))

theorem lengthM_refines {α : Type} (xs : List α) : Refines (lengthM xs) xs.length := by
  induction xs with
  | nil => exact scan_refines (ret_refines _)
  | cons x xs ih => exact scan_refines (bind_refines ih (ret_refines _))

theorem cons_safe (a : Rat) (as : P) : Safe (cons a as) :=
  bind_safe (lengthM_safe _) (fun n => bind_safe (tick_safe _ _ _ _) (fun _ => perform_safe _ _ _))
theorem cons_refines (a : Rat) (as : P) : Refines (cons a as) (a :: as) :=
  bind_refines (lengthM_refines _) (bind_refines (tick_refines _ _ _ _) (perform_refines _ _ _))

namespace Plain

def add : P → P → P
  | [], bs => bs
  | as, [] => as
  | a :: as, b :: bs => (a + b) :: add as bs

def scale (a : Rat) : P → P
  | [] => []
  | b :: bs => (a * b) :: scale a bs

def mul : P → P → P
  | [], _ => []
  | a :: as, bs => add (scale a bs) (0 :: mul as bs)

def value : P → Rat → Rat
  | [], _ => 0
  | c :: cs, x => c + x * value cs x

def power (as : P) : Nat → P
  | 0 => [1]
  | n + 1 => mul as (power as n)

def derivative : P → P
  | [] => []
  | _ :: cs => add cs (0 :: derivative cs)

end Plain

def polyAdd (as bs : P) : M P := scan fun _ =>
  match as, bs with
  | [], bs => ret bs
  | as, [] => ret as
  | a :: as, b :: bs => do
      let head ← ratAdd a b
      let tail ← polyAdd as bs
      cons head tail

def polyScale (a : Rat) (bs : P) : M P := scan fun _ =>
  match bs with
  | [] => ret []
  | b :: bs => do
      let head ← ratMul a b
      let tail ← polyScale a bs
      cons head tail

def polyMul (as bs : P) : M P := scan fun _ =>
  match as with
  | [] => ret []
  | a :: as => do
      let head ← polyScale a bs
      let tail ← polyMul as bs
      let shifted ← cons 0 tail
      polyAdd head shifted

def polyValue (cs : P) (x : Rat) : M Rat := scan fun _ =>
  match cs with
  | [] => ret 0
  | c :: cs => do
      let tail ← polyValue cs x
      let product ← ratMul x tail
      ratAdd c product

def polyPower (as : P) (n : Nat) : M P := scan fun _ =>
  match n with
  | 0 => cons 1 []
  | n + 1 => do
      let previous ← polyPower as n
      polyMul as previous

def polyDerivative (cs : P) : M P := scan fun _ =>
  match cs with
  | [] => ret []
  | _ :: cs => do
      let previous ← polyDerivative cs
      let shifted ← cons 0 previous
      polyAdd cs shifted

theorem polyAdd_safe (as bs : P) : Safe (polyAdd as bs) := by
  induction as generalizing bs with
  | nil => exact scan_safe (ret_safe _)
  | cons a as ih =>
    cases bs with
    | nil => exact scan_safe (ret_safe _)
    | cons b bs =>
      apply scan_safe
      apply bind_safe (ratAdd_safe _ _)
      intro head
      apply bind_safe (ih bs)
      intro tail
      exact cons_safe _ _

theorem polyAdd_refines (as bs : P) : Refines (polyAdd as bs) (Plain.add as bs) := by
  induction as generalizing bs with
  | nil => exact scan_refines (ret_refines _)
  | cons a as ih =>
    cases bs with
    | nil => exact scan_refines (ret_refines _)
    | cons b bs =>
      apply scan_refines
      exact bind_refines (ratAdd_refines _ _)
        (bind_refines (ih bs) (cons_refines _ _))

theorem polyScale_safe (a : Rat) (bs : P) : Safe (polyScale a bs) := by
  induction bs with
  | nil => exact scan_safe (ret_safe _)
  | cons b bs ih =>
    apply scan_safe
    apply bind_safe (ratMul_safe _ _)
    intro head
    apply bind_safe ih
    intro tail
    exact cons_safe _ _

theorem polyScale_refines (a : Rat) (bs : P) :
    Refines (polyScale a bs) (Plain.scale a bs) := by
  induction bs with
  | nil => exact scan_refines (ret_refines _)
  | cons b bs ih =>
    apply scan_refines
    exact bind_refines (ratMul_refines _ _) (bind_refines ih (cons_refines _ _))

theorem polyMul_safe (as bs : P) : Safe (polyMul as bs) := by
  induction as with
  | nil => exact scan_safe (ret_safe _)
  | cons a as ih =>
    apply scan_safe
    apply bind_safe (polyScale_safe _ _)
    intro head
    apply bind_safe ih
    intro tail
    apply bind_safe (cons_safe _ _)
    intro shifted
    exact polyAdd_safe head shifted

theorem polyMul_refines (as bs : P) : Refines (polyMul as bs) (Plain.mul as bs) := by
  induction as with
  | nil => exact scan_refines (ret_refines _)
  | cons a as ih =>
    apply scan_refines
    exact bind_refines (polyScale_refines _ _) (bind_refines ih
      (bind_refines (cons_refines _ _) (polyAdd_refines _ _)))

theorem polyValue_safe (cs : P) (x : Rat) : Safe (polyValue cs x) := by
  induction cs with
  | nil => exact scan_safe (ret_safe _)
  | cons c cs ih =>
    apply scan_safe
    apply bind_safe ih
    intro tail
    apply bind_safe (ratMul_safe _ _)
    intro product
    exact ratAdd_safe _ _

theorem polyValue_refines (cs : P) (x : Rat) :
    Refines (polyValue cs x) (Plain.value cs x) := by
  induction cs with
  | nil => exact scan_refines (ret_refines _)
  | cons c cs ih =>
    apply scan_refines
    exact bind_refines ih (bind_refines (ratMul_refines _ _) (ratAdd_refines _ _))

theorem polyPower_safe (as : P) (n : Nat) : Safe (polyPower as n) := by
  induction n with
  | zero => exact scan_safe (cons_safe _ _)
  | succ n ih =>
    apply scan_safe
    apply bind_safe ih
    intro previous
    exact polyMul_safe _ _

theorem polyPower_refines (as : P) (n : Nat) :
    Refines (polyPower as n) (Plain.power as n) := by
  induction n with
  | zero => exact scan_refines (cons_refines _ _)
  | succ n ih => exact scan_refines (bind_refines ih (polyMul_refines _ _))


theorem polyDerivative_safe (cs : P) : Safe (polyDerivative cs) := by
  induction cs with
  | nil => exact scan_safe (ret_safe _)
  | cons c cs ih =>
    apply scan_safe
    apply bind_safe ih
    intro previous
    apply bind_safe (cons_safe _ _)
    intro shifted
    exact polyAdd_safe _ _

theorem polyDerivative_refines (cs : P) :
    Refines (polyDerivative cs) (Plain.derivative cs) := by
  induction cs with
  | nil => exact scan_refines (ret_refines _)
  | cons c cs ih =>
    exact scan_refines (bind_refines ih
      (bind_refines (cons_refines _ _) (polyAdd_refines _ _)))

def emit {α : Type} (event : Event) (a : α) (as : List α) : M (List α) :=
  perform event (cost event 1) (fun _ => a :: as)

theorem emit_safe {α : Type} (event : Event) (a : α) (as : List α) :
    Safe (emit event a as) := perform_safe _ _ _
theorem emit_refines {α : Type} (event : Event) (a : α) (as : List α) :
    Refines (emit event a as) (a :: as) := perform_refines _ _ _

def allM {α : Type} (f : α → M Bool) (xs : List α) : M Bool := scan fun _ =>
  match xs with
  | [] => ret true
  | x :: xs => do
      let answer ← f x
      if answer then allM f xs else ret false

def anyM {α : Type} (f : α → M Bool) (xs : List α) : M Bool := scan fun _ =>
  match xs with
  | [] => ret false
  | x :: xs => do
      let answer ← f x
      if answer then ret true else anyM f xs

def mapM {α β : Type} (event : Event) (f : α → M β) (xs : List α) : M (List β) := scan fun _ =>
  match xs with
  | [] => ret []
  | x :: xs => do
      let head ← f x
      let tail ← mapM event f xs
      emit event head tail

theorem allM_safe {α : Type} (f : α → M Bool) (xs : List α)
    (safe : ∀ x, Safe (f x)) : Safe (allM f xs) := by
  induction xs with
  | nil => exact scan_safe (ret_safe _)
  | cons x xs ih =>
    apply scan_safe
    apply bind_safe (safe x)
    intro answer
    cases answer
    · exact ret_safe _
    · exact ih

theorem allM_refines {α : Type} (f : α → M Bool) (g : α → Bool) (xs : List α)
    (refines : ∀ x, Refines (f x) (g x)) : Refines (allM f xs) (xs.all g) := by
  induction xs with
  | nil => exact scan_refines (ret_refines _)
  | cons x xs ih =>
    apply scan_refines
    apply bind_refines (refines x)
    cases hg : g x <;> simp only [hg, List.all_cons, Bool.false_and, Bool.true_and,
      Bool.false_eq_true, ↓reduceIte]
    · exact ret_refines _
    · exact ih

theorem anyM_safe {α : Type} (f : α → M Bool) (xs : List α)
    (safe : ∀ x, Safe (f x)) : Safe (anyM f xs) := by
  induction xs with
  | nil => exact scan_safe (ret_safe _)
  | cons x xs ih =>
    apply scan_safe
    apply bind_safe (safe x)
    intro answer
    cases answer
    · exact ih
    · exact ret_safe _

theorem anyM_refines {α : Type} (f : α → M Bool) (g : α → Bool) (xs : List α)
    (refines : ∀ x, Refines (f x) (g x)) : Refines (anyM f xs) (xs.any g) := by
  induction xs with
  | nil => exact scan_refines (ret_refines _)
  | cons x xs ih =>
    apply scan_refines
    apply bind_refines (refines x)
    cases hg : g x <;> simp only [hg, List.any_cons, Bool.false_or, Bool.true_or,
      Bool.false_eq_true, ↓reduceIte]
    · exact ih
    · exact ret_refines _

theorem mapM_safe {α β : Type} (event : Event) (f : α → M β) (xs : List α)
    (safe : ∀ x, Safe (f x)) : Safe (mapM event f xs) := by
  induction xs with
  | nil => exact scan_safe (ret_safe _)
  | cons x xs ih =>
    apply scan_safe
    apply bind_safe (safe x)
    intro head
    apply bind_safe ih
    intro tail
    exact emit_safe _ _ _

theorem mapM_refines {α β : Type} (event : Event) (f : α → M β) (g : α → β) (xs : List α)
    (refines : ∀ x, Refines (f x) (g x)) : Refines (mapM event f xs) (xs.map g) := by
  induction xs with
  | nil => exact scan_refines (ret_refines _)
  | cons x xs ih =>
    exact scan_refines (bind_refines (refines x) (bind_refines ih (emit_refines _ _ _)))

def andThen (first : M Bool) (second : Unit → M Bool) : M Bool := do
  let answer ← first
  if answer then second () else ret false

theorem andThen_safe {first : M Bool} {second : Unit → M Bool}
    (a : Safe first) (b : Safe (second ())) : Safe (andThen first second) := by
  apply bind_safe a
  intro answer
  cases answer
  · exact ret_safe _
  · exact b

theorem andThen_refines {first : M Bool} {second : Unit → M Bool} {a b : Bool}
    (ha : Refines first a) (hb : Refines (second ()) b) :
    Refines (andThen first second) (a && b) := by
  apply bind_refines ha
  cases a
  · exact ret_refines _
  · exact hb

def ratMin (a b : Rat) : M Rat := do
  let choose ← ratLE a b
  ret (if choose then a else b)

def ratMax (a b : Rat) : M Rat := do
  let choose ← ratLE a b
  ret (if choose then b else a)

namespace Plain

def chooseMin (a b : Rat) : Rat := if decide (a ≤ b) then a else b
def chooseMax (a b : Rat) : Rat := if decide (a ≤ b) then b else a

def bounds : P → Rat → Rat → Rat × Rat
  | [], _, _ => (0, 0)
  | c :: cs, l, u =>
    let b := bounds cs l u
    (c + chooseMin (l * b.1) (u * b.1), c + chooseMax (l * b.2) (u * b.2))

def identity (as bs : P) : Bool :=
  (add as (scale (-1) bs)).all fun x => decide (x = 0)

end Plain

theorem ratMin_safe (a b : Rat) : Safe (ratMin a b) :=
  bind_safe (ratLE_safe _ _) (fun _ => ret_safe _)
theorem ratMax_safe (a b : Rat) : Safe (ratMax a b) :=
  bind_safe (ratLE_safe _ _) (fun _ => ret_safe _)
theorem ratMin_refines (a b : Rat) : Refines (ratMin a b) (Plain.chooseMin a b) :=
  bind_refines (ratLE_refines _ _) (ret_refines _)
theorem ratMax_refines (a b : Rat) : Refines (ratMax a b) (Plain.chooseMax a b) :=
  bind_refines (ratLE_refines _ _) (ret_refines _)

def polyBounds (cs : P) (l u : Rat) : M (Rat × Rat) := scan fun _ =>
  match cs with
  | [] => ret (0, 0)
  | c :: cs => do
    let b ← polyBounds cs l u
    let llo ← ratMul l b.1
    let ulo ← ratMul u b.1
    let lhi ← ratMul l b.2
    let uhi ← ratMul u b.2
    let lower ← ratMin llo ulo
    let upper ← ratMax lhi uhi
    let resultLower ← ratAdd c lower
    let resultUpper ← ratAdd c upper
    ret (resultLower, resultUpper)

theorem polyBounds_safe (cs : P) (l u : Rat) : Safe (polyBounds cs l u) := by
  induction cs with
  | nil => exact scan_safe (ret_safe _)
  | cons c cs ih =>
    apply scan_safe
    apply bind_safe ih; intro b
    apply bind_safe (ratMul_safe _ _); intro llo
    apply bind_safe (ratMul_safe _ _); intro ulo
    apply bind_safe (ratMul_safe _ _); intro lhi
    apply bind_safe (ratMul_safe _ _); intro uhi
    apply bind_safe (ratMin_safe _ _); intro lower
    apply bind_safe (ratMax_safe _ _); intro upper
    apply bind_safe (ratAdd_safe _ _); intro resultLower
    apply bind_safe (ratAdd_safe _ _); intro resultUpper
    exact ret_safe _

theorem polyBounds_refines (cs : P) (l u : Rat) :
    Refines (polyBounds cs l u) (Plain.bounds cs l u) := by
  induction cs with
  | nil => exact scan_refines (ret_refines _)
  | cons c cs ih =>
    apply scan_refines
    apply bind_refines ih
    apply bind_refines (ratMul_refines _ _)
    apply bind_refines (ratMul_refines _ _)
    apply bind_refines (ratMul_refines _ _)
    apply bind_refines (ratMul_refines _ _)
    apply bind_refines (ratMin_refines _ _)
    apply bind_refines (ratMax_refines _ _)
    apply bind_refines (ratAdd_refines _ _)
    apply bind_refines (ratAdd_refines _ _)
    exact ret_refines _

def polyIdentity (as bs : P) : M Bool := do
  let negated ← polyScale (-1) bs
  let difference ← polyAdd as negated
  allM (fun x => ratEQ x 0) difference

theorem polyIdentity_safe (as bs : P) : Safe (polyIdentity as bs) := by
  apply bind_safe (polyScale_safe _ _); intro negated
  apply bind_safe (polyAdd_safe _ _); intro difference
  exact allM_safe _ _ (fun _ => ratEQ_safe _ _)

theorem polyIdentity_refines (as bs : P) :
    Refines (polyIdentity as bs) (Plain.identity as bs) :=
  bind_refines (polyScale_refines _ _) (bind_refines (polyAdd_refines _ _)
    (allM_refines _ _ _ (fun _ => ratEQ_refines _ _)))

end ExactCIs.Unconditional.MeteredRationalReplay
