/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalPolynomials
import ExactCIs.Unconditional.GlobalCheckerProjection

/-! # Charged mixed-point order and complete projection covers -/
namespace ExactCIs.Unconditional.MeteredGlobalOrder
open ResourceModel MeteredProgram MeteredIntervalReplay MeteredAlgebraicReplay
open GlobalCheckerPoint RootCertificate

def natEQ (a b : Nat) : Program Bool :=
  andThen (MeteredDecodeInput.natLE a b) fun _ => MeteredDecodeInput.natLE b a
@[simp] theorem erase_natEQ (a b : Nat) : (natEQ a b).erase = decide (a=b) := by
  simp [natEQ, ← Bool.decide_and, Nat.le_antisymm_iff]

def less (a b : Point) (w : GlobalCheckerOrder.Witness) : Program Bool :=
  andThen (point a) fun _ => andThen (point b) fun _ => visit fun _ =>
    match a, b, w with
    | .rational x, .rational y, .direct => lt x y
    | .rational x, .algebraic y, .direct => le x y.lower
    | .algebraic x, .rational y, .direct => le x.upper y
    | .algebraic x, .algebraic y, .direct => le x.upper y.lower
    | .algebraic x, .algebraic y, .algebraic c => do
      let result ← comparison x y c
      metadata fun _ => decide (result = some .lt)
    | _, _, _ => pure false
@[simp] theorem erase_less (a b : Point) (w : GlobalCheckerOrder.Witness) :
    (less a b w).erase = GlobalCheckerOrder.lessCheck a b w := by
  cases a <;> cases b <;> cases w <;>
    simp [less, GlobalCheckerOrder.lessCheck, Bool.and_assoc]

def interior (a : Point) : Program Bool :=
  andThen (point a) fun _ => visit fun _ => match a with
    | .rational q => andThen (lt 0 q) fun _ => lt q 1
    | .algebraic q => andThen (le 0 q.lower) fun _ => le q.upper 1
@[simp] theorem erase_interior (a : Point) :
    (interior a).erase = GlobalCheckerOrder.interiorCheck a := by
  cases a <;> simp [interior, GlobalCheckerOrder.interiorCheck, Bool.decide_and]

def order (ps : List Point) (ws : List GlobalCheckerOrder.Witness) : Program Bool :=
  visit fun _ => match ps, ws with
  | [], [] => pure true
  | [_], [] => pure true
  | a :: b :: ps, w :: ws => andThen (less a b w) fun _ => order (b :: ps) ws
  | _, _ => pure false
termination_by ps.length
@[simp] theorem erase_order (ps : List Point) (ws : List GlobalCheckerOrder.Witness) :
    (order ps ws).erase = GlobalCheckerOrder.check ps ws := by
  match ps, ws with
  | [], [] => simp [order, GlobalCheckerOrder.check]
  | [_], [] => simp [order, GlobalCheckerOrder.check]
  | a :: b :: ps, w :: ws =>
    simp [order, GlobalCheckerOrder.check, erase_order (b :: ps) ws]
  | [], _ :: _ => simp [order, GlobalCheckerOrder.check]
  | [_], _ :: _ => simp [order, GlobalCheckerOrder.check]
  | _ :: _ :: _, [] => simp [order, GlobalCheckerOrder.check]
termination_by ps.length

def member (points : List Point) (p : Coefficients)
    (m : GlobalCheckerProjection.Member) : Program Bool := do
  let _ ← tickP .projectionRoot
  let found ← MeteredGlobalList.get points m.point
  match found with
  | none => pure false
  | some a => andThen (interior a) fun _ => do
    let result ← pointSign p a m.zero
    metadata fun _ => decide (result = some 0)
@[simp] theorem erase_member (points : List Point) (p : Coefficients)
    (m : GlobalCheckerProjection.Member) :
    (member points p m).erase = GlobalCheckerProjection.memberCheck points p m := by
  simp only [member, erase_monadic_bind, erase_tickP, MeteredGlobalList.erase_get]
  cases h : points[m.point]? <;> simp [GlobalCheckerProjection.memberCheck, h]

@[simp] theorem any_decide_eq {α : Type} [DecidableEq α] (x : α) (xs : List α) :
    (xs.any fun y => decide (x=y)) = decide (x ∈ xs) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, decide_eq_true_eq]
  constructor
  · rintro ⟨y,hy,h⟩
    exact h.symm ▸ hy
  · intro hx
    exact ⟨x,hx,rfl⟩

def nodup (xs : List Nat) : Program Bool := visit fun _ => match xs with
  | [] => pure true
  | x :: xs => andThen (do
      let found ← MeteredGlobalList.any (natEQ x) xs
      metadata fun _ => !found) fun _ => nodup xs
@[simp] theorem erase_nodup (xs : List Nat) :
    (nodup xs).erase = decide xs.Nodup := by
  induction xs <;> simp_all [nodup, List.nodup_cons, Bool.decide_and]

def openCount (p : Coefficients) (c : RootCountCertificate.Certificate) : Program Nat := do
  let n ← rootCount c 0 1
  let endpoint ← value p 1
  let zero ← eq endpoint 0
  MeteredGlobalPolynomials.natSub n (if zero then 1 else 0)
@[simp] theorem erase_openCount (p : Coefficients) (c : RootCountCertificate.Certificate) :
    (openCount p c).erase = GlobalCheckerProjection.openCount p c := by
  simp [openCount, GlobalCheckerProjection.openCount]

def cover (points : List Point) (c : GlobalCheckerProjection.Cover) : Program Bool :=
  andThen (rootCheck c.polynomial c.certificate) fun _ =>
    andThen (do
      let ids ← MeteredGlobalList.map (fun m => metadata fun _ => m.point) c.members
      nodup ids) fun _ =>
        andThen (MeteredGlobalList.all (member points c.polynomial) c.members) fun _ => do
          let count ← openCount c.polynomial c.certificate
          let size ← MeteredGlobalList.length c.members
          natEQ count size
@[simp] theorem erase_cover (points : List Point) (c : GlobalCheckerProjection.Cover) :
    (cover points c).erase = GlobalCheckerProjection.check points c := by
  simp [cover, GlobalCheckerProjection.check, Bool.decide_and, Bool.and_assoc]

end ExactCIs.Unconditional.MeteredGlobalOrder
