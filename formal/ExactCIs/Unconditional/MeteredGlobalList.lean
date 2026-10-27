/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeInput
import ExactCIs.Unconditional.MeteredAlgebraicReplay

/-! # Charged traversal and bounded index-set operations for global replay

Index enumeration/sorting reserves bounded structural capacity before work.
These bodies contain bounded indices and tags only. Rational/polynomial
predicates run through their individual charged operations. Unused conservative
reservations are not refunded.
-/
namespace ExactCIs.Unconditional.MeteredGlobalList
open ResourceModel MeteredProgram MeteredIntervalReplay ProductBinomial

def length {α : Type} (xs : List α) : Program Nat :=
  compose (MeteredRationalReplay.lengthM xs) (fun _ => xs.length)
    (MeteredRationalReplay.lengthM_safe _) (MeteredRationalReplay.lengthM_refines _)
@[simp] theorem erase_length {α : Type} (xs : List α) : (length xs).erase = xs.length := rfl

def map {α β : Type} (f : α → Program β) (xs : List α) : Program (List β) :=
  compose (MeteredRationalReplay.mapM .structural (fun x => (f x).run) xs)
    (fun _ => xs.map fun x => (f x).erase)
    (MeteredRationalReplay.mapM_safe _ _ _ (fun x => run_safe (f x)))
    (MeteredRationalReplay.mapM_refines _ _ _ _ (fun x => run_refines (f x)))
@[simp] theorem erase_map {α β : Type} (f : α → Program β) (xs : List α) :
    (map f xs).erase = xs.map (fun x => (f x).erase) := rfl

def all {α : Type} (f : α → Program Bool) (xs : List α) : Program Bool :=
  compose (MeteredRationalReplay.allM (fun x => (f x).run) xs)
    (fun _ => xs.all fun x => (f x).erase)
    (MeteredRationalReplay.allM_safe _ _ (fun x => run_safe (f x)))
    (MeteredRationalReplay.allM_refines _ _ _ (fun x => run_refines (f x)))
@[simp] theorem erase_all {α : Type} (f : α → Program Bool) (xs : List α) :
    (all f xs).erase = xs.all (fun x => (f x).erase) := rfl

def any {α : Type} (f : α → Program Bool) (xs : List α) : Program Bool :=
  compose (MeteredRationalReplay.anyM (fun x => (f x).run) xs)
    (fun _ => xs.any fun x => (f x).erase)
    (MeteredRationalReplay.anyM_safe _ _ (fun x => run_safe (f x)))
    (MeteredRationalReplay.anyM_refines _ _ _ (fun x => run_refines (f x)))
@[simp] theorem erase_any {α : Type} (f : α → Program Bool) (xs : List α) :
    (any f xs).erase = xs.any (fun x => (f x).erase) := rfl

def append {α : Type} (xs ys : List α) : Program (List α) := do
  let n ← length xs
  compose (perform .structural (cost .structural n) (fun _ => xs ++ ys))
    (fun _ => xs ++ ys) (perform_safe _ _ _) (perform_refines _ _ _)
@[simp] theorem erase_append {α : Type} (xs ys : List α) :
    (append xs ys).erase = xs ++ ys := by simp [append]

def flatten {α : Type} (xss : List (List α)) : Program (List α) := visit fun _ =>
  match xss with
  | [] => pure []
  | xs :: xss => do let tail ← flatten xss; append xs tail
@[simp] theorem erase_flatten {α : Type} (xss : List (List α)) :
    (flatten xss).erase = xss.flatten := by
  induction xss <;> simp_all [flatten]

/-- A resource guard is erased; its failure never produces a successful value. -/
def requireResource (predicate : Program Bool) : Program Unit :=
  compose (ResourceModel.bind predicate.run (fun ok =>
    if ok then ret () else fail .unsupportedCertificateClass)) (fun _ => ())
    (bind_safe (run_safe predicate) (fun ok => by
      cases ok
      · exact fail_safe _
      · exact ret_safe _))
    (bind_refines (run_refines predicate) (by
      cases predicate.erase
      · exact fail_refines _ _
      · exact ret_refines _))
@[simp] theorem erase_requireResource (predicate : Program Bool) :
    (requireResource predicate).erase = () := rfl

/-- The integer comparison precedes traversal or subtraction of a wire index. -/
def get {α : Type} (xs : List α) (i : Nat) : Program (Option α) := do
  let n ← length xs
  let outside ← MeteredDecodeInput.natLE n i
  if outside then pure none else
    compose (perform .structural (cost .structural n) (fun _ => xs[i]?))
      (fun _ => xs[i]?) (perform_safe _ _ _) (perform_refines _ _ _)
@[simp] theorem erase_get {α : Type} (xs : List α) (i : Nat) :
    (get xs i).erase = xs[i]? := by
  simp only [get, erase_monadic_bind, erase_length, MeteredDecodeInput.erase_natLE]
  by_cases h : xs.length ≤ i
  · simp [h, List.getElem?_eq_none h]
  · simp [h]

/-- This primitive is restricted by its callers to bounded index data. -/
def indexWork {α : Type} (visits slots : Nat) (body : Unit → α) : Program α :=
  compose (do tick .sampleState visits
              perform .structural (cost .structural slots) body) body
    (bind_safe (tick_safe _ _ _ _) (fun _ => perform_safe _ _ _))
    (bind_refines (tick_refines _ _ _ _) (perform_refines _ _ _))
@[simp] theorem erase_indexWork {α : Type} (visits slots : Nat) (body : Unit → α) :
    (indexWork visits slots body).erase = body () := rfl

local instance lexAntisymm (n1 n0 : Nat) :
    Std.Antisymm (fun a b : Outcome n1 n0 => toLex a ≤ toLex b) :=
  ⟨fun _ _ hab hba => toLex.injective (le_antisymm hab hba)⟩

def outcomeSort {n1 n0 : Nat} (s : Finset (Outcome n1 n0)) : Program (List (Outcome n1 n0)) :=
  let grid := (n1+1)*(n0+1)
  indexWork grid (5*(grid+1)*(grid+1))
    (fun _ => s.sort (fun a b => toLex a ≤ toLex b))
@[simp] theorem erase_outcomeSort {n1 n0 : Nat} (s : Finset (Outcome n1 n0)) :
    (outcomeSort s).erase = s.sort (fun a b => toLex a ≤ toLex b) := rfl

def sampleUniverse (n1 n0 : Nat) : Program (Finset (Outcome n1 n0)) :=
  let grid := (n1+1)*(n0+1)
  indexWork grid (4*grid+n1+n0+4) (fun _ => Finset.univ)
@[simp] theorem erase_sampleUniverse (n1 n0 : Nat) :
    (sampleUniverse n1 n0).erase = Finset.univ := rfl

def allOutcomes {n1 n0 : Nat} (f : Outcome n1 n0 → Program Bool) : Program Bool := do
  let space ← sampleUniverse n1 n0
  let ordered ← outcomeSort space
  all f ordered
@[simp] theorem erase_allOutcomes {n1 n0 : Nat} (f : Outcome n1 n0 → Program Bool) :
    (allOutcomes f).erase = decide (∀ o, (f o).erase = true) := by
  apply Bool.eq_iff_iff.mpr
  simp [allOutcomes, List.all_eq_true]

private theorem filtered_zip_map {α : Type} (xs : List α) (f : α → Bool) :
    (((xs.zip (xs.map f)).filter fun p => p.2).map Prod.fst) = xs.filter f := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases h : f x <;> simp [h, ih]

def filterOutcomes {n1 n0 : Nat} (s : Finset (Outcome n1 n0))
    (f : Outcome n1 n0 → Program Bool) : Program (Finset (Outcome n1 n0)) := do
  let ordered ← outcomeSort s
  let answers ← map f ordered
  let grid := (n1+1)*(n0+1)
  indexWork 0 (6*(grid+1)*(grid+1)) (fun _ =>
    (((ordered.zip answers).filter fun p => p.2).map Prod.fst).toFinset)
@[simp] theorem erase_filterOutcomes {n1 n0 : Nat} (s : Finset (Outcome n1 n0))
    (f : Outcome n1 n0 → Program Bool) :
    (filterOutcomes s f).erase = s.filter (fun x => (f x).erase = true) := by
  simp only [filterOutcomes, erase_monadic_bind, erase_outcomeSort, erase_map, erase_indexWork]
  rw [filtered_zip_map]
  ext x
  simp
end ExactCIs.Unconditional.MeteredGlobalList
