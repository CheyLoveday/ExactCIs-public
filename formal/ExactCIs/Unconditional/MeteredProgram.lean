/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ResourceModel

/-! # Suspended composition of verified metered primitives

`erase` is used only in proofs. Runtime interpretation visits `run`, then
constructs the selected continuation. In particular, building a program does
not evaluate an erased arithmetic body. Atoms are a proof interface, not a claim
that arbitrary code is one primitive: concrete callers must use the audited
numeric/list/decoding operations and charge each recursive visit.
-/
namespace ExactCIs.Unconditional.MeteredProgram

open ResourceModel

structure Atom (α : Type) where
  erase : Unit → α
  run : M α
  safe : Safe run
  refines : Refines run (erase ())

inductive Program (α : Type) where
  | done (value : α)
  | step {β : Type} (action : Atom β) (next : β → Program α)

def Program.erase {α : Type} : Program α → α
  | .done value => value
  | .step action next => (next (action.erase ())).erase

/-- A direct self-tail interpreter. Keeping the state arguments explicit avoids
one retained interpreter call frame per primitive in large byte programs. -/
def Program.run {α : Type} (program : Program α) (profile : Profile) (used : Vector) :
    Except Refusal (α × Vector) :=
  match program with
  | .done value => .ok (value,used)
  | .step action next => match action.run profile used with
    | .error reason => .error reason
    | .ok (value,spent) => Program.run (next value) profile spent

theorem run_done {α : Type} (value : α) : (Program.done value).run = ret value := rfl

theorem run_step {α β : Type} (action : Atom β) (next : β → Program α) :
    (Program.step action next).run = ResourceModel.bind action.run (fun value => (next value).run) := by
  funext profile used
  simp only [Program.run, ResourceModel.bind]
  cases action.run profile used with
  | error reason => rfl
  | ok pair => cases pair; rfl

def Program.bind {α β : Type} : Program α → (α → Program β) → Program β
  | .done value, next => next value
  | .step action rest, next => .step action (fun value => (rest value).bind next)

instance : Monad Program where
  pure := Program.done
  bind := Program.bind

def atom {α : Type} (action : Atom α) : Program α := .step action .done

theorem run_safe {α : Type} (program : Program α) : Safe program.run := by
  induction program with
  | done value => exact ret_safe _
  | step action next ih =>
    rw [run_step]
    exact bind_safe action.safe ih

theorem run_refines {α : Type} (program : Program α) : Refines program.run program.erase := by
  induction program with
  | done value => exact ret_refines _
  | step action next ih =>
    rw [run_step]
    exact bind_refines action.refines (ih (action.erase ()))

@[simp] theorem erase_done {α : Type} (value : α) : (Program.done value).erase = value := rfl
@[simp] theorem erase_atom {α : Type} (action : Atom α) : (atom action).erase = action.erase () := rfl
@[simp] theorem erase_bind {α β : Type} (first : Program α) (next : α → Program β) :
    (first.bind next).erase = (next first.erase).erase := by
  induction first with
  | done value => rfl
  | step action rest ih => exact ih (action.erase ())

@[simp] theorem erase_monadic_bind {α β : Type}
    (first : Program α) (next : α → Program β) :
    (first >>= next).erase = (next first.erase).erase := erase_bind first next

@[simp] theorem erase_pure {α : Type} (value : α) :
    (pure value : Program α).erase = value := rfl

/-- This is composition, not a new primitive unit. -/
def compose {α : Type} (body : M α) (value : Unit → α)
    (safe : Safe body) (refines : Refines body (value ())) : Program α :=
  atom ⟨value, body, safe, refines⟩

/-- Only bounded dispatch, tags and indices belong in this atom. -/
def metadata {α : Type} (body : Unit → α) : Program α :=
  atom ⟨body, perform .structural (cost .structural 1) body,
    perform_safe _ _ _, perform_refines _ _ _⟩

@[simp] theorem erase_metadata {α : Type} (body : Unit → α) :
    (metadata body).erase = body () := rfl

/-- Suspend a branch behind its own traversal charge. -/
def visit {α : Type} (body : Unit → Program α) : Program α :=
  .step ⟨fun _ => (), tick .structural, tick_safe _ _ _ _, tick_refines _ _ _ _⟩ body

@[simp] theorem erase_visit {α : Type} (body : Unit → Program α) :
    (visit body).erase = (body ()).erase := rfl

end ExactCIs.Unconditional.MeteredProgram
