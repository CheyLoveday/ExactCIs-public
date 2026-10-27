/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerCore
import ExactCIs.Unconditional.MeteredIntervalReplay

/-! # Concrete input validation for metered decoding and replay

String equality reserves its bounded traversal before comparison. Count sums
and tests and exact rational checks use charged integer/rational primitives.
This file is shared by the literal decoder and the typed global checker.
-/
namespace ExactCIs.Unconditional.MeteredDecodeInput

open ResourceModel MeteredProgram MeteredIntervalReplay

def stringEQ (a b : String) : Program Bool :=
  compose (perform .structural (cost .structural (a.utf8ByteSize + b.utf8ByteSize + 1))
    (fun _ => decide (a = b))) (fun _ => decide (a = b))
    (perform_safe _ _ _) (perform_refines _ _ _)

@[simp] theorem erase_stringEQ (a b : String) :
    (stringEQ a b).erase = decide (a = b) := rfl

def natAdd (a b : Nat) : Program Nat :=
  compose (perform .integer (cost .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b) + 1))
    (fun _ => a + b)) (fun _ => a + b)
    (perform_safe _ _ _) (perform_refines _ _ _)

@[simp] theorem erase_natAdd (a b : Nat) : (natAdd a b).erase = a + b := rfl

def natLE (a b : Nat) : Program Bool :=
  compose (perform .integer (cost .integer 1
    (max (MeteredRationalReplay.natBits a) (MeteredRationalReplay.natBits b)))
    (fun _ => decide (a ≤ b))) (fun _ => decide (a ≤ b))
    (perform_safe _ _ _) (perform_refines _ _ _)

@[simp] theorem erase_natLE (a b : Nat) : (natLE a b).erase = decide (a ≤ b) := rfl

def positiveNat (a : Nat) : Program Bool :=
  compose (perform .integer (cost .integer 1 (MeteredRationalReplay.natBits a))
    (fun _ => decide (0 < a))) (fun _ => decide (0 < a))
    (perform_safe _ _ _) (perform_refines _ _ _)

@[simp] theorem erase_positiveNat (a : Nat) :
    (positiveNat a).erase = decide (0 < a) := rfl

def divide (a b : Rat) : Program Rat :=
  compose (MeteredRationalReplay.ratDiv a b) (fun _ => a / b)
    (MeteredRationalReplay.ratDiv_safe _ _) (MeteredRationalReplay.ratDiv_refines _ _)

@[simp] theorem erase_divide (a b : Rat) : (divide a b).erase = a / b := rfl

def inputCheck (input : GlobalCheckerCore.Input) : Program Bool :=
  andThen (stringEQ input.schema "exactcis.boschloo.global-checker.input.v1") fun _ =>
    andThen (stringEQ input.method "boschloo") fun _ =>
      andThen (stringEQ input.estimand "odds_ratio") fun _ =>
        andThen (stringEQ input.design "independent_groups") fun _ => do
          let n1 ← natAdd input.table.a input.table.b
          andThen (positiveNat n1) fun _ => do
            let n0 ← natAdd input.table.c input.table.d
            andThen (positiveNat n0) fun _ =>
              andThen (le 0 input.alpha) fun _ =>
                andThen (le input.alpha 1) fun _ =>
                  andThen (do let half ← divide input.alpha 2; eq input.alphaSide half)
                    fun _ => le 0 input.tolerance

@[simp] theorem erase_inputCheck (input : GlobalCheckerCore.Input) :
    (inputCheck input).erase = GlobalCheckerCore.inputCheck input := by
  simp [inputCheck, GlobalCheckerCore.inputCheck, Table.n1, Table.n0,
    Bool.decide_and, Bool.and_assoc] <;> rfl

theorem inputCheck_safe (input : GlobalCheckerCore.Input) : Safe (inputCheck input).run :=
  run_safe _

theorem inputCheck_refines (input : GlobalCheckerCore.Input) :
    Refines (inputCheck input).run (GlobalCheckerCore.inputCheck input) := by
  rw [← erase_inputCheck]
  exact run_refines _

end ExactCIs.Unconditional.MeteredDecodeInput
