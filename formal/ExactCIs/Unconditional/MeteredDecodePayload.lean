/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeRecords

/-! # Metered input and payload decoding

Wire counters and table counts receive signed-63-bit admission before use in
runtime descriptors or bounded routing. This admission is resource-only: its
erasure does not change the frozen decoder's semantic grammar. Count sums and
the shared input validation use charged integer/rational operations.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram

abbrev WorkLimits := GlobalCheckerDecode.WorkLimits
abbrev Input := GlobalCheckerDecode.Input

def admitLimits (limits : WorkLimits) : Program Unit := do
  let _ ← admitWord limits.payloadBytes
  let _ ← admitWord limits.integerDigits
  let _ ← admitWord limits.polynomialDegree
  let _ ← admitWord limits.polynomialOps
  let _ ← admitWord limits.rootChecks
  let _ ← admitWord limits.algebraicComparisons
  let _ ← admitWord limits.leaves
  let _ ← admitWord limits.totalWork
  pure ()

@[simp] theorem erase_admitLimits (limits : WorkLimits) :
    (admitLimits limits).erase = () := by simp [admitLimits]

def workLimits (caps : Caps) (v : Value) : Decode WorkLimits := do
  let fs ← record ["payloadBytes", "integerDigits", "polynomialDegree", "polynomialOps",
    "rootChecks", "algebraicComparisons", "leaves", "totalWork"] v
  let limits : WorkLimits := {
    payloadBytes := ← natural caps (← field fs "payloadBytes")
    integerDigits := ← natural caps (← field fs "integerDigits")
    polynomialDegree := ← natural caps (← field fs "polynomialDegree")
    polynomialOps := ← natural caps (← field fs "polynomialOps")
    rootChecks := ← natural caps (← field fs "rootChecks")
    algebraicComparisons := ← natural caps (← field fs "algebraicComparisons")
    leaves := ← natural caps (← field fs "leaves")
    totalWork := ← natural caps (← field fs "totalWork") }
  let _ ← liftD (admitLimits limits)
  pure limits

@[simp] theorem erase_workLimits (caps : Caps) (v : Value) :
    eraseD (workLimits caps v) = GlobalCheckerDecode.workLimits caps v := by
  simp [workLimits, GlobalCheckerDecode.workLimits]

def input (caps : Caps) (v : Value) : Decode Input := do
  let fs ← record ["schema", "method", "estimand", "design", "a", "b", "c", "d", "alpha",
    "alphaSide", "hullEndpointExcessTolerance", "limits"] v
  let schema ← literalText "exactcis.boschloo.global-checker.input.v1" (← field fs "schema")
  let method ← literalText "boschloo" (← field fs "method")
  let estimand ← literalText "odds_ratio" (← field fs "estimand")
  let design ← literalText "independent_groups" (← field fs "design")
  let limits ← workLimits caps (← field fs "limits")
  let caps := { caps with digits := min caps.digits limits.integerDigits }
  let a ← natural caps (← field fs "a")
  let _ ← liftD (admitWord a)
  let b ← natural caps (← field fs "b")
  let _ ← liftD (admitWord b)
  let c ← natural caps (← field fs "c")
  let _ ← liftD (admitWord c)
  let d ← natural caps (← field fs "d")
  let _ ← liftD (admitWord d)
  let n1 ← liftD (MeteredDecodeInput.natAdd a b)
  let n0 ← liftD (MeteredDecodeInput.natAdd c d)
  let first ← liftD (MeteredDecodeInput.natLE n1 caps.groupTotal)
  let second ← liftD (MeteredDecodeInput.natLE n0 caps.groupTotal)
  require (first && second) (.resource .groupTotal)
  let core : GlobalCheckerCore.Input := {
    schema := schema
    method := method
    estimand := estimand
    design := design
    table := ⟨a, b, c, d⟩
    alpha := ← rational caps (← field fs "alpha")
    alphaSide := ← rational caps (← field fs "alphaSide")
    tolerance := ← rational caps (← field fs "hullEndpointExcessTolerance") }
  require (← liftD (MeteredDecodeInput.inputCheck core)) .invalidInput
  pure ⟨core, limits⟩

@[simp] theorem erase_input (caps : Caps) (v : Value) :
    eraseD (input caps v) = GlobalCheckerDecode.input caps v := by
  simp [input, GlobalCheckerDecode.input]

@[simp] theorem erase_input_run (caps : Caps) (v : Value) (supplied : Nat) :
    eraseP ((input caps v).run supplied) = (GlobalCheckerDecode.input caps v).run supplied :=
  congrFun (erase_input caps v) supplied

def payloadCaps (caps : Caps) (i : Input) : Caps := GlobalCheckerDecode.payloadCaps caps i

def leafArray {α : Type} (count : Nat) (decode : Value → Decode α)
    (v : Value) : Decode (List α) := do
  match v with
  | .array vs =>
      let n ← liftD (length vs)
      require (← liftD (MeteredDecodeInput.natLE n count)) (.resource .leaves)
      mapD decode vs
  | _ => throw .shape

@[simp] theorem erase_leafArray {α : Type} (n : Nat) (decode : Value → Decode α) (v : Value) :
    eraseD (leafArray n decode v) =
      GlobalCheckerDecode.leafArray n (fun v => eraseD (decode v)) v := by
  cases v <;> simp [leafArray, GlobalCheckerDecode.leafArray]

def arrayCount : Value → Decode Nat
  | .array vs => liftD (length vs)
  | _ => throw .shape

@[simp] theorem erase_arrayCount (v : Value) :
    eraseD (arrayCount v) = (match v with
      | .array vs => pure vs.length
      | _ => throw .shape : GlobalCheckerDecode.Decode Nat) := by
  cases v <;> simp [arrayCount]

def payload (caps : Caps) (i : Input) (v : Value) : Decode GlobalCheckerCore.Payload := do
  let fs ← record ["schema", "coordinate", "points", "adjacentOrder", "rootCovers",
    "openLeaves", "pointLeaves", "terminal"] v
  let openCount ← arrayCount (← field fs "openLeaves")
  let pointCount ← arrayCount (← field fs "pointLeaves")
  let total ← liftD (MeteredDecodeInput.natAdd openCount pointCount)
  require (← liftD (MeteredDecodeInput.natLE total i.limits.leaves)) (.resource .leaves)
  let n1 ← liftD (MeteredDecodeInput.natAdd i.core.table.a i.core.table.b)
  let n0 ← liftD (MeteredDecodeInput.natAdd i.core.table.c i.core.table.d)
  let total ← liftD (MeteredDecodeInput.natAdd n1 n0)
  let originalWidth ← liftD (MeteredDecodeInput.natAdd total 1)
  return {
    schema := ← literalText "exactcis.boschloo.global-checker.payload.v1" (← field fs "schema")
    coordinate := ← literalText "s=psi/(1+psi)" (← field fs "coordinate")
    points := ← leafArray i.limits.leaves (point caps) (← field fs "points")
    order := ← array (adjacentOrder caps) (← field fs "adjacentOrder")
    covers := ← array (rootCover caps) (← field fs "rootCovers")
    openLeaves := ← leafArray i.limits.leaves (leaf (openDecision caps)) (← field fs "openLeaves")
    pointLeaves := ← leafArray i.limits.leaves
      (leaf (pointDecisionWithWidth caps originalWidth)) (← field fs "pointLeaves")
    terminal := ← terminal caps (← field fs "terminal") }

@[simp] theorem erase_payload (caps : Caps) (i : Input) (v : Value) :
    eraseD (payload caps i v) = GlobalCheckerDecode.payload caps i v := by
  simp [payload, GlobalCheckerDecode.payload]
  congr 1
  funext fs
  cases ho : GlobalCheckerDecode.field fs "openLeaves" <;>
    cases hp : GlobalCheckerDecode.field fs "pointLeaves" <;> simp_all <;> rfl

@[simp] theorem erase_payload_run (caps : Caps) (i : Input) (v : Value) (supplied : Nat) :
    eraseP ((payload caps i v).run supplied) =
      (GlobalCheckerDecode.payload caps i v).run supplied :=
  congrFun (erase_payload caps i v) supplied

end ExactCIs.Unconditional.MeteredDecode
