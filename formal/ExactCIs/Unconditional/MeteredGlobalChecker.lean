/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalTerminal
import ExactCIs.Unconditional.MeteredDecode

/-! # Concrete global byte checker with one cumulative work vector

The input parser, payload parser, reconstruction, rational/algebraic replay,
complete cover and T1-min terminal checks all use the same state. Wire limits
can narrow the trusted profile after input decoding but cannot reset prior
work. Extra shape admission may refuse; every success refines the frozen core
and its actual Boschloo return contract. The pure erasure is proof-only.
-/
namespace ExactCIs.Unconditional.MeteredGlobalChecker
open ResourceModel MeteredProgram MeteredIntervalReplay

structure Shape where
  groupTotal : Nat := 128
  sampleGrid : Nat := 4096

def admitShape (shape : Shape) (input : GlobalCheckerCore.Input) : Program Unit := do
  let _ ← MeteredDecode.admitWord shape.groupTotal
  let _ ← MeteredDecode.admitWord shape.sampleGrid
  let _ ← MeteredDecode.admitWord input.table.a
  let _ ← MeteredDecode.admitWord input.table.b
  let _ ← MeteredDecode.admitWord input.table.c
  let _ ← MeteredDecode.admitWord input.table.d
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE input.table.a shape.groupTotal)
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE input.table.b shape.groupTotal)
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE input.table.c shape.groupTotal)
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE input.table.d shape.groupTotal)
  let n1 ← MeteredDecodeInput.natAdd input.table.a input.table.b
  let n0 ← MeteredDecodeInput.natAdd input.table.c input.table.d
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE n1 shape.groupTotal)
  let _ ← MeteredGlobalList.requireResource (MeteredDecodeInput.natLE n0 shape.groupTotal)
  let grid ← MeteredGlobalDecision.grid n1 n0
  MeteredGlobalList.requireResource (MeteredDecodeInput.natLE grid shape.sampleGrid)
@[simp] theorem erase_admitShape (shape : Shape) (input : GlobalCheckerCore.Input) :
    (admitShape shape input).erase = () := by simp [admitShape]

def check (shape : Shape) (input : GlobalCheckerCore.Input) (payload : GlobalCheckerCore.Payload) :
    Program (Option GlobalCheckerCore.Result) := do
  let _ ← admitShape shape input
  let valid ← andThen (MeteredDecodeInput.inputCheck input) fun _ =>
    andThen (MeteredDecodeInput.stringEQ payload.schema "exactcis.boschloo.global-checker.payload.v1")
      fun _ => MeteredDecodeInput.stringEQ payload.coordinate "s=psi/(1+psi)"
  if valid then
    let layout ← MeteredGlobalPartition.fromLists payload.points payload.openLeaves payload.pointLeaves
    match layout with
    | none => pure none
    | some chain => do
      let valid ← andThen (MeteredGlobalPartition.check (TableAt.of input.table)
        input.alphaSide chain payload.order) fun _ => do
          let points ← MeteredGlobalPartition.points chain
          let required ← MeteredGlobalFamily.required (TableAt.of input.table) input.alphaSide chain
          MeteredGlobalFamily.check points required payload.covers
      if valid then MeteredGlobalTerminal.terminal input chain payload.terminal else pure none
  else pure none
@[simp] theorem erase_check (shape : Shape) (input : GlobalCheckerCore.Input)
    (payload : GlobalCheckerCore.Payload) :
    (check shape input payload).erase = GlobalCheckerCore.check input payload := by
  simp only [check, erase_monadic_bind, erase_admitShape, erase_andThen,
    MeteredDecodeInput.erase_inputCheck, MeteredDecodeInput.erase_stringEQ,
    ← Bool.decide_and]
  split <;> simp only [GlobalCheckerCore.check, *]
  · try simp only [MeteredGlobalPartition.erase_fromLists]
    cases h : GlobalCheckerPartition.fromLists payload.points payload.openLeaves payload.pointLeaves <;>
      simp [h] <;> rfl
  · rfl

theorem check_safe (shape : Shape) (input : GlobalCheckerCore.Input)
    (payload : GlobalCheckerCore.Payload) : Safe (check shape input payload).run := run_safe _

theorem check_refines (shape : Shape) (input : GlobalCheckerCore.Input)
    (payload : GlobalCheckerCore.Payload) :
    Refines (check shape input payload).run (GlobalCheckerCore.check input payload) := by
  rw [← erase_check shape]
  exact run_refines _

theorem check_sound {shape : Shape} {input : GlobalCheckerCore.Input}
    {payload : GlobalCheckerCore.Payload} {result : GlobalCheckerCore.Result}
    {profile : Profile} {used next : ResourceModel.Vector}
    (success : (check shape input payload).run profile used = .ok (some result,next)) :
    GlobalCheckerCore.ValidInput input ∧ GlobalCheckerCore.ReturnContract input result := by
  exact GlobalCheckerCore.check_sound (check_refines shape input payload _ _ _ _ success).symm

/-- Byte dimension 0 remains cumulative input+payload. The payload-only cap is
enforced separately by `decodePayload`; it cannot erase input parsing costs. -/
def wireProfile (outer : Profile) (limits : GlobalCheckerDecode.WorkLimits) : Profile := {
  outer with
  caps := ResourceModel.Vector.ofFn fun d => if d = 14 then min (outer.caps d) limits.polynomialDegree else outer.caps d
  polynomialOps := min outer.polynomialOps limits.polynomialOps
  rootChecks := min outer.rootChecks limits.rootChecks
  algebraicComparisons := min outer.algebraicComparisons limits.algebraicComparisons
  leaves := min outer.leaves limits.leaves
  totalWork := min outer.totalWork limits.totalWork }

theorem wireProfile_le (outer : Profile) (limits : GlobalCheckerDecode.WorkLimits) :
    LimitsLE (wireProfile outer limits) outer := by
  refine ⟨?_, Nat.min_le_left _ _, Nat.min_le_left _ _, Nat.min_le_left _ _,
    Nat.min_le_left _ _, Nat.min_le_left _ _⟩
  intro d
  simp only [wireProfile, ResourceModel.Vector.ofFn_apply]
  split <;> simp [Nat.min_le_left]

def underWire {α : Type} (limits : GlobalCheckerDecode.WorkLimits) (body : M α) : M α :=
  fun outer used => under (wireProfile outer limits) body outer used
theorem underWire_safe {α : Type} (limits : GlobalCheckerDecode.WorkLimits) {body : M α}
    (safe : Safe body) : Safe (underWire limits body) := by
  intro outer used fits answer next success
  exact under_safe (wireProfile outer limits) safe outer used fits answer next success
theorem underWire_refines {α : Type} (limits : GlobalCheckerDecode.WorkLimits) {body : M α} {value : α}
    (refines : Refines body value) : Refines (underWire limits body) value := by
  intro outer used answer next success
  exact under_refines (wireProfile outer limits) refines outer used answer next success

def narrow {α : Type} (limits : GlobalCheckerDecode.WorkLimits) (body : Program α) : Program α :=
  compose (underWire limits body.run) (fun _ => body.erase)
    (underWire_safe limits (run_safe body)) (underWire_refines limits (run_refines body))
@[simp] theorem erase_narrow {α : Type} (limits : GlobalCheckerDecode.WorkLimits) (body : Program α) :
    (narrow limits body).erase = body.erase := rfl

def phase {α : Type} (name : String) (body : Program α) : Program α :=
  compose (withPhase name body.run) (fun _ => body.erase)
    (withPhase_safe name (run_safe body)) (withPhase_refines name (run_refines body))
@[simp] theorem erase_phase {α : Type} (name : String) (body : Program α) :
    (phase name body).erase = body.erase := rfl

def bytes (shape : Shape) (caps : BoundedJson.Caps) (inputBytes payloadBytes : ByteArray) :
    Program (Except GlobalCheckerDecode.SemanticRefusal GlobalCheckerCore.Result) := do
  let parsed ← phase "input" (MeteredDecode.decodeInput caps inputBytes).run
  match parsed with
  | .error reason => pure (.error (.input reason))
  | .ok i => narrow i.limits do
    let parsed ← phase "payload" (MeteredDecode.decodePayload caps i payloadBytes).run
    match parsed with
    | .error reason => pure (.error (.payload reason))
    | .ok p => do
      let checked ← phase "global_replay" (check shape i.core p)
      pure (match checked with
        | some result => .ok result
        | none => .error .certificate)
@[simp] theorem erase_bytes (shape : Shape) (caps : BoundedJson.Caps)
    (inputBytes payloadBytes : ByteArray) :
    (bytes shape caps inputBytes payloadBytes).erase =
      GlobalCheckerDecode.semanticCheck caps inputBytes payloadBytes := by
  have input_erasure := MeteredDecode.erase_decodeInput caps inputBytes
  change (MeteredDecode.decodeInput caps inputBytes).run.erase = _ at input_erasure
  simp only [bytes, erase_monadic_bind, erase_phase, input_erasure]
  cases hi : GlobalCheckerDecode.decodeInput caps inputBytes with
  | error reason => simp [GlobalCheckerDecode.semanticCheck, hi]
  | ok i =>
    have payload_erasure := MeteredDecode.erase_decodePayload caps i payloadBytes
    change (MeteredDecode.decodePayload caps i payloadBytes).run.erase = _ at payload_erasure
    simp only [erase_narrow, erase_monadic_bind, erase_phase, payload_erasure]
    cases hp : GlobalCheckerDecode.decodePayload caps i payloadBytes <;>
      simp [GlobalCheckerDecode.semanticCheck, hi, hp] <;> rfl

def run (shape : Shape) (caps : BoundedJson.Caps) (profile : Profile)
    (inputBytes payloadBytes : ByteArray) :=
  start profile (bytes shape caps inputBytes payloadBytes).run

theorem bytes_refines (shape : Shape) (caps : BoundedJson.Caps) (inputBytes payloadBytes : ByteArray) :
    Refines (bytes shape caps inputBytes payloadBytes).run
      (GlobalCheckerDecode.semanticCheck caps inputBytes payloadBytes) := by
  rw [← erase_bytes shape]
  exact run_refines _

theorem bytes_sound {shape : Shape} {caps : BoundedJson.Caps} {inputBytes payloadBytes : ByteArray}
    {result : GlobalCheckerCore.Result} {profile : Profile} {used next : ResourceModel.Vector}
    (success : (bytes shape caps inputBytes payloadBytes).run profile used = .ok (.ok result,next)) :
    ∃ i, GlobalCheckerDecode.decodeInput caps inputBytes = .ok i ∧
      GlobalCheckerCore.ValidInput i.core ∧ GlobalCheckerCore.ReturnContract i.core result := by
  exact GlobalCheckerDecode.semanticCheck_sound
    (bytes_refines shape caps inputBytes payloadBytes _ _ _ _ success).symm

theorem run_bounded {shape : Shape} {caps : BoundedJson.Caps} {inputBytes payloadBytes : ByteArray}
    {profile : Profile} {answer : Except GlobalCheckerDecode.SemanticRefusal GlobalCheckerCore.Result}
    {next : ResourceModel.Vector} (success : run shape caps profile inputBytes payloadBytes = .ok (answer,next)) :
    Fits profile next := (start_bounded (run_safe _) success).2.1

end ExactCIs.Unconditional.MeteredGlobalChecker
