/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeJson
import ExactCIs.Unconditional.MeteredDecodePayload

/-! # Literal-byte entry points for metered decoding

These programs parse and decode in one resource vector. They do not call
`ResourceModel.start` or reset spent work; the caller starts once and may narrow
the profile using the decoded wire limits before payload/replay. Resource-only
word admission keeps every cap suitable for native counter routing.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram ResourceModel

def admitCaps (caps : Caps) : Program Unit := do
  let _ ← admitWord caps.bytes
  let _ ← admitWord caps.depth
  let _ ← admitWord caps.nodes
  let _ ← admitWord caps.array
  let _ ← admitWord caps.object
  let _ ← admitWord caps.string
  let _ ← admitWord caps.digits
  let _ ← admitWord caps.degree
  let _ ← admitWord caps.coefficients
  let _ ← admitWord caps.exponent
  let _ ← admitWord caps.groupTotal
  pure ()

@[simp] theorem erase_admitCaps (caps : Caps) : (admitCaps caps).erase = () := by
  simp [admitCaps]

def decodeInput (caps : Caps) (bytes : ByteArray) : Parser Input := do
  let _ ← liftP (admitCaps caps)
  let v ← parse caps bytes
  return (← (input caps v).run 0).1

def decodePayload (caps : Caps) (i : Input) (bytes : ByteArray) : Parser GlobalCheckerCore.Payload := do
  let _ ← liftP (admitCaps caps)
  let _ ← liftP (admitLimits i.limits)
  let caps := payloadCaps caps i
  let v ← parse caps bytes
  return (← (payload caps i v).run 0).1

@[simp] theorem erase_decodeInput (caps : Caps) (bytes : ByteArray) :
    eraseP (decodeInput caps bytes) = GlobalCheckerDecode.decodeInput caps bytes := by
  simp [decodeInput, GlobalCheckerDecode.decodeInput]

@[simp] theorem erase_decodePayload (caps : Caps) (i : Input) (bytes : ByteArray) :
    eraseP (decodePayload caps i bytes) = GlobalCheckerDecode.decodePayload caps i bytes := by
  simp [decodePayload, GlobalCheckerDecode.decodePayload, payloadCaps]

theorem decodeInput_safe (caps : Caps) (bytes : ByteArray) :
    Safe (decodeInput caps bytes).run.run := run_safe _

theorem decodePayload_safe (caps : Caps) (i : Input) (bytes : ByteArray) :
    Safe (decodePayload caps i bytes).run.run := run_safe _

theorem decodeInput_refines (caps : Caps) (bytes : ByteArray) :
    Refines (decodeInput caps bytes).run.run (GlobalCheckerDecode.decodeInput caps bytes) := by
  rw [← erase_decodeInput]
  exact run_refines _

theorem decodePayload_refines (caps : Caps) (i : Input) (bytes : ByteArray) :
    Refines (decodePayload caps i bytes).run.run (GlobalCheckerDecode.decodePayload caps i bytes) := by
  rw [← erase_decodePayload]
  exact run_refines _

end ExactCIs.Unconditional.MeteredDecode
