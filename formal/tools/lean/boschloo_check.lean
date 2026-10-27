/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredGlobalChecker

/-! Command-line adapter for the checked development reference. File IO and
JSON reporting are outside the logical work model. Only a successful literal
byte replay exposes a statistical result. The optional fifteen prior counters
continue construction work rather than starting a second allowance. -/
open ExactCIs.Unconditional ResourceModel

private def profile : Profile where
  caps := ResourceModel.Vector.ofFn fun d => match d.val with
    | 0 => 4000000
    | 1 => 64000000
    | 2 => 100000
    | 3 => 8000000
    | 4 => 2000000
    | 5 | 6 | 7 | 8 | 9 => 20000
    | 10 => 2000000
    | 11 => 8000000
    | 12 => 4000000000000
    | 13 => 4096
    | _ => 512
  polynomialOps := maxCounter
  rootChecks := maxCounter
  algebraicComparisons := maxCounter
  leaves := maxCounter
  totalWork := maxCounter

private def rational (q : Rat) : Lean.Json := Lean.Json.mkObj
  [("numerator", .str (toString q.num)), ("denominator", .str (toString q.den))]

private def resultJson : GlobalCheckerCore.Result → Lean.Json
  | .full => Lean.Json.mkObj [("kind", .str "FULL_CERTIFIED")]
  | .empty => Lean.Json.mkObj [("kind", .str "EMPTY_CERTIFIED")]
  | .hull lo hi => Lean.Json.mkObj [("kind", .str "HULL_CERTIFIED"),
      ("compact_lower", rational lo), ("compact_upper", rational hi)]

private def counters (used : ResourceModel.Vector) : Lean.Json :=
  .arr ((List.ofFn fun d : Fin 15 => Lean.Json.str (toString (used d))).toArray)

private def reply (status : String) (used : ResourceModel.Vector)
    (fields : List (String × Lean.Json) := []) : IO Unit :=
  IO.println (Lean.Json.mkObj ([("protocol", .str "exactcis.boschloo.method.check.v1"),
    ("profile", .str "BOSCHLOO_CHECKED_REFERENCE_V1"),
    ("status", .str status), ("counters", counters used)] ++ fields)).compress

private def resourceReason : ResourceModel.Refusal → String × ResourceModel.Vector
  | .resource detail => (s!"resource limit at {repr detail.event}", detail.previous)
  | .invalidDescriptor => ("invalid resource descriptor", ResourceModel.zero)
  | .semantic code previous => (s!"semantic refusal: {repr code}", previous)
  | .context phase reason =>
      let (message, used) := resourceReason reason
      (phase ++ ": " ++ message, used)

private def priorCounters (args : List String) : Except String ResourceModel.Vector := do
  if args.isEmpty then return ResourceModel.zero
  if args.length != 15 then throw "expected exactly fifteen prior counters"
  let values ← args.mapM fun text => do
    if text.length > 19 then throw "prior counter exceeds the supported word range"
    match text.toNat? with
    | none => throw "prior counters must be nonnegative decimal integers"
    | some n =>
      if n > maxCounter then throw "prior counter exceeds the supported word range"
      pure n
  pure (ResourceModel.Vector.ofFn fun d => values[d.val]!)

def main (args : List String) : IO UInt32 := do
  if args.length < 2 then
    reply "refused" ResourceModel.zero [("reason", .str
      "usage: boschloo_check INPUT_JSON PAYLOAD_JSON [15 prior counters]")]
    return 2
  match priorCounters (args.drop 2) with
  | .error message =>
    reply "refused" ResourceModel.zero [("reason", .str message)]
    return 2
  | .ok seed =>
    if !(decide (Fits profile seed)) then
      reply "refused" seed [("reason", .str "construction counters exceed the checker profile")]
      return 2
    try
      let inputPath : System.FilePath := args[0]!
      let payloadPath : System.FilePath := args[1]!
      if (← inputPath.metadata).byteSize.toNat > 2000000 ||
          (← payloadPath.metadata).byteSize.toNat > 2000000 then
        reply "refused" seed [("reason", .str "candidate file exceeds the two-million-byte file limit")]
        return 2
      let input ← IO.FS.readBinFile inputPath
      let payload ← IO.FS.readBinFile payloadPath
      match (MeteredGlobalChecker.bytes {} {degree := 512} input payload).run profile seed with
      | .error reason =>
        let (message, used) := resourceReason reason
        reply "refused" used [("reason", .str message)]
        return 2
      | .ok (.error (.input (.resource limit)), used) =>
        reply "refused" used [("reason", .str ("input shape limit: " ++ reprStr limit))]
        return 2
      | .ok (.error (.payload (.resource limit)), used) =>
        reply "refused" used [("reason", .str ("payload shape limit: " ++ reprStr limit))]
        return 2
      | .ok (.error reason, used) =>
        reply "rejected" used [("reason", .str (reprStr reason))]
        return 3
      | .ok (.ok result, used) =>
        reply "accepted" used [("result", resultJson result)]
        return 0
    catch error =>
      reply "refused" seed [("reason", .str ("checker IO failure: " ++ error.toString))]
      return 2
