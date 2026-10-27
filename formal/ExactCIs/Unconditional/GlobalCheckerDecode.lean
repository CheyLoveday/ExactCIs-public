/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoundedJson
import ExactCIs.Unconditional.GlobalCheckerCore
import ExactCIs.Unconditional.CanonicalEncoding
import ExactCIs.Unconditional.SpecializedWitnessWidth

/-! # Frozen-schema decoding into the proved global checker records

No proof fields or producer flags are decoded. All records below are the same
candidate records consumed by `GlobalCheckerCore.check`. Parse caps precede AST
allocation; degree/coefficient/digit/exponent caps precede typed expansion.
Input work limits are retained exactly. Semantic replay below is deliberately
named `semanticCheck`: polynomial-operation/root/comparison/total-work metering
and deterministic production remain separate, unfinished runtime obligations.
-/
namespace ExactCIs.Unconditional.GlobalCheckerDecode

open BoundedJson

abbrev Decode := StateT Nat (Except Refusal)

def require (condition : Bool) (reason : Refusal := .shape) : Decode Unit :=
  if condition then pure () else throw reason

def record (keys : List String) : Value → Decode (List (String × Value))
  | .object fields => do
      require (fields.length == keys.length &&
        keys.all (fun k => fields.any (fun p => p.1 == k))) .fields
      return fields
  | _ => throw .shape

def field (fields : List (String × Value)) (key : String) : Value :=
  (fields.find? (fun p => p.1 == key)).map Prod.snd |>.getD .null

def text : Value → Decode String
  | .string s => pure s
  | _ => throw .shape

def tag (v : Value) : Decode String := do
  match v with
  | .object fs => text (field fs "kind")
  | _ => throw .shape

def literalText (expected : String) (v : Value) : Decode String := do
  let s ← text v
  require (s == expected)
  return s

def array {α : Type} (decode : Value → Decode α) : Value → Decode (List α)
  | .array vs => vs.mapM decode
  | _ => throw .shape

def optional {α : Type} (decode : Value → Decode α) : Value → Decode (Option α)
  | .null => pure none
  | v => return some (← decode v)

def decimal (caps : Caps) (s : String) : Decode Nat := do
  -- Check byte length before allocating the character list or a bignum.
  require (s.utf8ByteSize ≤ caps.digits) (.resource .digits)
  let chars := s.toList
  require (!chars.isEmpty && chars.all (fun c => '0' ≤ c && c ≤ '9') &&
    (chars.length == 1 || chars.head! != '0')) .noncanonical
  return chars.foldl (fun n c => 10 * n + (c.toNat - 48)) 0

def natural (caps : Caps) (v : Value) : Decode Nat := do decimal caps (← text v)

def integer (caps : Caps) (v : Value) : Decode Int := do
  let s ← text v
  require (s.utf8ByteSize ≤ caps.digits + 1) (.resource .digits)
  match s.toList with
  | '-' :: cs =>
      let n ← decimal caps (String.ofList cs)
      require (n != 0) .noncanonical
      return -Int.ofNat n
  | _ => return Int.ofNat (← decimal caps s)

def rational (caps : Caps) (v : Value) : Decode ℚ := do
  let fs ← record ["numerator", "denominator"] v
  let n ← integer caps (field fs "numerator")
  let d ← natural caps (field fs "denominator")
  require (0 < d && n.natAbs.gcd d == 1) .noncanonical
  return (n : ℚ) / (d : ℚ)

def polynomial (caps : Caps) : Value → Decode RootCertificate.Coefficients
  | .array vs => do
      require (vs.length ≤ caps.degree + 1) (.resource .degree)
      let supplied ← get
      require (supplied + vs.length ≤ caps.coefficients) (.resource .coefficients)
      set (supplied + vs.length)
      let cs ← vs.mapM (rational caps)
      require (cs.isEmpty || cs.getLast! != 0) .noncanonical
      return cs
  | _ => throw .shape

def bivariate (caps : Caps) : Value → Decode AlgebraicSpecialization.Bivariate
  | .array vs => do
      require (vs.length ≤ caps.degree + 1) (.resource .degree)
      let cs ← vs.mapM (polynomial caps)
      require (cs.isEmpty || !cs.getLast!.isEmpty) .noncanonical
      return cs
  | _ => throw .shape

def exponent (caps : Caps) (v : Value) : Decode Nat := do
  let n ← natural caps v
  require (n ≤ caps.exponent) (.resource .exponent)
  return n

def sign : Value → Decode SignType
  | .number (-1) => pure (-1)
  | .number 0 => pure 0
  | .number 1 => pure 1
  | _ => throw .shape

def rootCount (caps : Caps) (v : Value) : Decode RootCountCertificate.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "exponent",
    "bezoutLeft", "bezoutRight", "tail", "quotients", "last"] v
  return {
    representative := ← polynomial caps (field fs "representative")
    quotient := ← polynomial caps (field fs "quotient")
    powerQuotient := ← polynomial caps (field fs "powerQuotient")
    exponent := ← exponent caps (field fs "exponent")
    bezoutLeft := ← polynomial caps (field fs "bezoutLeft")
    bezoutRight := ← polynomial caps (field fs "bezoutRight")
    tail := ← array (polynomial caps) (field fs "tail")
    quotients := ← array (polynomial caps) (field fs "quotients")
    last := ← rational caps (field fs "last") }

def algebraicRoot (caps : Caps) (v : Value) : Decode SelectedRoot.Root := do
  let fs ← record ["definer", "lower", "upper", "certificate"] v
  return {
    definer := ← polynomial caps (field fs "definer")
    lower := ← rational caps (field fs "lower")
    upper := ← rational caps (field fs "upper")
    certificate := ← rootCount caps (field fs "certificate") }

def point (caps : Caps) (v : Value) : Decode GlobalCheckerPoint.Point := do
  let kind ← tag v
  let fs ← record ["kind", "value"] v
  if kind == "rational" then return .rational (← rational caps (field fs "value"))
  else if kind == "algebraic" then return .algebraic (← algebraicRoot caps (field fs "value"))
  else throw .shape

def algebraicSign (caps : Caps) (v : Value) : Decode AlgebraicSignReplay.SignWitness := do
  let fs ← record ["sign", "quotient", "remainder"] v
  return {
    sign := ← sign (field fs "sign")
    quotient := ← polynomial caps (field fs "quotient")
    remainder := ← polynomial caps (field fs "remainder") }

def pointSign (caps : Caps) (v : Value) : Decode GlobalCheckerPoint.SignWitness := do
  match ← tag v with
  | "rational" => let _ ← record ["kind"] v; return .rational
  | "algebraic" =>
      let fs ← record ["kind", "witness"] v
      return .algebraic (← algebraicSign caps (field fs "witness"))
  | _ => throw .shape

def refinement (caps : Caps) (v : Value) : Decode SelectedRoot.Refinement := do
  let fs ← record ["lower", "upper", "certificate"] v
  return {
    lower := ← rational caps (field fs "lower")
    upper := ← rational caps (field fs "upper")
    certificate := ← rootCount caps (field fs "certificate") }

def rootOrder (caps : Caps) (v : Value) : Decode RootComparison.Certificate := do
  match ← tag v with
  | "less" =>
      let fs ← record ["kind", "left", "right"] v
      return .less (← refinement caps (field fs "left")) (← refinement caps (field fs "right"))
  | "greater" =>
      let fs ← record ["kind", "left", "right"] v
      return .greater (← refinement caps (field fs "left")) (← refinement caps (field fs "right"))
  | "equal" =>
      let fs ← record ["kind", "common", "leftQuotient", "rightQuotient"] v
      return .equal (← algebraicRoot caps (field fs "common"))
        (← polynomial caps (field fs "leftQuotient")) (← polynomial caps (field fs "rightQuotient"))
  | _ => throw .shape

def adjacentOrder (caps : Caps) (v : Value) : Decode GlobalCheckerOrder.Witness := do
  match ← tag v with
  | "rational_or_disjoint" => let _ ← record ["kind"] v; return .direct
  | "algebraic" =>
      let fs ← record ["kind", "witness"] v
      return .algebraic (← rootOrder caps (field fs "witness"))
  | _ => throw .shape

def rootMember (caps : Caps) (v : Value) : Decode GlobalCheckerProjection.Member := do
  let fs ← record ["point", "zero"] v
  return {
    point := ← natural caps (field fs "point")
    zero := ← pointSign caps (field fs "zero") }

def rootCover (caps : Caps) (v : Value) : Decode GlobalCheckerProjection.Cover := do
  let fs ← record ["polynomial", "certificate", "members"] v
  return {
    polynomial := ← polynomial caps (field fs "polynomial")
    certificate := ← rootCount caps (field fs "certificate")
    members := ← array (rootMember caps) (field fs "members") }

def openSign (caps : Caps) (v : Value) : Decode GlobalCheckerOpenSign.Witness := do
  match ← tag v with
  | "identity_zero" => let _ ← record ["kind"] v; return .identityZero
  | "root_free" =>
      let fs ← record ["kind", "sign", "certificate", "leftSigns", "rightSigns", "sample"] v
      let s ← sign (field fs "sign")
      require (s != 0)
      return .rootFree s (← rootCount caps (field fs "certificate"))
        (← array (pointSign caps) (field fs "leftSigns"))
        (← array (pointSign caps) (field fs "rightSigns")) (← rational caps (field fs "sample"))
  | _ => throw .shape

def parametricStep (caps : Caps) (v : Value) : Decode GlobalCheckerParametricRoot.Step := do
  let fs ← record ["quotient", "scale", "guard"] v
  return {
    quotient := ← bivariate caps (field fs "quotient")
    scale := ← polynomial caps (field fs "scale")
    guard := ← openSign caps (field fs "guard") }

def parametricRoot (caps : Caps) (v : Value) : Decode GlobalCheckerParametricRoot.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "bezoutLeft", "bezoutRight",
    "rootScale", "powerScale", "bezoutScale", "last", "rootGuard", "powerGuard", "bezoutGuard",
    "lastGuard", "exponent", "tail", "steps"] v
  return {
    representative := ← bivariate caps (field fs "representative")
    quotient := ← bivariate caps (field fs "quotient")
    powerQuotient := ← bivariate caps (field fs "powerQuotient")
    exponent := ← exponent caps (field fs "exponent")
    rootScale := ← polynomial caps (field fs "rootScale")
    powerScale := ← polynomial caps (field fs "powerScale")
    rootGuard := ← openSign caps (field fs "rootGuard")
    powerGuard := ← openSign caps (field fs "powerGuard")
    bezoutLeft := ← bivariate caps (field fs "bezoutLeft")
    bezoutRight := ← bivariate caps (field fs "bezoutRight")
    bezoutScale := ← polynomial caps (field fs "bezoutScale")
    bezoutGuard := ← openSign caps (field fs "bezoutGuard")
    tail := ← array (bivariate caps) (field fs "tail")
    steps := ← array (parametricStep caps) (field fs "steps")
    last := ← polynomial caps (field fs "last")
    lastGuard := ← openSign caps (field fs "lastGuard") }

def padWitness (caps : Caps) (width : Nat) (witness : AlgebraicSpecialization.Bivariate) :
    Decode AlgebraicSpecialization.Bivariate := do
  require (width ≤ caps.degree + 1) (.resource .degree)
  return SpecializedWitnessWidth.pad width witness

def padWitnesses (caps : Caps) : List Nat → List AlgebraicSpecialization.Bivariate →
    Decode (List AlgebraicSpecialization.Bivariate)
  | width :: widths, witness :: witnesses => do
      let head ← padWitness caps width witness
      let tail ← padWitnesses caps widths witnesses
      return head :: tail
  | _, witnesses => pure witnesses

def rehydrateWitnesses (caps : Caps) (originalWidth : Nat)
    (c : AlgebraicRootCertificate.Certificate) : Decode AlgebraicRootCertificate.Certificate := do
  let widths := SpecializedWitnessWidth.widths originalWidth c
  let root ← padWitness caps widths.root c.rootWitness
  let power ← padWitness caps widths.power c.powerWitness
  let bezout ← padWitness caps widths.bezout c.bezoutWitness
  let chain ← padWitnesses caps widths.chain c.witnesses
  let derivative ← padWitness caps widths.derivative c.derivativeWitness
  return { c with
    rootWitness := root
    powerWitness := power
    bezoutWitness := bezout
    witnesses := chain
    derivativeWitness := derivative }

def specializedRootWithWidth (caps : Caps) (originalWidth : Nat) (v : Value) :
    Decode AlgebraicRootCertificate.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "rootWitness", "powerWitness",
    "bezoutLeft", "bezoutRight", "bezoutWitness", "derivativeWitness", "last", "lastInverse",
    "lastQuotient", "exponent", "tail", "quotients", "witnesses"] v
  let c : AlgebraicRootCertificate.Certificate := {
    representative := ← bivariate caps (field fs "representative")
    quotient := ← bivariate caps (field fs "quotient")
    powerQuotient := ← bivariate caps (field fs "powerQuotient")
    exponent := ← exponent caps (field fs "exponent")
    rootWitness := ← bivariate caps (field fs "rootWitness")
    powerWitness := ← bivariate caps (field fs "powerWitness")
    bezoutLeft := ← bivariate caps (field fs "bezoutLeft")
    bezoutRight := ← bivariate caps (field fs "bezoutRight")
    bezoutWitness := ← bivariate caps (field fs "bezoutWitness")
    tail := ← array (bivariate caps) (field fs "tail")
    quotients := ← array (bivariate caps) (field fs "quotients")
    witnesses := ← array (bivariate caps) (field fs "witnesses")
    last := ← polynomial caps (field fs "last")
    lastInverse := ← polynomial caps (field fs "lastInverse")
    lastQuotient := ← polynomial caps (field fs "lastQuotient")
    derivativeWitness := ← bivariate caps (field fs "derivativeWitness") }
  rehydrateWitnesses caps originalWidth c

/-- Shape-only clients without an original objective retain the historical
    entry point. Literal payloads use `specializedRootWithWidth` below. -/
def specializedRoot (caps : Caps) (v : Value) : Decode AlgebraicRootCertificate.Certificate :=
  specializedRootWithWidth caps 0 v

def direction (dir : BoschlooOrdering.Direction) (v : Value) : Decode Unit := do
  let _ ← literalText (match dir with | .greater => "greater" | .less => "less") v

def openDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerOpenDecision.Certificate := do
  let kind ← tag v
  let keys := if kind == "interior_root" then
    ["kind", "direction", "ordering", "originalLeft", "originalRight", "root", "left", "right"]
    else ["kind", "direction", "ordering"]
  let fs ← record keys v
  direction dir (field fs "direction")
  let ordering ← array (openSign caps) (field fs "ordering")
  let branch ← match kind with
    | "full_mask" => pure .fullMask
    | "zero_level" => pure .zeroLevel
    | "interior_root" => pure (.interiorRoot {
        originalLeft := ← openSign caps (field fs "originalLeft")
        originalRight := ← openSign caps (field fs "originalRight")
        root := ← parametricRoot caps (field fs "root")
        left := ← array (openSign caps) (field fs "left")
        right := ← array (openSign caps) (field fs "right") })
    | _ => throw .shape
  return ⟨ordering, branch⟩

def pointDecisionWithWidth (caps : Caps) (originalWidth : Nat)
    (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerPointDecision.Certificate := do
  let kind ← tag v
  let keys := if kind == "rational_root" then ["kind", "direction", "ordering", "root"]
    else if kind == "algebraic_root" then
      ["kind", "direction", "ordering", "original", "root", "left", "right"]
    else ["kind", "direction", "ordering"]
  let fs ← record keys v
  direction dir (field fs "direction")
  let ordering ← array (pointSign caps) (field fs "ordering")
  let branch ← match kind with
    | "full_mask" => pure .fullMask
    | "zero_level" => pure .zeroLevel
    | "rational_root" => pure (.rationalRoot (← rootCount caps (field fs "root")))
    | "algebraic_root" => pure (.algebraicRoot {
        original := ← pointSign caps (field fs "original")
        root := ← specializedRootWithWidth caps originalWidth (field fs "root")
        left := ← array (pointSign caps) (field fs "left")
        right := ← array (pointSign caps) (field fs "right") })
    | _ => throw .shape
  return ⟨ordering, branch⟩

def pointDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerPointDecision.Certificate := pointDecisionWithWidth caps 0 dir v

def leafState (v : Value) : Decode GlobalCheckerLeaf.State := do
  match ← text v with
  | "ACCEPTED" => pure .accepted
  | "REJECTED_GREATER" => pure .rejectedGreater
  | "REJECTED_LESS" => pure .rejectedLess
  | "BOUNDARY_ENCLOSURE" => pure .boundary
  | _ => throw .shape

def leaf {α : Type} (decode : BoschlooOrdering.Direction → Value → Decode α)
    (v : Value) : Decode (GlobalCheckerLeaf.Leaf α) := do
  let fs ← record ["state", "greater", "less"] v
  return {
    state := ← leafState (field fs "state")
    greater := ← optional (decode .greater) (field fs "greater")
    less := ← optional (decode .less) (field fs "less") }

def anchor (caps : Caps) (v : Value) : Decode GlobalCheckerAnchor.Anchor := do
  match ← tag v with
  | "rational" =>
      let fs ← record ["kind", "value", "openCell"] v
      return .rational (← rational caps (field fs "value")) (← natural caps (field fs "openCell"))
  | "point" =>
      let fs ← record ["kind", "index"] v
      return .point (← natural caps (field fs "index"))
  | _ => throw .shape

def hullBranch (caps : Caps) (v : Value) : Decode GlobalCheckerHull.Branch := do
  match ← tag v with
  | "structural" =>
      let fs ← record ["kind", "endpoint"] v
      match ← text (field fs "endpoint") with
      | "zero" => pure (.structural .zero)
      | "one" => pure (.structural .infinity)
      | _ => throw .shape
  | "finite" =>
      let fs ← record ["kind", "anchor", "enclosureLower", "enclosureUpper"] v
      return .finite (← anchor caps (field fs "anchor"))
        (← rational caps (field fs "enclosureLower")) (← rational caps (field fs "enclosureUpper"))
  | _ => throw .shape

def terminal (caps : Caps) (v : Value) : Decode GlobalCheckerCore.Terminal := do
  match ← tag v with
  | "FULL_CERTIFIED" => let _ ← record ["kind"] v; return .full
  | "EMPTY_CERTIFIED" => let _ ← record ["kind"] v; return .empty
  | "HULL_CERTIFIED" =>
      let fs ← record ["kind", "outerLower", "outerUpper", "lower", "upper"] v
      return .hull (← rational caps (field fs "outerLower"))
        (← rational caps (field fs "outerUpper")) (← hullBranch caps (field fs "lower"))
        (← hullBranch caps (field fs "upper"))
  | _ => throw .shape

structure WorkLimits where
  payloadBytes : Nat
  integerDigits : Nat
  polynomialDegree : Nat
  polynomialOps : Nat
  rootChecks : Nat
  algebraicComparisons : Nat
  leaves : Nat
  totalWork : Nat
  deriving Repr

structure Input where
  core : GlobalCheckerCore.Input
  limits : WorkLimits

def workLimits (caps : Caps) (v : Value) : Decode WorkLimits := do
  let fs ← record ["payloadBytes", "integerDigits", "polynomialDegree", "polynomialOps",
    "rootChecks", "algebraicComparisons", "leaves", "totalWork"] v
  return {
    payloadBytes := ← natural caps (field fs "payloadBytes")
    integerDigits := ← natural caps (field fs "integerDigits")
    polynomialDegree := ← natural caps (field fs "polynomialDegree")
    polynomialOps := ← natural caps (field fs "polynomialOps")
    rootChecks := ← natural caps (field fs "rootChecks")
    algebraicComparisons := ← natural caps (field fs "algebraicComparisons")
    leaves := ← natural caps (field fs "leaves")
    totalWork := ← natural caps (field fs "totalWork") }

def input (caps : Caps) (v : Value) : Decode Input := do
  let fs ← record ["schema", "method", "estimand", "design", "a", "b", "c", "d", "alpha",
    "alphaSide", "hullEndpointExcessTolerance", "limits"] v
  let schema ← literalText "exactcis.boschloo.global-checker.input.v1" (field fs "schema")
  let method ← literalText "boschloo" (field fs "method")
  let estimand ← literalText "odds_ratio" (field fs "estimand")
  let design ← literalText "independent_groups" (field fs "design")
  let limits ← workLimits caps (field fs "limits")
  let caps := { caps with digits := min caps.digits limits.integerDigits }
  let a ← natural caps (field fs "a")
  let b ← natural caps (field fs "b")
  let c ← natural caps (field fs "c")
  let d ← natural caps (field fs "d")
  require (a + b ≤ caps.groupTotal && c + d ≤ caps.groupTotal) (.resource .groupTotal)
  let core : GlobalCheckerCore.Input := {
    schema := schema
    method := method
    estimand := estimand
    design := design
    table := ⟨a, b, c, d⟩
    alpha := ← rational caps (field fs "alpha")
    alphaSide := ← rational caps (field fs "alphaSide")
    tolerance := ← rational caps (field fs "hullEndpointExcessTolerance") }
  require (GlobalCheckerCore.inputCheck core) .invalidInput
  return ⟨core, limits⟩

def payloadCaps (caps : Caps) (i : Input) : Caps :=
  { caps with
    bytes := min caps.bytes i.limits.payloadBytes
    digits := min caps.digits i.limits.integerDigits
    degree := min caps.degree i.limits.polynomialDegree }

def leafArray {α : Type} (count : Nat) (decode : Value → Decode α)
    (v : Value) : Decode (List α) := do
  match v with
  | .array vs =>
      require (vs.length ≤ count) (.resource .leaves)
      vs.mapM decode
  | _ => throw .shape

def payload (caps : Caps) (i : Input) (v : Value) : Decode GlobalCheckerCore.Payload := do
  let fs ← record ["schema", "coordinate", "points", "adjacentOrder", "rootCovers",
    "openLeaves", "pointLeaves", "terminal"] v
  let openCount ← match field fs "openLeaves" with
    | .array vs => pure vs.length
    | _ => throw .shape
  let pointCount ← match field fs "pointLeaves" with
    | .array vs => pure vs.length
    | _ => throw .shape
  require (openCount + pointCount ≤ i.limits.leaves) (.resource .leaves)
  let originalWidth := (i.core.table.a + i.core.table.b) +
    (i.core.table.c + i.core.table.d) + 1
  return {
    schema := ← literalText "exactcis.boschloo.global-checker.payload.v1" (field fs "schema")
    coordinate := ← literalText "s=psi/(1+psi)" (field fs "coordinate")
    points := ← leafArray i.limits.leaves (point caps) (field fs "points")
    order := ← array (adjacentOrder caps) (field fs "adjacentOrder")
    covers := ← array (rootCover caps) (field fs "rootCovers")
    openLeaves := ← leafArray i.limits.leaves (leaf (openDecision caps)) (field fs "openLeaves")
    pointLeaves := ← leafArray i.limits.leaves
      (leaf (pointDecisionWithWidth caps originalWidth)) (field fs "pointLeaves")
    terminal := ← terminal caps (field fs "terminal") }

def decodeInput (caps : Caps) (bytes : ByteArray) : Except Refusal Input := do
  let v ← parse caps bytes
  return (← (input caps v).run 0).1

def decodePayload (caps : Caps) (i : Input) (bytes : ByteArray) :
    Except Refusal GlobalCheckerCore.Payload := do
  let caps := payloadCaps caps i
  let v ← parse caps bytes
  return (← (payload caps i v).run 0).1

inductive SemanticRefusal where
  | input (reason : Refusal)
  | payload (reason : Refusal)
  | certificate
  deriving DecidableEq, Repr

/-- Development semantic replay. WorkLimits are retained, not claimed as metered. -/
def semanticCheck (caps : Caps) (inputBytes payloadBytes : ByteArray) :
    Except SemanticRefusal GlobalCheckerCore.Result :=
  match decodeInput caps inputBytes with
  | .error reason => .error (.input reason)
  | .ok i => match decodePayload caps i payloadBytes with
    | .error reason => .error (.payload reason)
    | .ok p => match GlobalCheckerCore.check i.core p with
      | some result => .ok result
      | none => .error .certificate

theorem semanticCheck_sound {caps : Caps} {inputBytes payloadBytes : ByteArray}
    {result : GlobalCheckerCore.Result}
    (checked : semanticCheck caps inputBytes payloadBytes = .ok result) :
    ∃ i, decodeInput caps inputBytes = .ok i ∧ GlobalCheckerCore.ValidInput i.core ∧
      GlobalCheckerCore.ReturnContract i.core result := by
  unfold semanticCheck at checked
  cases hi : decodeInput caps inputBytes with
  | error reason => simp [hi] at checked
  | ok i =>
    simp only [hi] at checked
    cases hp : decodePayload caps i payloadBytes with
    | error reason => simp [hp] at checked
    | ok p =>
      simp only [hp] at checked
      cases hc : GlobalCheckerCore.check i.core p with
      | none => simp [hc] at checked
      | some answer =>
        have same : answer = result := by simpa [hc] using checked
        subst result
        exact ⟨i, rfl, GlobalCheckerCore.check_sound hc⟩

end ExactCIs.Unconditional.GlobalCheckerDecode
