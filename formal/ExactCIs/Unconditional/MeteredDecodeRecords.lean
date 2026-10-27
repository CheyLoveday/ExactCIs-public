/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.MeteredDecodeWitnessWidth
import Mathlib.Tactic.FailIfNoProgress

/-! # Metered certificate record constructors

Every field access uses the charged lookup, every array uses the charged typed
slot traversal, and every scalar delegates to the metered canonical decoder.
The record constructor itself is fixed-size dispatch and tuple construction.
-/
namespace ExactCIs.Unconditional.MeteredDecode

open BoundedJson MeteredProgram

def dispatchText (v : Value) : Decode String := do
  let s ← text v
  let _ ← liftD (reserve .structural (16 * (s.utf8ByteSize + 1)))
  pure s

@[simp] theorem erase_dispatchText (v : Value) :
    eraseD (dispatchText v) = GlobalCheckerDecode.text v := by simp [dispatchText]

def index (caps : Caps) (v : Value) : Decode Nat := do
  let n ← natural caps v
  let _ ← liftD (admitWord n)
  pure n

@[simp] theorem erase_index (caps : Caps) (v : Value) :
    eraseD (index caps v) = GlobalCheckerDecode.natural caps v := by simp [index]

def rootCount (caps : Caps) (v : Value) : Decode RootCountCertificate.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "exponent",
    "bezoutLeft", "bezoutRight", "tail", "quotients", "last"] v
  return {
    representative := ← polynomial caps (← field fs "representative")
    quotient := ← polynomial caps (← field fs "quotient")
    powerQuotient := ← polynomial caps (← field fs "powerQuotient")
    exponent := ← exponent caps (← field fs "exponent")
    bezoutLeft := ← polynomial caps (← field fs "bezoutLeft")
    bezoutRight := ← polynomial caps (← field fs "bezoutRight")
    tail := ← array (polynomial caps) (← field fs "tail")
    quotients := ← array (polynomial caps) (← field fs "quotients")
    last := ← rational caps (← field fs "last") }

@[simp] theorem erase_rootCount (caps : Caps) (v : Value) :
    eraseD (rootCount caps v) = GlobalCheckerDecode.rootCount caps v := by
  simp [rootCount, GlobalCheckerDecode.rootCount]

def algebraicRoot (caps : Caps) (v : Value) : Decode SelectedRoot.Root := do
  let fs ← record ["definer", "lower", "upper", "certificate"] v
  return {
    definer := ← polynomial caps (← field fs "definer")
    lower := ← rational caps (← field fs "lower")
    upper := ← rational caps (← field fs "upper")
    certificate := ← rootCount caps (← field fs "certificate") }

@[simp] theorem erase_algebraicRoot (caps : Caps) (v : Value) :
    eraseD (algebraicRoot caps v) = GlobalCheckerDecode.algebraicRoot caps v := by
  simp [algebraicRoot, GlobalCheckerDecode.algebraicRoot]

def point (caps : Caps) (v : Value) : Decode GlobalCheckerPoint.Point := do
  let kind ← tag v
  let fs ← record ["kind", "value"] v
  if kind == "rational" then return .rational (← rational caps (← field fs "value"))
  else if kind == "algebraic" then return .algebraic (← algebraicRoot caps (← field fs "value"))
  else throw .shape

@[simp] theorem erase_point (caps : Caps) (v : Value) :
    eraseD (point caps v) = GlobalCheckerDecode.point caps v := by
  simp [point, GlobalCheckerDecode.point]

def algebraicSign (caps : Caps) (v : Value) : Decode AlgebraicSignReplay.SignWitness := do
  let fs ← record ["sign", "quotient", "remainder"] v
  return {
    sign := ← sign (← field fs "sign")
    quotient := ← polynomial caps (← field fs "quotient")
    remainder := ← polynomial caps (← field fs "remainder") }

@[simp] theorem erase_algebraicSign (caps : Caps) (v : Value) :
    eraseD (algebraicSign caps v) = GlobalCheckerDecode.algebraicSign caps v := by
  simp [algebraicSign, GlobalCheckerDecode.algebraicSign]

def pointSign (caps : Caps) (v : Value) : Decode GlobalCheckerPoint.SignWitness := do
  match ← tag v with
  | "rational" => let _ ← record ["kind"] v; return .rational
  | "algebraic" =>
      let fs ← record ["kind", "witness"] v
      return .algebraic (← algebraicSign caps (← field fs "witness"))
  | _ => throw .shape

@[simp] theorem erase_pointSign (caps : Caps) (v : Value) :
    eraseD (pointSign caps v) = GlobalCheckerDecode.pointSign caps v := by
  simp [pointSign, GlobalCheckerDecode.pointSign]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def refinement (caps : Caps) (v : Value) : Decode SelectedRoot.Refinement := do
  let fs ← record ["lower", "upper", "certificate"] v
  return {
    lower := ← rational caps (← field fs "lower")
    upper := ← rational caps (← field fs "upper")
    certificate := ← rootCount caps (← field fs "certificate") }

@[simp] theorem erase_refinement (caps : Caps) (v : Value) :
    eraseD (refinement caps v) = GlobalCheckerDecode.refinement caps v := by
  simp [refinement, GlobalCheckerDecode.refinement]

def rootOrder (caps : Caps) (v : Value) : Decode RootComparison.Certificate := do
  match ← tag v with
  | "less" =>
      let fs ← record ["kind", "left", "right"] v
      return .less (← refinement caps (← field fs "left")) (← refinement caps (← field fs "right"))
  | "greater" =>
      let fs ← record ["kind", "left", "right"] v
      return .greater (← refinement caps (← field fs "left")) (← refinement caps (← field fs "right"))
  | "equal" =>
      let fs ← record ["kind", "common", "leftQuotient", "rightQuotient"] v
      return .equal (← algebraicRoot caps (← field fs "common"))
        (← polynomial caps (← field fs "leftQuotient")) (← polynomial caps (← field fs "rightQuotient"))
  | _ => throw .shape

@[simp] theorem erase_rootOrder (caps : Caps) (v : Value) :
    eraseD (rootOrder caps v) = GlobalCheckerDecode.rootOrder caps v := by
  simp [rootOrder, GlobalCheckerDecode.rootOrder]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def adjacentOrder (caps : Caps) (v : Value) : Decode GlobalCheckerOrder.Witness := do
  match ← tag v with
  | "rational_or_disjoint" => let _ ← record ["kind"] v; return .direct
  | "algebraic" =>
      let fs ← record ["kind", "witness"] v
      return .algebraic (← rootOrder caps (← field fs "witness"))
  | _ => throw .shape

@[simp] theorem erase_adjacentOrder (caps : Caps) (v : Value) :
    eraseD (adjacentOrder caps v) = GlobalCheckerDecode.adjacentOrder caps v := by
  simp [adjacentOrder, GlobalCheckerDecode.adjacentOrder]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def rootMember (caps : Caps) (v : Value) : Decode GlobalCheckerProjection.Member := do
  let fs ← record ["point", "zero"] v
  return {
    point := ← index caps (← field fs "point")
    zero := ← pointSign caps (← field fs "zero") }

@[simp] theorem erase_rootMember (caps : Caps) (v : Value) :
    eraseD (rootMember caps v) = GlobalCheckerDecode.rootMember caps v := by
  simp [rootMember, GlobalCheckerDecode.rootMember]

def rootCover (caps : Caps) (v : Value) : Decode GlobalCheckerProjection.Cover := do
  let fs ← record ["polynomial", "certificate", "members"] v
  return {
    polynomial := ← polynomial caps (← field fs "polynomial")
    certificate := ← rootCount caps (← field fs "certificate")
    members := ← array (rootMember caps) (← field fs "members") }

@[simp] theorem erase_rootCover (caps : Caps) (v : Value) :
    eraseD (rootCover caps v) = GlobalCheckerDecode.rootCover caps v := by
  simp [rootCover, GlobalCheckerDecode.rootCover]

def openSign (caps : Caps) (v : Value) : Decode GlobalCheckerOpenSign.Witness := do
  match ← tag v with
  | "identity_zero" => let _ ← record ["kind"] v; return .identityZero
  | "root_free" =>
      let fs ← record ["kind", "sign", "certificate", "leftSigns", "rightSigns", "sample"] v
      let s ← sign (← field fs "sign")
      require (s != 0)
      return .rootFree s (← rootCount caps (← field fs "certificate"))
        (← array (pointSign caps) (← field fs "leftSigns"))
        (← array (pointSign caps) (← field fs "rightSigns")) (← rational caps (← field fs "sample"))
  | _ => throw .shape

@[simp] theorem erase_openSign (caps : Caps) (v : Value) :
    eraseD (openSign caps v) = GlobalCheckerDecode.openSign caps v := by
  simp [openSign, GlobalCheckerDecode.openSign]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def parametricStep (caps : Caps) (v : Value) : Decode GlobalCheckerParametricRoot.Step := do
  let fs ← record ["quotient", "scale", "guard"] v
  return {
    quotient := ← bivariate caps (← field fs "quotient")
    scale := ← polynomial caps (← field fs "scale")
    guard := ← openSign caps (← field fs "guard") }

@[simp] theorem erase_parametricStep (caps : Caps) (v : Value) :
    eraseD (parametricStep caps v) = GlobalCheckerDecode.parametricStep caps v := by
  simp [parametricStep, GlobalCheckerDecode.parametricStep]

def parametricRoot (caps : Caps) (v : Value) : Decode GlobalCheckerParametricRoot.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "bezoutLeft", "bezoutRight",
    "rootScale", "powerScale", "bezoutScale", "last", "rootGuard", "powerGuard", "bezoutGuard",
    "lastGuard", "exponent", "tail", "steps"] v
  return {
    representative := ← bivariate caps (← field fs "representative")
    quotient := ← bivariate caps (← field fs "quotient")
    powerQuotient := ← bivariate caps (← field fs "powerQuotient")
    exponent := ← exponent caps (← field fs "exponent")
    rootScale := ← polynomial caps (← field fs "rootScale")
    powerScale := ← polynomial caps (← field fs "powerScale")
    rootGuard := ← openSign caps (← field fs "rootGuard")
    powerGuard := ← openSign caps (← field fs "powerGuard")
    bezoutLeft := ← bivariate caps (← field fs "bezoutLeft")
    bezoutRight := ← bivariate caps (← field fs "bezoutRight")
    bezoutScale := ← polynomial caps (← field fs "bezoutScale")
    bezoutGuard := ← openSign caps (← field fs "bezoutGuard")
    tail := ← array (bivariate caps) (← field fs "tail")
    steps := ← array (parametricStep caps) (← field fs "steps")
    last := ← polynomial caps (← field fs "last")
    lastGuard := ← openSign caps (← field fs "lastGuard") }

@[simp] theorem erase_parametricRoot (caps : Caps) (v : Value) :
    eraseD (parametricRoot caps v) = GlobalCheckerDecode.parametricRoot caps v := by
  simp [parametricRoot, GlobalCheckerDecode.parametricRoot]

def specializedRootWithWidth (caps : Caps) (originalWidth : Nat) (v : Value) :
    Decode AlgebraicRootCertificate.Certificate := do
  let fs ← record ["representative", "quotient", "powerQuotient", "rootWitness", "powerWitness",
    "bezoutLeft", "bezoutRight", "bezoutWitness", "derivativeWitness", "last", "lastInverse",
    "lastQuotient", "exponent", "tail", "quotients", "witnesses"] v
  let c : AlgebraicRootCertificate.Certificate := {
    representative := ← bivariate caps (← field fs "representative")
    quotient := ← bivariate caps (← field fs "quotient")
    powerQuotient := ← bivariate caps (← field fs "powerQuotient")
    exponent := ← exponent caps (← field fs "exponent")
    rootWitness := ← bivariate caps (← field fs "rootWitness")
    powerWitness := ← bivariate caps (← field fs "powerWitness")
    bezoutLeft := ← bivariate caps (← field fs "bezoutLeft")
    bezoutRight := ← bivariate caps (← field fs "bezoutRight")
    bezoutWitness := ← bivariate caps (← field fs "bezoutWitness")
    tail := ← array (bivariate caps) (← field fs "tail")
    quotients := ← array (bivariate caps) (← field fs "quotients")
    witnesses := ← array (bivariate caps) (← field fs "witnesses")
    last := ← polynomial caps (← field fs "last")
    lastInverse := ← polynomial caps (← field fs "lastInverse")
    lastQuotient := ← polynomial caps (← field fs "lastQuotient")
    derivativeWitness := ← bivariate caps (← field fs "derivativeWitness") }
  rehydrateWitnesses caps originalWidth c

@[simp] theorem erase_specializedRootWithWidth (caps : Caps) (originalWidth : Nat) (v : Value) :
    eraseD (specializedRootWithWidth caps originalWidth v) =
      GlobalCheckerDecode.specializedRootWithWidth caps originalWidth v := by
  simp [specializedRootWithWidth, GlobalCheckerDecode.specializedRootWithWidth]

def specializedRoot (caps : Caps) (v : Value) : Decode AlgebraicRootCertificate.Certificate :=
  specializedRootWithWidth caps 0 v

@[simp] theorem erase_specializedRoot (caps : Caps) (v : Value) :
    eraseD (specializedRoot caps v) = GlobalCheckerDecode.specializedRoot caps v := by
  simp [specializedRoot, GlobalCheckerDecode.specializedRoot]

def direction (dir : BoschlooOrdering.Direction) (v : Value) : Decode Unit := do
  let _ ← literalText (match dir with | .greater => "greater" | .less => "less") v

@[simp] theorem erase_direction (expected : BoschlooOrdering.Direction) (v : Value) :
    eraseD (direction expected v) = GlobalCheckerDecode.direction expected v := by
  simp [direction, GlobalCheckerDecode.direction]
  rfl

def openDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerOpenDecision.Certificate := do
  let kind ← tag v
  let keys := if kind == "interior_root" then
    ["kind", "direction", "ordering", "originalLeft", "originalRight", "root", "left", "right"]
    else ["kind", "direction", "ordering"]
  let fs ← record keys v
  direction dir (← field fs "direction")
  let ordering ← array (openSign caps) (← field fs "ordering")
  let branch ← match kind with
    | "full_mask" => pure .fullMask
    | "zero_level" => pure .zeroLevel
    | "interior_root" => pure (.interiorRoot {
        originalLeft := ← openSign caps (← field fs "originalLeft")
        originalRight := ← openSign caps (← field fs "originalRight")
        root := ← parametricRoot caps (← field fs "root")
        left := ← array (openSign caps) (← field fs "left")
        right := ← array (openSign caps) (← field fs "right") })
    | _ => throw .shape
  return ⟨ordering, branch⟩

@[simp] theorem erase_openDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    eraseD (openDecision caps dir v) = GlobalCheckerDecode.openDecision caps dir v := by
  simp [openDecision, GlobalCheckerDecode.openDecision]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def pointDecisionWithWidth (caps : Caps) (originalWidth : Nat)
    (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerPointDecision.Certificate := do
  let kind ← tag v
  let keys := if kind == "rational_root" then ["kind", "direction", "ordering", "root"]
    else if kind == "algebraic_root" then
      ["kind", "direction", "ordering", "original", "root", "left", "right"]
    else ["kind", "direction", "ordering"]
  let fs ← record keys v
  direction dir (← field fs "direction")
  let ordering ← array (pointSign caps) (← field fs "ordering")
  let branch ← match kind with
    | "full_mask" => pure .fullMask
    | "zero_level" => pure .zeroLevel
    | "rational_root" => pure (.rationalRoot (← rootCount caps (← field fs "root")))
    | "algebraic_root" => pure (.algebraicRoot {
        original := ← pointSign caps (← field fs "original")
        root := ← specializedRootWithWidth caps originalWidth (← field fs "root")
        left := ← array (pointSign caps) (← field fs "left")
        right := ← array (pointSign caps) (← field fs "right") })
    | _ => throw .shape
  return ⟨ordering, branch⟩

@[simp] theorem erase_pointDecisionWithWidth (caps : Caps) (originalWidth : Nat)
    (dir : BoschlooOrdering.Direction) (v : Value) :
    eraseD (pointDecisionWithWidth caps originalWidth dir v) =
      GlobalCheckerDecode.pointDecisionWithWidth caps originalWidth dir v := by
  simp [pointDecisionWithWidth, GlobalCheckerDecode.pointDecisionWithWidth]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def pointDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    Decode GlobalCheckerPointDecision.Certificate := pointDecisionWithWidth caps 0 dir v

@[simp] theorem erase_pointDecision (caps : Caps) (dir : BoschlooOrdering.Direction) (v : Value) :
    eraseD (pointDecision caps dir v) = GlobalCheckerDecode.pointDecision caps dir v := by
  simp [pointDecision, GlobalCheckerDecode.pointDecision]

def leafState (v : Value) : Decode GlobalCheckerLeaf.State := do
  match ← dispatchText v with
  | "ACCEPTED" => pure .accepted
  | "REJECTED_GREATER" => pure .rejectedGreater
  | "REJECTED_LESS" => pure .rejectedLess
  | "BOUNDARY_ENCLOSURE" => pure .boundary
  | _ => throw .shape

@[simp] theorem erase_leafState (v : Value) :
    eraseD (leafState v) = GlobalCheckerDecode.leafState v := by
  simp [leafState, GlobalCheckerDecode.leafState]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def leaf {α : Type} (decode : BoschlooOrdering.Direction → Value → Decode α)
    (v : Value) : Decode (GlobalCheckerLeaf.Leaf α) := do
  let fs ← record ["state", "greater", "less"] v
  return {
    state := ← leafState (← field fs "state")
    greater := ← optional (decode .greater) (← field fs "greater")
    less := ← optional (decode .less) (← field fs "less") }

@[simp] theorem erase_leaf {α : Type}
    (decode : BoschlooOrdering.Direction → Value → Decode α) (v : Value) :
    eraseD (leaf decode v) =
      GlobalCheckerDecode.leaf (fun d v => eraseD (decode d v)) v := by
  simp [leaf, GlobalCheckerDecode.leaf]

def anchor (caps : Caps) (v : Value) : Decode GlobalCheckerAnchor.Anchor := do
  match ← tag v with
  | "rational" =>
      let fs ← record ["kind", "value", "openCell"] v
      return .rational (← rational caps (← field fs "value")) (← index caps (← field fs "openCell"))
  | "point" =>
      let fs ← record ["kind", "index"] v
      return .point (← index caps (← field fs "index"))
  | _ => throw .shape

@[simp] theorem erase_anchor (caps : Caps) (v : Value) :
    eraseD (anchor caps v) = GlobalCheckerDecode.anchor caps v := by
  simp [anchor, GlobalCheckerDecode.anchor]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

def hullBranch (caps : Caps) (v : Value) : Decode GlobalCheckerHull.Branch := do
  match ← tag v with
  | "structural" =>
      let fs ← record ["kind", "endpoint"] v
      match ← dispatchText (← field fs "endpoint") with
      | "zero" => pure (.structural .zero)
      | "one" => pure (.structural .infinity)
      | _ => throw .shape
  | "finite" =>
      let fs ← record ["kind", "anchor", "enclosureLower", "enclosureUpper"] v
      return .finite (← anchor caps (← field fs "anchor"))
        (← rational caps (← field fs "enclosureLower")) (← rational caps (← field fs "enclosureUpper"))
  | _ => throw .shape

@[simp] theorem erase_hullBranch (caps : Caps) (v : Value) :
    eraseD (hullBranch caps v) = GlobalCheckerDecode.hullBranch caps v := by
  simp [hullBranch, GlobalCheckerDecode.hullBranch]
  congr 1
  funext kind
  split <;> simp_all
  congr 1
  funext fs
  congr 1
  funext endpoint
  split <;> simp_all

def terminal (caps : Caps) (v : Value) : Decode GlobalCheckerCore.Terminal := do
  match ← tag v with
  | "FULL_CERTIFIED" => let _ ← record ["kind"] v; return .full
  | "EMPTY_CERTIFIED" => let _ ← record ["kind"] v; return .empty
  | "HULL_CERTIFIED" =>
      let fs ← record ["kind", "outerLower", "outerUpper", "lower", "upper"] v
      return .hull (← rational caps (← field fs "outerLower"))
        (← rational caps (← field fs "outerUpper")) (← hullBranch caps (← field fs "lower"))
        (← hullBranch caps (← field fs "upper"))
  | _ => throw .shape

@[simp] theorem erase_terminal (caps : Caps) (v : Value) :
    eraseD (terminal caps v) = GlobalCheckerDecode.terminal caps v := by
  simp [terminal, GlobalCheckerDecode.terminal]
  congr 1
  funext kind
  all_goals
    repeat' first | rfl | fail_if_no_progress simp_all | split

end ExactCIs.Unconditional.MeteredDecode
