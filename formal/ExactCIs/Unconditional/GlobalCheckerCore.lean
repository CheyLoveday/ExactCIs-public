/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerHull
import ExactCIs.Unconditional.GlobalCheckerFamily
import ExactCIs.Unconditional.U0Table

/-! # Data-only global acceptance core for the frozen Boschloo scope

The core recomputes the observation, finite leaf layout, comparison/guard family,
complete root covers, all leaf decisions and the terminal return conditions.
Its soundness theorem has no producer, cover, mask, enclosure or T1 hypothesis.
Canonical bounded byte decoding and operation accounting are separate boundaries;
this typed core must not be advertised as an implemented byte checker.
-/
namespace ExactCIs.Unconditional.GlobalCheckerCore

open ProductBinomial GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition

structure Input where
  schema : String
  method : String
  estimand : String
  design : String
  table : Table
  alpha : ℚ
  alphaSide : ℚ
  tolerance : ℚ

def ValidInput (input : Input) : Prop :=
  input.schema = "exactcis.boschloo.global-checker.input.v1" ∧ input.method = "boschloo" ∧
    input.estimand = "odds_ratio" ∧ input.design = "independent_groups" ∧
    PositiveGroupTotals input.table ∧ 0 ≤ input.alpha ∧ input.alpha ≤ 1 ∧
    input.alphaSide = input.alpha / 2 ∧ 0 ≤ input.tolerance

def inputCheck (input : Input) : Bool :=
  decide (input.schema = "exactcis.boschloo.global-checker.input.v1" ∧ input.method = "boschloo" ∧
    input.estimand = "odds_ratio" ∧ input.design = "independent_groups" ∧
    0 < input.table.n1 ∧ 0 < input.table.n0 ∧ 0 ≤ input.alpha ∧ input.alpha ≤ 1 ∧
    input.alphaSide = input.alpha / 2 ∧ 0 ≤ input.tolerance)

theorem inputCheck_sound {input : Input} (checked : inputCheck input = true) :
    ValidInput input := by
  simpa only [inputCheck, decide_eq_true_eq, ValidInput, PositiveGroupTotals, and_assoc]
    using checked

inductive Terminal where
  | hull (lower upper : ℚ) (lowerBranch upperBranch : GlobalCheckerHull.Branch)
  | full
  | empty

structure Payload where
  schema : String
  coordinate : String
  points : List Point
  order : List GlobalCheckerOrder.Witness
  covers : List GlobalCheckerProjection.Cover
  openLeaves : List OpenLeaf
  pointLeaves : List PointLeaf
  terminal : Terminal

inductive Result where
  | hull (lower upper : ℚ)
  | full
  | empty
  deriving DecidableEq, Repr

inductive Bound where
  | zero | infinity | finite (value : ℚ)
  deriving DecidableEq, Repr

def bound (q : ℚ) : Bound :=
  if q = 0 then .zero else if q = 1 then .infinity else .finite (q / (1 - q))

theorem bound_zero : bound 0 = .zero := by decide
theorem bound_one : bound 1 = .infinity := by decide

noncomputable def ReturnContract (input : Input) : Result → Prop
  | .hull lo hi =>
      (0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 1) ∧
        GlobalHull.HullGuarantee (CellEnclosure.actual (TableAt.of input.table) input.alphaSide)
          (GlobalCheckerEnclosure.interval lo hi) input.tolerance
  | .full => CellEnclosure.actual (TableAt.of input.table) input.alphaSide = Set.univ
  | .empty => CellEnclosure.actual (TableAt.of input.table) input.alphaSide = ∅

def terminalCheck (input : Input) (chain : Chain) : Terminal → Option Result
  | .full => if fullCheck (TableAt.of input.table) input.alphaSide chain then some .full else none
  | .empty =>
      if emptyCheck (TableAt.of input.table) input.alphaSide chain then some .empty else none
  | .hull lo hi lb ub =>
      if GlobalCheckerHull.check (TableAt.of input.table) input.alphaSide input.tolerance
          lo hi chain lb ub then some (.hull lo hi) else none

theorem terminalCheck_sound {input : Input} {chain : Chain}
    {order : List GlobalCheckerOrder.Witness} {terminal : Terminal} {result : Result}
    (leaves : GlobalCheckerPartition.check
      (TableAt.of input.table) input.alphaSide chain order = true)
    (checked : terminalCheck input chain terminal = some result) : ReturnContract input result := by
  cases terminal with
  | full =>
    simp only [terminalCheck] at checked
    split at checked
    · rename_i h
      cases Option.some.inj checked
      exact full_sound leaves h
    · contradiction
  | empty =>
    simp only [terminalCheck] at checked
    split at checked
    · rename_i h
      cases Option.some.inj checked
      exact empty_sound leaves h
    · contradiction
  | hull lo hi lb ub =>
    simp only [terminalCheck] at checked
    split at checked
    · rename_i h
      cases Option.some.inj checked
      have outer := (Bool.and_eq_true_iff.mp
        (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).1).1).2
      exact ⟨(GlobalCheckerEnclosure.outerCheck_sound leaves outer).1,
        GlobalCheckerHull.check_sound leaves h⟩
    · contradiction

def check (input : Input) (payload : Payload) : Option Result := do
  if inputCheck input && decide (payload.schema = "exactcis.boschloo.global-checker.payload.v1" ∧
      payload.coordinate = "s=psi/(1+psi)") then
    let chain ← fromLists payload.points payload.openLeaves payload.pointLeaves
    if GlobalCheckerPartition.check (TableAt.of input.table) input.alphaSide chain payload.order &&
        GlobalCheckerFamily.check chain.points
          (GlobalCheckerFamily.required (TableAt.of input.table) input.alphaSide chain)
          payload.covers
    then terminalCheck input chain payload.terminal else none
  else none

theorem check_sound {input : Input} {payload : Payload} {result : Result}
    (checked : check input payload = some result) :
    ValidInput input ∧ ReturnContract input result := by
  unfold check at checked
  split at checked
  · rename_i h
    refine ⟨inputCheck_sound (Bool.and_eq_true_iff.mp h).1, ?_⟩
    cases layout : fromLists payload.points payload.openLeaves payload.pointLeaves with
    | none => simp [layout] at checked
    | some chain =>
      simp only [layout] at checked
      dsimp only [Bind.bind, Option.bind] at checked
      split at checked
      · rename_i checks
        exact terminalCheck_sound (Bool.and_eq_true_iff.mp checks).1 checked
      · contradiction
  · contradiction

end ExactCIs.Unconditional.GlobalCheckerCore
