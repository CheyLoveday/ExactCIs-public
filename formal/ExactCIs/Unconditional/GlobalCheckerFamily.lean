/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerPartition
import ExactCIs.Unconditional.CanonicalEncoding

/-! # Recomputed projection families and complete checked root coverage

All outcome comparisons in both directions are reconstructed. Open-certificate
families conservatively include every coefficient polynomial, original endpoint
polynomial, signed recurrence scale and specialized variation polynomial used
by the checker. Normalization removes trailing zeroes only. The producer cannot
replace this required family with its own list of convenient polynomials.
-/
namespace ExactCIs.Unconditional.GlobalCheckerFamily

open RootCertificate AlgebraicSpecialization ProductBinomial BoschlooOrdering
open GlobalCheckerPoint GlobalCheckerLeaf GlobalCheckerPartition

def comparisons {n1 n0 : ℕ} (observed : Outcome n1 n0) : List Coefficients :=
  (List.finRange (n1 + 1)).flatMap fun x =>
    (List.finRange (n0 + 1)).flatMap fun y =>
      [CompactPolynomial.comparison .greater (x, y) observed,
        CompactPolynomial.comparison .less (x, y) observed]

theorem comparison_mem {n1 n0 : ℕ} (observed candidate : Outcome n1 n0) (dir : Direction) :
    CompactPolynomial.comparison dir candidate observed ∈ comparisons observed := by
  cases candidate with
  | mk x y =>
    apply List.mem_flatMap.mpr
    refine ⟨x, List.mem_finRange x, List.mem_flatMap.mpr ?_⟩
    refine ⟨y, List.mem_finRange y, ?_⟩
    cases dir <;> simp

def rootGuards (c : GlobalCheckerParametricRoot.Certificate) : List Coefficients :=
  [c.rootScale, c.powerScale, c.bezoutScale, c.last] ++
    c.representative ++ c.quotient ++ c.powerQuotient ++ c.bezoutLeft ++ c.bezoutRight ++
    c.tail.flatten ++ c.steps.flatMap (fun s => s.scale :: s.quotient) ++
    (c.representative :: c.tail).flatMap (fun p =>
      [AlgebraicSignReplay.atRational p 0, AlgebraicSignReplay.atRational p 1])

def decisionGuards {n1 n0 : ℕ} (r : ℚ)
    (c : GlobalCheckerOpenDecision.Certificate) : List Coefficients :=
  match c.branch with
  | .fullMask | .zeroLevel => []
  | .interiorRoot branch =>
    let h := CompactPolynomial.objective
      (GlobalCheckerOpenDecision.certifiedMask n1 n0 c.ordering) r
    [AlgebraicSignReplay.atRational h 0, AlgebraicSignReplay.atRational h 1] ++
      h ++ rootGuards branch.root

def leafGuards (n1 n0 : ℕ) (r : ℚ) (leaf : OpenLeaf) : List Coefficients :=
  (leaf.greater.toList ++ leaf.less.toList).flatMap
    (decisionGuards (n1 := n1) (n0 := n0) r)

def chainGuards (n1 n0 : ℕ) (r : ℚ) : Chain → List Coefficients
  | .last gap => leafGuards n1 n0 r gap
  | .next _ gap _ rest => leafGuards n1 n0 r gap ++ chainGuards n1 n0 r rest

def normalize (ps : List Coefficients) : List Coefficients :=
  ((ps.map CanonicalEncoding.trim).filter fun p => p != []).dedup

def required {n1 n0 : ℕ} (observed : Outcome n1 n0) (r : ℚ) (chain : Chain) :
    List Coefficients := normalize (comparisons observed ++ chainGuards n1 n0 r chain)

theorem trim_eval (p : Coefficients) (x : ℝ) : eval (CanonicalEncoding.trim p) x = eval p x := by
  rw [← PolynomialList.polynomial_eval, ← PolynomialList.polynomial_eval,
    CanonicalEncoding.trim_polynomial]

theorem normalized_mem {ps : List Coefficients} {p : Coefficients}
    (member : p ∈ ps) (nonzero : CanonicalEncoding.trim p ≠ []) :
    CanonicalEncoding.trim p ∈ normalize ps := by
  simp only [normalize, List.mem_dedup, List.mem_filter, bne_iff_ne]
  exact ⟨List.mem_map.mpr ⟨p, member, rfl⟩, nonzero⟩

def check (points : List Point) (family : List Coefficients)
    (covers : List GlobalCheckerProjection.Cover) : Bool :=
  covers.all (GlobalCheckerProjection.check points) &&
    family.all (fun p => covers.any (fun c => decide (c.polynomial = p)))

theorem check_sound {points : List Point} {family : List Coefficients}
    {covers : List GlobalCheckerProjection.Cover}
    (distinct : (points.map Point.value).Nodup) (checked : check points family covers = true) :
    ∀ p ∈ family, ∀ x ∈ Set.Ioo (0 : ℝ) 1, eval p x = 0 →
      ∃ a ∈ points, a.value = x := by
  have parts := Bool.and_eq_true_iff.mp checked
  intro p hp x hx zero
  have found := List.all_eq_true.mp parts.2 p hp
  obtain ⟨c, hc, same⟩ := List.any_eq_true.mp found
  have same' : c.polynomial = p := of_decide_eq_true same
  have cover := GlobalCheckerProjection.check_sound distinct
    (List.all_eq_true.mp parts.1 c hc)
  have represented : x ∈ GlobalCheckerProjection.represented points c := by
    rw [cover, same']
    exact ⟨hx.1, hx.2, zero⟩
  obtain ⟨m, hm, hmx⟩ := List.mem_map.mp represented
  have member_checked := List.all_eq_true.mp
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp
      (List.all_eq_true.mp parts.1 c hc)).1).2 m hm
  obtain ⟨a, lookup, _, _⟩ := GlobalCheckerProjection.memberCheck_sound member_checked
  refine ⟨a, List.mem_of_getElem? lookup, ?_⟩
  simpa only [GlobalCheckerProjection.selectedValue, lookup, Option.getD_some] using hmx

theorem comparison_roots_covered {n1 n0 : ℕ} {observed : Outcome n1 n0} {r : ℚ}
    {chain : Chain} {order : List GlobalCheckerOrder.Witness}
    {covers : List GlobalCheckerProjection.Cover}
    (ordered : GlobalCheckerOrder.check chain.points order = true)
    (checked : check chain.points (required observed r chain) covers = true)
    (candidate : Outcome n1 n0) (dir : Direction)
    (nonzero : CanonicalEncoding.trim (CompactPolynomial.comparison dir candidate observed) ≠ [])
    {x : ℝ} (inside : x ∈ Set.Ioo (0 : ℝ) 1)
    (zero : eval (CompactPolynomial.comparison dir candidate observed) x = 0) :
    ∃ a ∈ chain.points, a.value = x := by
  apply check_sound (GlobalCheckerOrder.values_distinct ordered) checked
    (CanonicalEncoding.trim (CompactPolynomial.comparison dir candidate observed))
    (normalized_mem (List.mem_append_left _ (comparison_mem observed candidate dir)) nonzero)
    x inside
  simpa only [trim_eval] using zero

end ExactCIs.Unconditional.GlobalCheckerFamily
