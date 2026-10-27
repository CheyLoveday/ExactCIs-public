/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.BoschlooOrdering
import ExactCIs.Unconditional.AlgebraicEmbeddingComplete
import ExactCIs.Unconditional.StratumSignReplay
import Mathlib.Topology.Order.IntermediateValue

/-! # Canonical ownership of the positive line for a finite event family

Gap labels are strict lower cuts of the deduplicated finite event set. Empty
labels may denote empty gaps; every positive real nevertheless has exactly one
owner. Point ownership never takes a decision from an adjacent open gap.
-/
namespace ExactCIs.Unconditional.OpenStrata

def gap (events : Finset ℝ) (lower : Finset events) : Set ℝ :=
  {x | 0 < x ∧ ∀ e : events,
    (e ∈ lower → (e : ℝ) < x) ∧ (e ∉ lower → x < (e : ℝ))}

noncomputable def cut (events : Finset ℝ) (x : ℝ) : Finset events := by
  classical
  exact Finset.univ.filter (fun e => (e : ℝ) < x)

theorem mem_cut (events : Finset ℝ) (x : ℝ) (e : events) :
    e ∈ cut events x ↔ (e : ℝ) < x := by
  classical
  simp [cut]

theorem gap_event_free {events : Finset ℝ} {lower : Finset events} {x : ℝ}
    (inside : x ∈ gap events lower) : x ∉ events := by
  classical
  intro member
  let e : events := ⟨x, member⟩
  by_cases below : e ∈ lower
  · exact (lt_irrefl x) ((inside.2 e).1 below)
  · exact (lt_irrefl x) ((inside.2 e).2 below)

theorem mem_gap_cut {events : Finset ℝ} {x : ℝ} (positive : 0 < x)
    (regular : x ∉ events) : x ∈ gap events (cut events x) := by
  classical
  refine ⟨positive, ?_⟩
  intro e
  refine ⟨(mem_cut events x e).mp, ?_⟩
  intro not_below
  have lower : x ≤ (e : ℝ) :=
    le_of_not_gt (fun h => not_below ((mem_cut events x e).mpr h))
  refine lt_of_le_of_ne lower ?_
  intro equality
  apply regular
  rw [equality]
  exact e.property

theorem gap_label_unique {events : Finset ℝ} {lower : Finset events} {x : ℝ}
    (inside : x ∈ gap events lower) : lower = cut events x := by
  classical
  ext e
  constructor
  · intro below
    exact (mem_cut events x e).mpr ((inside.2 e).1 below)
  · intro below
    by_contra absent
    exact (not_lt_of_gt ((mem_cut events x e).mp below)) ((inside.2 e).2 absent)

abbrev Owner (events : Finset ℝ) := Sum events (Finset events)

def owns (events : Finset ℝ) : Owner events → ℝ → Prop
  | .inl e, x => x = (e : ℝ)
  | .inr lower, x => x ∈ gap events lower

theorem finite_owners (events : Finset ℝ) :
    (Set.univ : Set (Owner events)).Finite := Set.toFinite _

theorem unique_owner (events : Finset ℝ) {x : ℝ} (positive : 0 < x) :
    ∃! owner : Owner events, owns events owner x := by
  classical
  by_cases event : x ∈ events
  · refine ⟨.inl ⟨x, event⟩, rfl, ?_⟩
    intro owner owned
    cases owner with
    | inl e =>
      apply congrArg Sum.inl
      exact Subtype.ext owned.symm
    | inr lower => exact False.elim (gap_event_free owned event)
  · refine ⟨.inr (cut events x), mem_gap_cut positive event, ?_⟩
    intro owner owned
    cases owner with
    | inl e =>
      apply False.elim
      apply event
      change x = (e : ℝ) at owned
      rw [owned]
      exact e.property
    | inr lower => exact congrArg Sum.inr (gap_label_unique owned)

theorem gap_ordConnected (events : Finset ℝ) (lower : Finset events) :
    (gap events lower).OrdConnected := by
  refine ⟨?_⟩
  intro x hx y hy z hz
  refine ⟨hx.1.trans_le hz.1, ?_⟩
  intro e
  exact ⟨fun he => ((hx.2 e).1 he).trans_le hz.1,
    fun he => hz.2.trans_lt ((hy.2 e).2 he)⟩

theorem gap_preconnected (events : Finset ℝ) (lower : Finset events) :
    IsPreconnected (gap events lower) := (gap_ordConnected events lower).isPreconnected

theorem gap_open (events : Finset ℝ) (lower : Finset events) :
    IsOpen (gap events lower) := by
  classical
  have description : gap events lower = Set.Ioi 0 ∩
      ⋂ e : events, if e ∈ lower then Set.Ioi (e : ℝ) else Set.Iio (e : ℝ) := by
    ext x
    simp only [gap, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_Ioi, Set.mem_iInter]
    refine and_congr Iff.rfl ?_
    apply forall_congr'
    intro e
    by_cases member : e ∈ lower <;> simp [member]
  rw [description]
  apply isOpen_Ioi.inter
  apply isOpen_iInter_of_finite
  intro e
  split_ifs <;> first | exact isOpen_Ioi | exact isOpen_Iio

/-- Every positive finite boundary belongs to the event-point lane. -/
theorem positive_frontier_is_event {events : Finset ℝ} {lower : Finset events} {x : ℝ}
    (positive : 0 < x) (boundary : x ∈ frontier (gap events lower)) : x ∈ events := by
  classical
  by_contra regular
  have inside := mem_gap_cut positive regular
  obtain ⟨y, hy, old⟩ := mem_closure_iff.mp boundary.1
    (gap events (cut events x)) (gap_open _ _) inside
  have same : lower = cut events x :=
    (gap_label_unique old).trans (gap_label_unique hy).symm
  have member : x ∈ gap events lower := by rw [same]; exact inside
  apply boundary.2
  simpa only [(gap_open events lower).interior_eq] using member

theorem frontier_subset {events : Finset ℝ} (lower : Finset events) :
    frontier (gap events lower) ⊆ ({0} : Set ℝ) ∪ (events : Set ℝ) := by
  intro x boundary
  have nonnegative : 0 ≤ x :=
    closure_minimal (fun _ hx => hx.1.le) isClosed_Ici boundary.1
  rcases eq_or_lt_of_le nonnegative with zero | positive
  · exact Or.inl zero.symm
  · exact Or.inr (positive_frontier_is_event positive boundary)

theorem rational_closed_neighborhood {cell : Set ℝ} (open_cell : IsOpen cell)
    {x : ℝ} (inside : x ∈ cell) :
    ∃ l u : ℚ, x ∈ Set.Ioo (l : ℝ) u ∧ Set.Icc (l : ℝ) u ⊆ cell := by
  obtain ⟨a, b, bounds, neighborhood⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (open_cell.mem_nhds inside)
  obtain ⟨l, al, lx⟩ := exists_rat_btwn bounds.1
  obtain ⟨u, xu, ub⟩ := exists_rat_btwn bounds.2
  exact ⟨l, u, ⟨lx, xu⟩, fun _ hy => neighborhood
    ⟨al.trans_le hy.1, hy.2.trans_lt ub⟩⟩

/-- Each nonempty gap is maximal among order-connected positive sets avoiding
the event points. No artificial rational clipping is hidden in the definition. -/
theorem gap_maximal {events : Finset ℝ} {cell : Set ℝ} (connected : cell.OrdConnected)
    (positive : ∀ x ∈ cell, 0 < x) (regular : ∀ x ∈ cell, x ∉ events)
    {x : ℝ} (inside : x ∈ cell) : cell ⊆ gap events (cut events x) := by
  classical
  intro y hy
  refine ⟨positive y hy, ?_⟩
  intro e
  constructor
  · intro below
    have ex := (mem_cut events x e).mp below
    by_contra not_below
    have ec : (e : ℝ) ∈ cell := connected.out hy inside ⟨le_of_not_gt not_below, ex.le⟩
    exact regular e ec e.property
  · intro absent
    have xe : x < (e : ℝ) := ((mem_gap_cut (positive x inside) (regular x inside)).2 e).2 absent
    by_contra not_above
    have ec : (e : ℝ) ∈ cell := connected.out inside hy ⟨xe.le, le_of_not_gt not_above⟩
    exact regular e ec e.property

def eventSet {ι : Type*} (guards : ι → Polynomial ℚ) : Set ℝ :=
  {x | 0 < x ∧ ∃ i, guards i ≠ 0 ∧ BoschlooOrdering.realEval (guards i) x = 0}

theorem finite_eventSet {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ) :
    (eventSet guards).Finite := by
  classical
  have each : ∀ i, {x : ℝ | guards i ≠ 0 ∧
      0 < x ∧ BoschlooOrdering.realEval (guards i) x = 0}.Finite := by
    intro i
    by_cases zero : guards i = 0
    · simp [zero]
    · exact (Polynomial.finite_setOfPred_isRoot
        (Polynomial.map_ne_zero (f := Rat.castHom ℝ) zero)).subset (fun _ hx => hx.2.2)
  apply (Set.finite_iUnion each).subset
  rintro x ⟨positive, i, nonzero, root⟩
  exact Set.mem_iUnion.mpr ⟨i, nonzero, positive, root⟩

noncomputable def events {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ) : Finset ℝ :=
  (finite_eventSet guards).toFinset

theorem mem_events {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ) (x : ℝ) :
    x ∈ events guards ↔ 0 < x ∧
      ∃ i, guards i ≠ 0 ∧ BoschlooOrdering.realEval (guards i) x = 0 := by
  simp [events, eventSet]

theorem zero_not_owned {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    (owner : Owner (events guards)) : ¬ owns (events guards) owner 0 := by
  cases owner with
  | inl e =>
    intro equality
    have positive := ((mem_events guards e).mp e.property).1
    change (0 : ℝ) = e at equality
    rw [← equality] at positive
    exact (lt_irrefl 0) positive
  | inr lower => exact fun inside => (lt_irrefl 0) inside.1

theorem guard_nonzero_on_gap {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    (lower : Finset (events guards)) (i : ι) (nonzero : guards i ≠ 0)
    {x : ℝ} (inside : x ∈ gap (events guards) lower) :
    BoschlooOrdering.realEval (guards i) x ≠ 0 := by
  intro zero
  exact gap_event_free inside ((mem_events guards x).mpr ⟨inside.1, i, nonzero, zero⟩)

/-- Every owned guard event has a finite certificate selecting that very real
embedding, including conjugates, repeated roots and roots shared by guards. -/
theorem event_checked_embedding {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    {x : ℝ} (event : x ∈ events guards) :
    ∃ i, ∃ d : RootCertificate.Coefficients, ∃ l u : ℚ,
      ∃ c : RootCountCertificate.Certificate,
        PolynomialList.polynomial d = guards i ∧
        0 < l ∧
        AlgebraicEmbedding.check d l u c = true ∧
        x ∈ Set.Ioo (l : ℝ) u ∧ RootCertificate.eval d x = 0 := by
  obtain ⟨positive, i, nonzero, root⟩ := (mem_events guards x).mp event
  obtain ⟨d, encoding⟩ := PolynomialList.exists_coefficients (guards i)
  have root_d : RootCertificate.eval d x = 0 := by
    rw [← RootCountCertificate.realPolynomial_eval_apply]
    change ((PolynomialList.polynomial d).map (Rat.castHom ℝ)).eval x = 0
    rw [encoding]
    exact root
  obtain ⟨l, u, c, lower_positive, checked, inside⟩ :=
    AlgebraicEmbedding.exists_positive_checked_isolator d
      (by rw [encoding]; exact nonzero) root_d positive
  exact ⟨i, d, l, u, c, encoding, lower_positive, checked, inside, root_d⟩

theorem guard_sign_constant {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    (lower : Finset (events guards)) (i : ι) (nonzero : guards i ≠ 0)
    {x y : ℝ} (hx : x ∈ gap (events guards) lower) (hy : y ∈ gap (events guards) lower) :
    BoschlooOrdering.realEval (guards i) x < 0 ↔
      BoschlooOrdering.realEval (guards i) y < 0 := by
  have signs := BoschlooOrdering.polynomial_sign_constant (guards i)
    (gap_preconnected _ _) (fun _ hz => guard_nonzero_on_gap guards lower i nonzero hz) hx hy
  have nx := guard_nonzero_on_gap guards lower i nonzero hx
  have ny := guard_nonzero_on_gap guards lower i nonzero hy
  exact (lt_iff_le_and_ne.trans (and_iff_left nx)).trans
    (signs.trans (lt_iff_le_and_ne.trans (and_iff_left ny)).symm)

/-- Actual inclusive Fisher masks are constant on every entire open gap of
their nonzero comparison guards. Identically zero comparisons stay tied. -/
theorem fisher_mask_constant {n1 n0 : ℕ} (direction : BoschlooOrdering.Direction)
    (observed : ProductBinomial.Outcome n1 n0)
    (lower : Finset (events (fun candidate =>
      BoschlooOrdering.comparisonPolynomial direction candidate observed)))
    {x y : ℝ}
    (hx : x ∈ gap (events (fun candidate =>
      BoschlooOrdering.comparisonPolynomial direction candidate observed)) lower)
    (hy : y ∈ gap (events (fun candidate =>
      BoschlooOrdering.comparisonPolynomial direction candidate observed)) lower) :
    BoschlooOrdering.mask direction x observed = BoschlooOrdering.mask direction y observed := by
  apply BoschlooOrdering.chamber_mask_eq direction observed (gap_preconnected _ _) ?_
    hx.1 hy.1 hx hy
  intro candidate
  by_cases zero : BoschlooOrdering.comparisonPolynomial direction candidate observed = 0
  · exact Or.inl zero
  · exact Or.inr (fun _ hz => guard_nonzero_on_gap _ lower candidate zero hz)

/-- At an event point the actual inclusive comparator owns its equality tie.
No decision from either adjacent open gap is used. -/
theorem fisher_event_tie_included {n1 n0 : ℕ} (direction : BoschlooOrdering.Direction)
    (candidate observed : ProductBinomial.Outcome n1 n0) {x : ℝ} (positive : 0 < x)
    (tie : BoschlooOrdering.realEval
      (BoschlooOrdering.comparisonPolynomial direction candidate observed) x = 0) :
    candidate ∈ BoschlooOrdering.mask direction x observed := by
  classical
  rw [BoschlooOrdering.mask_iff_polynomial positive, tie]

theorem negative_certificate (d : RootCertificate.Coefficients) (l u : ℚ)
    (order : l ≤ u)
    (negative : ∀ x ∈ Set.Icc (l : ℝ) u, RootCertificate.eval d x < 0) :
    ∃ c, RootSignCertificate.check d l u c = some false := by
  obtain ⟨c, answer, checked⟩ := RootSignCertificate.existsComplete d l u order
  cases answer with
  | false => exact ⟨c, checked⟩
  | true =>
    obtain ⟨x, inside, nonnegative⟩ := (RootSignCertificate.checkerSound checked).2.mp rfl
    exact False.elim (not_lt_of_ge nonnegative (negative x inside))

/-- A strict constant sign or a polynomial identity has an accepted whole-cell
sign witness. Strict signs, rather than one sampled value, are the premises. -/
theorem sign_witness_complete (d : RootCertificate.Coefficients) (l u : ℚ)
    (order : l ≤ u)
    (signs : PolynomialList.polynomial d = 0 ∨
      (∀ x ∈ Set.Icc (l : ℝ) u, RootCertificate.eval d x < 0) ∨
      (∀ x ∈ Set.Icc (l : ℝ) u, 0 < RootCertificate.eval d x)) :
    ∃ w, StratumSignReplay.signCheck d l u w = true := by
  classical
  rcases signs with zero | negative | positive
  · have identity : RootCertificate.identityCheck d [] = true := by
      apply (PolynomialList.identityCheck_iff _ _).mpr
      simpa [PolynomialList.polynomial] using zero
    exact ⟨⟨0, ⟨[], [], [], 0, [], [], [], [], 0⟩⟩, by
      simpa [StratumSignReplay.signCheck] using identity⟩
  · obtain ⟨c, checked⟩ := negative_certificate d l u order negative
    exact ⟨⟨-1, c⟩, by simp [StratumSignReplay.signCheck, checked]⟩
  · have negative : ∀ x ∈ Set.Icc (l : ℝ) u,
        RootCertificate.eval (RootCertificate.scale (-1) d) x < 0 := by
      intro x hx
      simpa only [RootCertificate.eval_scale, Rat.cast_neg, Rat.cast_one, neg_one_mul,
        neg_lt_zero] using positive x hx
    obtain ⟨c, checked⟩ := negative_certificate _ l u order negative
    exact ⟨⟨1, c⟩, by simp [StratumSignReplay.signCheck, checked]⟩

/-- Any prescribed rational closed subcell of a gap has a finite accepted
sign witness for every supplied guard, including degenerate closed cells. -/
theorem certificates_on_closed_cell {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    (lower : Finset (events guards)) {l u : ℚ} (order : l ≤ u)
    (subset : Set.Icc (l : ℝ) u ⊆ gap (events guards) lower) :
    ∀ i, ∃ d : RootCertificate.Coefficients, ∃ w : StratumSignReplay.SignWitness,
      PolynomialList.polynomial d = guards i ∧
      StratumSignReplay.signCheck d l u w = true := by
  classical
  have inside : (l : ℝ) ∈ gap (events guards) lower :=
    subset ⟨le_rfl, by exact_mod_cast order⟩
  intro i
  obtain ⟨d, encoding⟩ := PolynomialList.exists_coefficients (guards i)
  have eval_identity : ∀ y : ℝ,
      RootCertificate.eval d y = BoschlooOrdering.realEval (guards i) y := by
    intro y
    rw [← RootCountCertificate.realPolynomial_eval_apply]
    change ((PolynomialList.polynomial d).map (Rat.castHom ℝ)).eval y = _
    rw [encoding]
    rfl
  have signs : PolynomialList.polynomial d = 0 ∨
      (∀ y ∈ Set.Icc (l : ℝ) u, RootCertificate.eval d y < 0) ∨
      (∀ y ∈ Set.Icc (l : ℝ) u, 0 < RootCertificate.eval d y) := by
    by_cases zero : guards i = 0
    · exact Or.inl (encoding.trans zero)
    · rcases lt_trichotomy (BoschlooOrdering.realEval (guards i) (l : ℝ)) 0 with
        negative | zero_at_x | positive
      · refine Or.inr (Or.inl ?_)
        intro y hy
        rw [eval_identity]
        exact (guard_sign_constant guards lower i zero inside (subset hy)).mp negative
      · exact False.elim (guard_nonzero_on_gap guards lower i zero inside zero_at_x)
      · refine Or.inr (Or.inr ?_)
        intro y hy
        rw [eval_identity]
        apply lt_of_not_ge
        intro nonpositive
        have constancy := BoschlooOrdering.polynomial_sign_constant (guards i)
          (gap_preconnected _ _)
          (fun _ hz => guard_nonzero_on_gap guards lower i zero hz) inside (subset hy)
        exact not_le_of_gt positive (constancy.mpr nonpositive)
  obtain ⟨w, checked⟩ := sign_witness_complete d l u order signs
  exact ⟨d, w, encoding, checked⟩

/-- Every point of every whole open stratum lies strictly inside a rational
closed cell carrying accepted sign certificates for all the supplied guards.
This covers neighborhoods arbitrarily close to algebraic boundaries; it does
not assert a universal symbolic packet generator or a finite resource bound. -/
theorem local_certificates_cover_gap {ι : Type*} [Finite ι] (guards : ι → Polynomial ℚ)
    (lower : Finset (events guards)) {x : ℝ}
    (inside : x ∈ gap (events guards) lower) :
    ∃ l u : ℚ, x ∈ Set.Ioo (l : ℝ) u ∧
      Set.Icc (l : ℝ) u ⊆ gap (events guards) lower ∧
      ∀ i, ∃ d : RootCertificate.Coefficients, ∃ w : StratumSignReplay.SignWitness,
        PolynomialList.polynomial d = guards i ∧
        StratumSignReplay.signCheck d l u w = true := by
  classical
  obtain ⟨l, u, bounds, subset⟩ := rational_closed_neighborhood (gap_open _ _) inside
  have order : l ≤ u := by exact_mod_cast (bounds.1.trans bounds.2).le
  refine ⟨l, u, bounds, subset, ?_⟩
  exact certificates_on_closed_cell guards lower order subset

end ExactCIs.Unconditional.OpenStrata
