/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.RootComparison
import ExactCIs.Unconditional.OpenStrata

/-! # Checked positive algebraic event order and point/cut binding

Every asserted order is replayed by the exact comparison checker. Soundness
does not trust the producer's real-root ordering. This does not prove that an
arbitrary event array includes every required projection root or that its byte
representation is canonical.
-/
namespace ExactCIs.Unconditional.RootEventOrder

open SelectedRoot OpenStrata

noncomputable def value (a : Root) : ℝ :=
  if checked : a.check = true then Classical.choose (unique checked) else 0

theorem value_means {a : Root} (checked : a.check = true) : a.Means (value a) := by
  simp only [value, dif_pos checked]
  exact (Classical.choose_spec (unique checked)).1

theorem value_eq {a : Root} (checked : a.check = true) {x : ℝ} (meaning : a.Means x) :
    value a = x := same_value checked (value_means checked) meaning

def check {n : ℕ} (roots : Fin n → Root)
    (certificates : Fin n → Fin n → RootComparison.Certificate) : Bool :=
  (List.finRange n).all fun i => (roots i).check && decide (0 < (roots i).lower) &&
    (List.finRange n).all fun j =>
      if i < j then decide (RootComparison.check (roots i) (roots j) (certificates i j) = some .lt)
      else true

theorem check_sound {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true) :
    (∀ i, (roots i).check = true ∧ 0 < value (roots i)) ∧
      StrictMono (fun i => value (roots i)) := by
  have parts (i : Fin n) : (roots i).check = true ∧ 0 < (roots i).lower ∧
      ∀ j : Fin n, (if i < j then
        decide (RootComparison.check (roots i) (roots j) (certificates i j) = some .lt)
        else true) = true := by
    have selected := List.all_eq_true.mp checked i (List.mem_finRange i)
    simpa only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
      List.mem_finRange, forall_const, and_assoc] using selected
  have bases (i : Fin n) : (roots i).check = true := (parts i).1
  refine ⟨fun i => ⟨bases i, ?_⟩, ?_⟩
  · exact (by exact_mod_cast (parts i).2.1 : (0 : ℝ) < (roots i).lower).trans
      (value_means (bases i)).1.1
  · intro i j order
    have comparison : RootComparison.check (roots i) (roots j) (certificates i j) = some .lt := by
      simpa only [if_pos order, decide_eq_true_eq] using (parts i).2.2 j
    exact (RootComparison.check_sound comparison
      (value_means (bases i)) (value_means (bases j))).2.2

theorem check_complete {n : ℕ} (roots : Fin n → Root)
    (bases : ∀ i, (roots i).check = true ∧ 0 < (roots i).lower)
    (ordered : StrictMono (fun i => value (roots i))) :
    ∃ certificates, check roots certificates = true := by
  classical
  have available (i j : Fin n) : ∃ c : RootComparison.Certificate,
      i < j → RootComparison.check (roots i) (roots j) c = some .lt := by
    by_cases order : i < j
    · obtain ⟨left, right, separated⟩ := RootComparison.exists_separated
        (bases i).1 (bases j).1 (value_means (bases i).1) (value_means (bases j).1)
        (ordered order)
      exact ⟨.less left right, fun _ => by
        simp only [RootComparison.check, (bases i).1, (bases j).1,
          Bool.and_self, ↓reduceIte, separated]⟩
    · exact ⟨.less ⟨0, 1, (roots i).certificate⟩ ⟨0, 1, (roots j).certificate⟩,
        fun impossible => False.elim (order impossible)⟩
  let certificates i j := Classical.choose (available i j)
  refine ⟨certificates, List.all_eq_true.mpr ?_⟩
  intro i _
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨(bases i).1, (bases i).2⟩, List.all_eq_true.mpr ?_⟩
  intro j _
  by_cases order : i < j
  · simpa only [if_pos order, decide_eq_true_eq] using
      Classical.choose_spec (available i j) order
  · simp only [if_neg order]

noncomputable def events {n : ℕ} (roots : Fin n → Root) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun i => value (roots i))

theorem mem_events {n : ℕ} (roots : Fin n → Root) (x : ℝ) :
    x ∈ events roots ↔ ∃ i, value (roots i) = x := by
  classical
  simp only [events, Finset.mem_image, Finset.mem_univ, true_and]

noncomputable def eventIndex {n : ℕ} (roots : Fin n → Root) (i : Fin n) : events roots :=
  ⟨value (roots i), (mem_events roots _).mpr ⟨i, rfl⟩⟩

theorem eventIndex_injective {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true) :
    Function.Injective (eventIndex roots) := by
  intro i j equal
  exact (check_sound checked).2.injective (congrArg Subtype.val equal)

theorem unique_point_index {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true)
    {x : ℝ} (member : x ∈ events roots) : ∃! i, value (roots i) = x := by
  obtain ⟨i, hi⟩ := (mem_events roots x).mp member
  refine ⟨i, hi, ?_⟩
  intro j hj
  exact (check_sound checked).2.injective (hj.trans hi.symm)

noncomputable def mappedCut {n : ℕ} (roots : Fin n → Root) (lower : Finset (Fin n)) :
    Finset (events roots) := by
  classical
  exact lower.image (eventIndex roots)

theorem mem_mappedCut {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true) (lower : Finset (Fin n)) (i : Fin n) :
    eventIndex roots i ∈ mappedCut roots lower ↔ i ∈ lower := by
  classical
  change eventIndex roots i ∈ lower.image (eventIndex roots) ↔ i ∈ lower
  rw [Finset.mem_image]
  constructor
  · rintro ⟨j, member, equal⟩
    exact eventIndex_injective checked equal ▸ member
  · intro member
    exact ⟨i, member, rfl⟩

theorem indexed_gap {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true)
    (lower : Finset (Fin n)) (x : ℝ) :
    x ∈ gap (events roots) (mappedCut roots lower) ↔
      0 < x ∧ ∀ i, (i ∈ lower → value (roots i) < x) ∧ (i ∉ lower → x < value (roots i)) := by
  constructor
  · intro owned
    refine ⟨owned.1, ?_⟩
    intro i
    exact ⟨fun hi => (owned.2 (eventIndex roots i)).1 ((mem_mappedCut checked lower i).mpr hi),
      fun hi => (owned.2 (eventIndex roots i)).2
        (fun included => hi ((mem_mappedCut checked lower i).mp included))⟩
  · rintro ⟨positive, bounds⟩
    refine ⟨positive, ?_⟩
    intro e
    obtain ⟨i, hi⟩ := (mem_events roots e).mp e.property
    have same : eventIndex roots i = e := Subtype.ext hi
    subst e
    exact ⟨fun included => (bounds i).1 ((mem_mappedCut checked lower i).mp included),
      fun excluded => (bounds i).2 (fun hi => excluded ((mem_mappedCut checked lower i).mpr hi))⟩

theorem checked_unique_owner {n : ℕ} {roots : Fin n → Root}
    {certificates : Fin n → Fin n → RootComparison.Certificate}
    (checked : check roots certificates = true)
    {x : ℝ} (positive : 0 < x) :
    (∀ e ∈ events roots, 0 < e) ∧ ∃! owner : Owner (events roots), owns (events roots) owner x := by
  refine ⟨?_, unique_owner (events roots) positive⟩
  intro e member
  obtain ⟨i, equal⟩ := (mem_events roots e).mp member
  exact equal ▸ (check_sound checked).1 i |>.2

end ExactCIs.Unconditional.RootEventOrder
