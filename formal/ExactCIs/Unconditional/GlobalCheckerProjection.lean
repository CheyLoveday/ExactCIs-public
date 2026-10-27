/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.GlobalCheckerOrder
import ExactCIs.Unconditional.OpenRootCount

/-! # Complete projection-root covers from checked finite data

Known roots are insufficient: every listed index must denote an actual internal
root, indices and selected values must be distinct, and the number listed must
equal the independently checked distinct-root count on (0,1).
-/
namespace ExactCIs.Unconditional.GlobalCheckerProjection

open RootCertificate GlobalCheckerPoint

structure Member where
  point : ℕ
  zero : SignWitness

structure Cover where
  polynomial : Coefficients
  certificate : RootCountCertificate.Certificate
  members : List Member

def memberCheck (points : List Point) (p : Coefficients) (m : Member) : Bool :=
  match points[m.point]? with
  | none => false
  | some a => GlobalCheckerOrder.interiorCheck a &&
      decide (GlobalCheckerPoint.sign p a m.zero = some 0)

theorem memberCheck_sound {points : List Point} {p : Coefficients} {m : Member}
    (checked : memberCheck points p m = true) :
    ∃ a, points[m.point]? = some a ∧ a.value ∈ Set.Ioo (0 : ℝ) 1 ∧ eval p a.value = 0 := by
  cases h : points[m.point]? with
  | none => simp [memberCheck, h] at checked
  | some a =>
    have parts : GlobalCheckerOrder.interiorCheck a = true ∧
        GlobalCheckerPoint.sign p a m.zero = some 0 := by
      simpa only [memberCheck, h, Bool.and_eq_true, decide_eq_true_eq] using checked
    exact ⟨a, rfl, (GlobalCheckerOrder.interiorCheck_sound parts.1).2,
      sign_eq_zero_iff.mp (sign_sound parts.2).2⟩

def openCount (p : Coefficients) (c : RootCountCertificate.Certificate) : ℕ :=
  RootCountCertificate.count c 0 1 - if RootCertificate.value p 1 = 0 then 1 else 0

theorem openCount_sound {p : Coefficients} {c : RootCountCertificate.Certificate}
    (checked : RootCountCertificate.check p c = true) :
    openCount p c = {x : ℝ | 0 < x ∧ x < 1 ∧ eval p x = 0}.ncard := by
  have result := OpenRootCount.count_open_sound checked (by norm_num : (0 : ℝ) < 1)
  have right : eval p (1 : ℝ) = 0 ↔ RootCertificate.value p 1 = 0 := by
    have coercion := value_coercion p 1
    simp only [Rat.cast_one] at coercion
    rw [← coercion]
    exact Rat.cast_eq_zero
  have lo := RootCountCertificate.variation_coercion (c.representative :: c.tail) 0
  have hi := RootCountCertificate.variation_coercion (c.representative :: c.tail) 1
  simp only [Rat.cast_zero] at lo
  simp only [Rat.cast_one] at hi
  simpa only [openCount, RootCountCertificate.count, lo, hi, right] using result

def check (points : List Point) (c : Cover) : Bool :=
  RootCountCertificate.check c.polynomial c.certificate &&
    decide ((c.members.map Member.point).Nodup) &&
    c.members.all (memberCheck points c.polynomial) &&
    decide (openCount c.polynomial c.certificate = c.members.length)

noncomputable def selectedValue (points : List Point) (m : Member) : ℝ :=
  (points[m.point]?.getD (.rational 0)).value

noncomputable def represented (points : List Point) (c : Cover) : Set ℝ :=
  {x | x ∈ c.members.map (selectedValue points)}

theorem lookup_value_injective {points : List Point}
    (distinct : (points.map Point.value).Nodup) {i j : ℕ} {a b : Point}
    (left : points[i]? = some a) (right : points[j]? = some b)
    (same : a.value = b.value) : i = j := by
  obtain ⟨hi, ha⟩ := List.getElem?_eq_some_iff.mp left
  obtain ⟨hj, hb⟩ := List.getElem?_eq_some_iff.mp right
  apply (distinct.getElem_inj_iff (hi := by simpa using hi) (hj := by simpa using hj)).mp
  simpa only [List.getElem_map, ha, hb] using same

theorem check_sound {points : List Point} {c : Cover}
    (distinct : (points.map Point.value).Nodup) (checked : check points c = true) :
    represented points c = {x : ℝ | 0 < x ∧ x < 1 ∧ eval c.polynomial x = 0} := by
  classical
  have parts : RootCountCertificate.check c.polynomial c.certificate = true ∧
      (c.members.map Member.point).Nodup ∧
      (∀ m ∈ c.members, memberCheck points c.polynomial m = true) ∧
      openCount c.polynomial c.certificate = c.members.length := by
    simpa only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc]
      using checked
  have roots_finite := (RootCountCertificate.roots_finite parts.1).subset
    (show {x : ℝ | 0 < x ∧ x < 1 ∧ eval c.polynomial x = 0} ⊆
      {x : ℝ | eval c.polynomial x = 0} from fun _ hx => hx.2.2)
  have subset : represented points c ⊆
      {x : ℝ | 0 < x ∧ x < 1 ∧ eval c.polynomial x = 0} := by
    intro x hx
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hx
    obtain ⟨a, ha, domain, root⟩ := memberCheck_sound (parts.2.2.1 m hm)
    simpa only [selectedValue, ha, Option.getD_some, Set.mem_ofPred_eq]
      using And.intro domain.1 ⟨domain.2, root⟩
  have no_duplicates : (c.members.map (selectedValue points)).Nodup := by
    change (c.members.map (selectedValue points)).Pairwise (· ≠ ·)
    rw [List.pairwise_map]
    have ids : c.members.Pairwise (fun a b => a.point ≠ b.point) := by
      simpa only [List.Nodup, List.pairwise_map] using parts.2.1
    apply ids.imp_of_mem
    intro a b ha hb different same
    obtain ⟨pa, hpa, _, _⟩ := memberCheck_sound (parts.2.2.1 a ha)
    obtain ⟨pb, hpb, _, _⟩ := memberCheck_sound (parts.2.2.1 b hb)
    apply different
    apply lookup_value_injective distinct hpa hpb
    simpa only [selectedValue, hpa, hpb, Option.getD_some] using same
  have cardinal : (represented points c).ncard = c.members.length := by
    have equal : represented points c =
        ((c.members.map (selectedValue points)).toFinset : Set ℝ) := by
      ext x
      simp [represented]
    rw [equal, Set.ncard_coe_finset, List.toFinset_card_of_nodup no_duplicates, List.length_map]
  apply Set.eq_of_subset_of_ncard_le subset _ roots_finite
  rw [← openCount_sound parts.1, parts.2.2.2, cardinal]

end ExactCIs.Unconditional.GlobalCheckerProjection
