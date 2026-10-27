/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.ProductBinomial

/-! # Count-preserving table and outcome names used by the frozen U0 contracts -/
namespace ExactCIs.Table

def groupSwap (table : Table) : Table := ⟨table.c, table.d, table.a, table.b⟩

theorem groupSwap_groupSwap (table : Table) : groupSwap (groupSwap table) = table := by
  cases table
  rfl

def outcomeComplement (table : Table) : Table := ⟨table.b, table.a, table.d, table.c⟩

theorem outcomeComplement_outcomeComplement (table : Table) :
    outcomeComplement (outcomeComplement table) = table := by
  cases table
  rfl

theorem n1_groupSwap (table : Table) : (groupSwap table).n1 = table.n0 := rfl
theorem n0_groupSwap (table : Table) : (groupSwap table).n0 = table.n1 := rfl

theorem n1_outcomeComplement (table : Table) : (outcomeComplement table).n1 = table.n1 := by
  simp only [outcomeComplement, n1, Nat.add_comm]

theorem n0_outcomeComplement (table : Table) : (outcomeComplement table).n0 = table.n0 := by
  simp only [outcomeComplement, n0, Nat.add_comm]

end ExactCIs.Table

namespace ExactCIs.Unconditional

def PositiveGroupTotals (table : Table) : Prop := 0 < table.n1 ∧ 0 < table.n0

abbrev TableAt (n1 n0 : ℕ) := ProductBinomial.Outcome n1 n0

abbrev ProductBinomial.Outcome.toTable (n1 n0 : ℕ) (o : ProductBinomial.Outcome n1 n0) :=
  ProductBinomial.toTable o

namespace TableAt

def x {n1 n0 : ℕ} (o : TableAt n1 n0) : ℕ := o.1.val
def y {n1 n0 : ℕ} (o : TableAt n1 n0) : ℕ := o.2.val

def of (table : Table) : TableAt table.n1 table.n0 :=
  (⟨table.a, by simp only [Table.n1]; omega⟩,
    ⟨table.c, by simp only [Table.n0]; omega⟩)

def groupSwap {n1 n0 : ℕ} (o : TableAt n1 n0) : TableAt n0 n1 := o.swap

theorem of_x (table : Table) : x (of table) = table.a := rfl
theorem of_y (table : Table) : y (of table) = table.c := rfl

theorem toTable_of (table : Table) : ProductBinomial.toTable (of table) = table := by
  cases table
  simp only [of, ProductBinomial.toTable, Table.n1, Table.n0, Nat.add_sub_cancel_left]

theorem of_groupSwap (table : Table) : of (Table.groupSwap table) = groupSwap (of table) := rfl

theorem groupSwap_groupSwap {n1 n0 : ℕ} (o : TableAt n1 n0) :
    groupSwap (groupSwap o) = o := rfl

theorem groupSwap_toTable {n1 n0 : ℕ} (o : TableAt n1 n0) :
    ProductBinomial.toTable (groupSwap o) = Table.groupSwap (ProductBinomial.toTable o) := rfl

end TableAt

end ExactCIs.Unconditional
