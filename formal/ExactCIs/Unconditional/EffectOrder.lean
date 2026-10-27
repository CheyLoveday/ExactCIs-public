/-
Copyright (c) 2026 ExactCIs Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: ExactCIs Contributors
-/
import ExactCIs.Unconditional.EffectCoordinate

/-! # Order isomorphism between compact effects and extended nonnegative effects -/
namespace ExactCIs.Unconditional.EffectOrder

open EffectCoordinate
open scoped NNReal

abbrev BetaEffect := ENNReal

noncomputable def encode : EffectState → BetaEffect
  | .finite x nonnegative => ENNReal.ofNNReal (⟨x, nonnegative⟩ : ℝ≥0)
  | .positiveInfinity => ⊤

noncomputable def decode : BetaEffect → EffectState
  | ⊤ => .positiveInfinity
  | (x : ℝ≥0) => .finite x x.property

theorem decode_encode (e : EffectState) : decode (encode e) = e := by cases e <;> rfl

theorem encode_decode (e : BetaEffect) : encode (decode e) = e := by
  cases e using ENNReal.recTopCoe <;> rfl

theorem encode_le_iff (a b : EffectState) : encode a ≤ encode b ↔ compact a ≤ compact b := by
  cases a with
  | positiveInfinity =>
    cases b with
    | positiveInfinity => simp [encode, compact]
    | finite y hy =>
      constructor
      · intro impossible
        exact False.elim (ENNReal.not_top_le_coe impossible)
      · intro impossible
        exact False.elim (not_le_of_gt (finiteCompact_mem hy).2 impossible)
  | finite x hx =>
    cases b with
    | positiveInfinity =>
      simp only [encode, compact, le_top, true_iff]
      exact (finiteCompact_mem hx).2.le
    | finite y hy =>
      have reduced : encode (.finite x hx) ≤ encode (.finite y hy) ↔ x ≤ y :=
        ENNReal.coe_le_coe
      apply reduced.trans
      constructor
      · exact finiteCompact_strictMonoOn.monotoneOn hx hy
      · intro order
        by_contra reverse
        exact not_lt_of_ge order (finiteCompact_strictMonoOn hy hx (lt_of_not_ge reverse))

noncomputable def compactEquiv : Compact ≃ BetaEffect :=
  ({ toFun := effect
     invFun := fun e => ⟨compact e, compact_mem e⟩
     left_inv := fun s => Subtype.ext (compact_effect s)
     right_inv := effect_compact } : Compact ≃ EffectState).trans
    { toFun := encode
      invFun := decode
      left_inv := decode_encode
      right_inv := encode_decode }

noncomputable def orderIso : Compact ≃o BetaEffect where
  toEquiv := compactEquiv
  map_rel_iff' := by
    intro a b
    change encode (effect a) ≤ encode (effect b) ↔ a ≤ b
    rw [encode_le_iff, compact_effect, compact_effect]
    rfl

theorem finite_map (x : ℝ) (nonnegative : 0 ≤ x) :
    orderIso ⟨finiteCompact x, (finiteCompact_mem nonnegative).1,
      (finiteCompact_mem nonnegative).2.le⟩ = ENNReal.ofNNReal (⟨x, nonnegative⟩ : ℝ≥0) := by
  exact congrArg encode (effect_compact (.finite x nonnegative))

theorem infinity_map : orderIso ⟨1, zero_le_one, le_rfl⟩ = ⊤ := by
  change encode (effect ⟨1, zero_le_one, le_rfl⟩) = ⊤
  simp [effect, encode]

end ExactCIs.Unconditional.EffectOrder

namespace ExactCIs.Unconditional.Structural

/-- The concrete compact/extended order isomorphism required by U0 B.16.4. -/
noncomputable def effectOrderIso : EffectCoordinate.Compact ≃o EffectOrder.BetaEffect :=
  EffectOrder.orderIso

end ExactCIs.Unconditional.Structural
