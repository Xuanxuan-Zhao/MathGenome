import MathGenome.Internal.Specs.D07.Ch20.SeparablePart
import MathGenome.Internal.D07.Ch20.SeparablePartUniformInseparableExponent

/-!
The separable part of an algebraic extension, K07.20.separable_part.

We use the canonical intermediate field of separable elements, rather than
an external separable closure. Mathlib's subfield construction proves closure
under the field operations. For an algebraic extension the upper step is
purely inseparable; an element separable over K remains separable over any
intermediate field, so in a purely inseparable upper step it already belongs
to that intermediate field. This gives uniqueness. Finite-dimensionality
passes to the subfield. The accepted common-exponent helper supplies the
uniform positive-characteristic assertion with no perfection assumption.
-/

universe u v

namespace D07.Ch20.SeparablePart

open Specs.D07.Ch20.SeparablePart

theorem subfield_carrier : SubfieldCarrier.{u, v} := by
  intro K L _ _ _ _
  rfl

theorem separable_lower_step : SeparableLowerStep.{u, v} := by
  intro K L _ _ _ _
  infer_instance

theorem purely_inseparable_upper_step : PurelyInseparableUpperStep.{u, v} := by
  intro K L _ _ _ _
  infer_instance

theorem unique_separable_part : UniqueSeparablePart.{u, v} := by
  intro K L _ _ _ _ T
  exact (eq_separableClosure_iff K L T).symm

theorem exists_unique_separable_part : ExistsUniqueSeparablePart.{u, v} := by
  intro K L _ _ _ _
  refine ⟨separableClosure K L, ⟨separable_lower_step K L,
    purely_inseparable_upper_step K L⟩, ?_⟩
  intro T hT
  exact (unique_separable_part K L T).mp hT

theorem characteristic_zero_part : CharacteristicZeroPart.{u, v} := by
  intro K L _ _ _ _ _
  exact (separableClosure.eq_top_iff K L).mpr inferInstance

theorem finite_separable_part : FiniteSeparablePart.{u, v} := by
  intro K L _ _ _ _
  infer_instance

theorem uniform_exponent : UniformExponent.{u, v} := by
  exact D07.Ch20.SeparablePartUniformInseparableExponent.uniform_inseparable_exponent

end D07.Ch20.SeparablePart
