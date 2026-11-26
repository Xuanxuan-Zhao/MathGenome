import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteValuationDegreeBound
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.PurelyInseparableValuationExtension
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability

namespace CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability

open Specs.CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability

universe u v

/-- Theorem 5.22 gives the fundamental inequality for finite field extensions and
identifies the unique extension in the purely inseparable case. -/
theorem valuation_extension_degrees_and_inseparability :
    Specs.CommutativeAlgebraNotes.FiniteValuationDegreeBound.DegreeBound.{u, v} ∧
      PurelyInseparableClassification.{u, v} := by
  refine ⟨FiniteValuationDegreeBound.degree_bound, ?_⟩
  intro K L _ _ _ _ V
  obtain ⟨W, hW, hUnique⟩ :=
    PurelyInseparableValuationExtension.existsUnique_extension (L := L) V
  exact ⟨W, hW, PurelyInseparableValuationExtension.extension_eq_integralClosure V W hW, hUnique⟩

end CommutativeAlgebraNotes.ValuationExtensionDegreesAndInseparability
