import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.LocalCohomologyCompletion
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.CohenMacaulay.FlatLocalCohenMacaulay
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.CompletionDepthDimension

open Specs.CommutativeAlgebraNotes.CompletionDepthDimension
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (Completion)

namespace CommutativeAlgebraNotes

universe u

local notation "𝔪[" R "]" => IsLocalRing.maximalIdeal R

/-- Faithful flatness and the tensor model give nonvanishing of completion. -/
theorem completion_nontrivial : completionNontrivialType.{u} := by
  intro R M _ _ _ _ _ _ _
  let := AdvCommAlg.CohenMacaulay.completion_faithfullyFlat R
  let e := AdicCompletion.ofTensorProductEquivOfFiniteNoetherian 𝔪[R] M
  exact e.nontrivial_congr.mp
    ((Module.FaithfullyFlat.nontrivial_tensorProduct_iff_right R (Completion R)).mpr
      inferInstance)

/-- Completion preserves the Krull dimension of support. -/
theorem completion_supportDim : completionSupportDimType.{u} := by
  intro R M _ _ _ _ _ _ _
  exact AdvCommAlg.CohenMacaulay.completion_dimension R M

/-- Completion preserves depth with respect to the maximal ideal. -/
theorem completion_depth : completionDepthType.{u} := by
  intro R M _ _ _ _ _ _ _
  exact AdvCommAlg.CohenMacaulay.completion_depth R M

/-- Local cohomology with the completed action agrees naturally with local
cohomology of the adic completion in each integer degree. -/
theorem localCohomologyAdicCompletion : localCohomologyAdicCompletionType.{u} := by
  intro R _ _ _ q
  simpa only [AdicCompletion.maximalIdeal_eq_map] using
    (localCohomologyFiniteCompletion (R := R) q)

end CommutativeAlgebraNotes
