import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.NormalizedDualizingComplex
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.RegularCoverDualizingModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DualizingComplexHomothety

namespace CommutativeAlgebraNotes.NormalizedDualizingComplex

open Specs.CommutativeAlgebraNotes.NormalizedDualizingComplex
open CommutativeAlgebraNotes.RegularCoverDualizingModel

universe u w

theorem normalizedDualizingComplex : NormalizedDualizingComplexType.{u, w} := by
  intro S R _ _ _ _ _ _ _ _ f _ hf n hn
  obtain ⟨J, _, _⟩ := shiftedRingResolution_exists S n hn
  exact ⟨⟨J⟩, fun J' =>
    ⟨coinduced_bounded_injective f J',
      finite_cohomology f hf hn J',
      DualizingComplexHomothety.derivedHomothety_isIso f hf hn J',
      normalization f hf hn J'⟩⟩

end CommutativeAlgebraNotes.NormalizedDualizingComplex
