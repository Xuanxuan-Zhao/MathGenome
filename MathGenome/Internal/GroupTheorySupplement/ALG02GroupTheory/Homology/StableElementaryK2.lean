import MathGenome.Internal.GroupTheorySupplement.Specs.ALG02GroupTheory.Homology.StableElementaryK2
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.SteinbergUniversality
import MathGenome.Internal.GroupTheorySupplement.ALG02GroupTheory.Extensions.UniversalCentral

namespace ALG02GroupTheory.StableElementaryK2

open Extensions.StableSteinberg (steinbergExtension steinbergExtension_isUniversal)
open Extensions.UniversalCentral (universal_kernel_homology)

universe u

/-- The Hopf kernel identification for the universal stable Steinberg extension. -/
theorem k₂_homology_identification : Spec.K2HomologyIdentification.{u} := by
  intro R _
  exact universal_kernel_homology.{u, u, u, 0}
    (S := steinbergExtension R) (steinbergExtension_isUniversal R)

end ALG02GroupTheory.StableElementaryK2
