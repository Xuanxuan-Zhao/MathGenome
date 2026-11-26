import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.DegreeMultiplicity
import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorGradedLayers

namespace Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity

open _root_.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct
open _root_.CommutativeAlgebraNotes.Intersection.ExteriorTensorInverseLimit
open _root_.P103.Specs.Ch06.DimensionConventions (moduleDimensionValue)
open DegreeMultiplicity (hilbertSamuelMultiplicity)

universe u v w

/-- Dimensions and maximal-ideal multiplicities for the completed exterior tensor product
of two nonzero finite modules over power series rings over a field. -/
def DimensionAndMultiplicity : Prop :=
  ∀ (k : Type u) [Field k] (a b : ℕ) (M : Type v) (N : Type w)
    [AddCommGroup M] [Module (X k a) M] [Module.Finite (X k a) M] [Nontrivial M]
    [AddCommGroup N] [Module (Y k b) N] [Module.Finite (Y k b) N] [Nontrivial N],
    let T := _root_.CommutativeAlgebraNotes.Intersection.ExteriorTensorProduct.Spec.productValue
      k a b M N
    Nontrivial T ∧
      moduleDimensionValue (S k a b) T =
        moduleDimensionValue (X k a) M + moduleDimensionValue (Y k b) N ∧
      hilbertSamuelMultiplicity (jointIdeal k a b) T =
        hilbertSamuelMultiplicity (variableIdeal k (Fin a)) M *
          hilbertSamuelMultiplicity (variableIdeal k (YIndex b)) N

end Specs.CommutativeAlgebraNotes.Intersection.ExteriorTensorDimensionAndMultiplicity
