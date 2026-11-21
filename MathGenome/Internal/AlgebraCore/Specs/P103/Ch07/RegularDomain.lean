import MathGenome.Internal.AlgebraCore.Specs.P103.Ch07.EmbeddingDimension

/-!
The domain assertion of Theorem 7.7, paper.tex:1281–1291.
Regularity is the shared equality of embedding dimension and Krull dimension.
The local-ring hypothesis supplies a proper maximal ideal. No reducedness,
nonzero-divisor, or domain condition is included in regularity.
-/
namespace Specs.P103.RegularDomain

open P103.Specs.Ch07.EmbeddingDimension
open P103.Specs.Ch06.DimensionConventions

universe u

def domainType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    regularLocalValue R → IsDomain R

/-- The dimension-zero boundary of the same assertion is a field. -/
def dimensionZeroType : Prop :=
  ∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R],
    regularLocalValue R → ringDimensionValue R = 0 → IsField R

end Specs.P103.RegularDomain
