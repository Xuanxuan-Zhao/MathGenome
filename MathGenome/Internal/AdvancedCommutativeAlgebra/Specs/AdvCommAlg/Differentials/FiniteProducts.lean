import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Differentials.Universal
import Mathlib.Algebra.Algebra.Pi
import Mathlib.LinearAlgebra.Pi

/-! KD-20: the projection isomorphism, including the empty product.
The action of the product ring on each factor of the target is explicitly
restriction through its coordinate projection. -/
namespace Specs.AdvCommAlg.Differentials

universe u v w
noncomputable section

namespace ProductDifferentials

/-- Restriction of scalars through the i-th ring projection. -/
scoped instance componentModule (A : Type u) {ι : Type v} (B : ι → Type w)
    [CommRing A] [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)] (i : ι) :
    Module (∀ j, B j) (KaehlerDifferential A (B i)) :=
  Module.compHom _ (Pi.evalRingHom B i)

end ProductDifferentials

open scoped ProductDifferentials

/-- The value on every universal differential identifies the isomorphism as
exactly the one induced by all the coordinate projections. `Finite` admits
empty index types, and none of the rings is required to be nonzero. -/
def finiteProducts : Prop :=
  ∀ (A : Type u) (ι : Type v) (B : ι → Type w)
    [CommRing A] [Finite ι] [∀ i, CommRing (B i)] [∀ i, Algebra A (B i)],
    ∃ e : KaehlerDifferential A (∀ i, B i) ≃ₗ[∀ i, B i]
        (∀ i, KaehlerDifferential A (B i)),
      ∀ (b : ∀ i, B i) (i : ι),
        e (KaehlerDifferential.D A (∀ i, B i) b) i =
          KaehlerDifferential.D A (B i) (b i)

end
end Specs.AdvCommAlg.Differentials
