import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient

open CategoryTheory CategoryTheory.MonoidalCategory

universe u

namespace LinearAlgebraicGroups.Specs.ReductiveProductWithSplitTorus

open IntegralCentralQuotient

/-- Taking the product with a split integral torus preserves connected reductive
geometric fibres and the maximality of the product of the marked tori. -/
def Statement : Prop :=
  let R := IntegralRing.{u}
  ∀ {X M : Type u} [CommGroup X] [CommGroup M]
    [Module.Free ℤ (Additive X)] [Module.Finite ℤ (Additive X)]
    [Module.Free ℤ (Additive M)] [Module.Finite ℤ (Additive M)]
    {G : Grp (OverBase R)}
    (t : HopfSpectrum R (MonoidAlgebra R X) ⟶ G),
    ReductiveFibres t →
    ReductiveFibres (t ⊗ₘ 𝟙 (HopfSpectrum R (MonoidAlgebra R M)))

end LinearAlgebraicGroups.Specs.ReductiveProductWithSplitTorus
