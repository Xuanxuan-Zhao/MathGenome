import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralSemisimpleModel

universe u

namespace LinearAlgebraicGroups.Specs.IntegralRealization

/-- Every finite based reduced root datum has an integral split pinned model.
The model uses the full character lattice and realizes the given based datum
with its marked torus and root coordinates in every field fibre. -/
def Statement : Prop :=
  ∀ D : Pinning.BasedRootDatum.{u}, Nonempty (IntegralSemisimpleModel.Model D)

end LinearAlgebraicGroups.Specs.IntegralRealization
