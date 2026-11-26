import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.ReducedDatumAndCentre
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.LinearAlgebraicGroups.RootData.SchemeCentre

universe u

namespace LinearAlgebraicGroups.RootData.ReducedDatumAndCentre

/-- The reflection-generated Weyl group and the scheme centre of a split
connected reductive pair, with the Weyl action on its actual root datum. -/
theorem reducedDatumAndCentre : Specs.ReducedDatumAndCentre.Statement.{u} :=
  ⟨DatumAndWeyl.datumAndWeyl.{u}, SchemeCentre.schemeCentre.{u}⟩

end LinearAlgebraicGroups.RootData.ReducedDatumAndCentre
