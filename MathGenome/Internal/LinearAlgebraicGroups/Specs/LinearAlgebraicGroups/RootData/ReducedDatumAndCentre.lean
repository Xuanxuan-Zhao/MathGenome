import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.DatumAndWeyl
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.SchemeCentre

universe u

namespace LinearAlgebraicGroups.Specs.ReducedDatumAndCentre

/-- For every split connected reductive pair, the actual roots and coroots
form a finite reduced integral root datum whose Weyl group identifies with the
scheme normalizer quotient. The scheme centre is the intersection of the root
kernels in the torus and is diagonalizable with character group the full
quotient by the root lattice. -/
def Statement : Prop :=
  DatumAndWeyl.Statement.{u} ∧ SchemeCentre.CentreFormula.{u}

end LinearAlgebraicGroups.Specs.ReducedDatumAndCentre
