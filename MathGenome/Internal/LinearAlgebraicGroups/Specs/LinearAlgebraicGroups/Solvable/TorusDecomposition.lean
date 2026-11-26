import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.GeometricTorusSplitting
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Solvable.SplitTorusConjugacy

universe u

namespace LinearAlgebraicGroups.Specs.TorusDecomposition

/-- Result B13. Maximal tori give radical complements and are conjugate by the
radical over an algebraically closed field. Over any field the corresponding
assertions hold for a split solvable group and its maximal split tori.
Over a perfect field a split torus action on a smooth connected unipotent
group preserves a central series with one-dimensional additive factors. -/
def SplittingConjugacyAndStableSeries : Prop :=
  GeometricTorusSplitting.Splitting.{u} ∧
  GeometricTorusSplitting.Conjugacy.{u} ∧
  SplitTorusConjugacy.Splitting.{u} ∧
  SplitTorusConjugacy.Conjugacy.{u} ∧
  EquivariantUnipotentSeries.StableSeriesForTorusAction.{u}

end LinearAlgebraicGroups.Specs.TorusDecomposition
