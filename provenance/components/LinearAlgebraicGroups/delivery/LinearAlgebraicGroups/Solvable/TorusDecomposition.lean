import Specs.LinearAlgebraicGroups.Solvable.TorusDecomposition
import LinearAlgebraicGroups.Solvable.EquivariantUnipotentSeries
import LinearAlgebraicGroups.Solvable.GeometricTorusSplitting

import LinearAlgebraicGroups.Solvable.SplitTorusConjugacy
universe u

namespace LinearAlgebraicGroups.TorusDecomposition

theorem torusDecomposition_conditional
    (conjugacy : Specs.SplitTorusConjugacy.Conjugacy.{u})
    (splitting : Specs.SplitTorusConjugacy.Splitting.{u}) :
    Specs.TorusDecomposition.SplittingConjugacyAndStableSeries.{u} :=
  ⟨GeometricTorusSplitting.splitting, GeometricTorusSplitting.conjugacy,
    splitting, conjugacy, EquivariantUnipotentSeries.stableSeriesForTorusAction⟩

end LinearAlgebraicGroups.TorusDecomposition

universe v8_closure_46348a5f06194873_u0
theorem _root_.«LinearAlgebraicGroups».«TorusDecomposition».«torusDecomposition» : _root_.«LinearAlgebraicGroups».«Specs».«TorusDecomposition».«SplittingConjugacyAndStableSeries».{v8_closure_46348a5f06194873_u0} :=
  @_root_.«LinearAlgebraicGroups».«TorusDecomposition».«torusDecomposition_conditional».{v8_closure_46348a5f06194873_u0} (@_root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«conjugacy».{v8_closure_46348a5f06194873_u0}) (@_root_.«LinearAlgebraicGroups».«SplitTorusConjugacy».«splitting».{v8_closure_46348a5f06194873_u0})
