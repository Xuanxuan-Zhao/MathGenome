import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.NontrialitarianSpinModels

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.StrongApproximationNontrialitarianD

open LinearAlgebraicGroups.Arithmetic
open AdelicGroups (StrongApproximation)
open ArithmeticLatticeProjection (FinitePoints)
open IntegralModels (MatrixRealization)
open NontrialitarianSpinModels (HasFixedVectorVertex)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Sufficiency in the strong approximation criterion for nontrialitarian
type `Dₙ`. A fixed vector vertex can be any fixed outer vertex in type `D₄`. -/
def StrongApproximationNontrialitarian : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) (n : ℕ), 4 ≤ n →
    AbsoluteDynkinTypes.IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G →
    HasFixedVectorVertex G n →
    ∀ (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → ¬ CompactSpace (FinitePoints D i S) → StrongApproximation D i S

end LinearAlgebraicGroups.Specs.Arithmetic.StrongApproximationNontrialitarianD
