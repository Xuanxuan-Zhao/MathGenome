import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

set_option autoImplicit false

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.StrongApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection (FinitePoints)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The strong approximation criterion over global fields. -/
def Criterion : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G) (S : Finset D.Place),
    IsAbsolutelyAlmostSimple G → S.Nonempty →
    (StrongApproximation D i S ↔
      GeometricallySimplyConnected G ∧ ¬ CompactSpace (FinitePoints D i S))

end LinearAlgebraicGroups.Specs.Arithmetic.StrongApproximation
