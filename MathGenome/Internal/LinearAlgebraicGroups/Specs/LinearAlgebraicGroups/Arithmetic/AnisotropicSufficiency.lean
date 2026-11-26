import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicClassicalApproximation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.RootData.AbsoluteDynkinTypes

set_option autoImplicit false

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSufficiency

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection (FinitePoints)
open AbsoluteDynkinTypes (IsAbsolutelyAlmostSimple)
open AnisotropicClassicalApproximation (GloballyAnisotropic)
open IntegralModels (MatrixRealization)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A globally anisotropic, absolutely almost simple, simply connected group
over a global field has strong approximation away from any finite nonempty
set of places whose product of local point groups is noncompact. -/
def StrongApproximationStatement : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K),
    IsAbsolutelyAlmostSimple G →
    GeometricallySimplyConnected G →
    GloballyAnisotropic G →
    ∀ (i : MatrixRealization G) (S : Finset D.Place),
      S.Nonempty → ¬ CompactSpace (FinitePoints D i S) → StrongApproximation D i S

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSufficiency
