import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSufficiency

open LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open LinearAlgebraicGroups.Arithmetic.AdelicGroups (StrongApproximation)
open CharacterDescent (Cocharacter)
open IntegralModels (MatrixRealization)
open OppositeRadicals (IsNoncentral)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- A globally isotropic, geometrically simply connected, absolutely almost
simple group over a global field has strong approximation away from every
finite nonempty set of places. The cocharacter witnesses global isotropy. -/
def IsotropicStrongApproximation : Prop :=
  ∀ {K : Type u} [Field K] (D : GlobalFieldData.{u, v} K)
    (G : AffineAlgebraicGroup K) (i : MatrixRealization G),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    (∃ c : Cocharacter G.val, IsNoncentral c) →
    ∀ (S : Finset D.Place), S.Nonempty → StrongApproximation D i S

end LinearAlgebraicGroups.Specs.Arithmetic.IsotropicSufficiency
