import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms

open CategoryTheory

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicOctonionApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (Adeles StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
  (FinitePoints diagonalSubgroup)
open _root_.LinearAlgebraicGroups.Composition.Specification (OctonionNormConditions)
open _root_.LinearAlgebraicGroups.Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open CharacterDescent (Cocharacter)
open IntegralModels (MatrixRealization)
open OppositeRadicals (IsNoncentral)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Compactness of the full adelic quotient and strong approximation for
the group scheme of an anisotropic octonion algebra over a global field. -/
def Octonion : Prop :=
  ∀ {K C : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
    (q : QuadraticForm K C) (A : AutomorphismGroup K C),
    OctonionNormConditions q → (∀ x, q x = 0 → x = 0) →
    ∀ G : AffineAlgebraicGroup K,
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
      (¬ ∃ c : Cocharacter G.val, IsNoncentral c) →
      Nonempty (G.val ≅ A.group) →
      ∀ i : MatrixRealization G,
        CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) ∧
        ∀ S : Finset D.Place, S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
          StrongApproximation D i S

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicOctonionApproximation
