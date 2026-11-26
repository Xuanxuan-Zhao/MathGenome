import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (Adeles StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
  (FinitePoints diagonalSubgroup)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open IntegralModels (MatrixRealization)
open CharacterDescent (Cocharacter)
open OppositeRadicals (IsNoncentral)
open OuterTypeAModels (RepresentsUnitary)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- The full adelic quotient of the globally anisotropic special unitary group
is compact. Strong approximation holds away from each finite nonempty set of
places whose product of local point groups is noncompact. -/
def OuterTypeA : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A), 3 ≤ degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
      (¬ ∃ c : Cocharacter G.val, IsNoncentral c) →
      RepresentsUnitary hA b s G →
      ∀ i : MatrixRealization G,
        CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) ∧
        ∀ S : Finset D.Place, S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
          StrongApproximation D i S

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitaryApproximation
