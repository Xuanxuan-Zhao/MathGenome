import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels

open CategoryTheory

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection (rationalProjection)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open GeometricRadicals
  (GeometricGroup identitySubgroup IsSemisimple IsSmoothConnectedNormal IsTrivialSubgroup)
open IntegralModels (MatrixRealization)
open OuterTypeAModels (RepresentsUnitary)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- Special unitary rational points are dense in the finite product at places
where the quadratic centre embeds in the completion. The product carries the
local point topologies of the given closed matrix realization. -/
def SplitCentreWeakApproximation : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E]
    [Ring A] [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A), 3 ≤ degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
      (IsSemisimple G ∧
        ¬ IsIso (identitySubgroup (GeometricGroup G)).inclusion ∧
        ∀ N : ClosedSubgroup (GeometricGroup G).val, IsSmoothConnectedNormal N →
          IsTrivialSubgroup N ∨ IsIso N.inclusion) →
      GeometricallySimplyConnected G →
      RepresentsUnitary hA b s G →
      ∀ (i : MatrixRealization G) (J : Finset D.Place),
        (∀ p ∈ J, ∃ w : D.FinitePlace,
          p = Sum.inl w ∧ Nonempty (E →ₐ[K] D.Completion (Sum.inl w))) →
        DenseRange (rationalProjection D i J)

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicUnitarySplitCentreWeakApproximation
