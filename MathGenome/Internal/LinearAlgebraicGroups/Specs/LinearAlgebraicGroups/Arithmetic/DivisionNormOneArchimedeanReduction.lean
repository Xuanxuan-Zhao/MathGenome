import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.RelativeRootIrreducibility
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.DivisionNormOneArchimedeanReduction

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups
  (Adeles LocalPoints StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
  (FinitePoints diagonalSubgroup)
open _root_.Specs.RM03.CSA (isCentralSimple)
open IntegralModels (MatrixRealization)
open OuterTypeAModels (RepresentsNormOne)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)

/-- With compact full adelic quotient, one may add precisely the noncompact
archimedean factors to the omitted set. Strong approximation for the enlarged
set implies strong approximation for the original set and realization.
For a global function field the membership equivalence gives `T = S`. -/
def ArchimedeanReduction : Prop :=
  ∀ {K A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [DivisionRing A] [Algebra K A] (hA : isCentralSimple K A)
    {I : Type u} [Fintype I] (b : Module.Basis I K A) (G : AffineAlgebraicGroup K),
    IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G →
    RepresentsNormOne hA b G →
    ∀ (i : MatrixRealization G),
      CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) →
      ∀ (S : Finset D.Place), S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
        ∃ T : Finset D.Place,
          (∀ w : D.Place, w ∈ T ↔ w ∈ S ∨
            ∃ a : D.InfinitePlace, w = Sum.inr a ∧
              ¬ CompactSpace (LocalPoints D i (Sum.inr a))) ∧
          (∀ a : D.InfinitePlace, Sum.inr a ∉ T →
            CompactSpace (LocalPoints D i (Sum.inr a))) ∧
          ¬ CompactSpace (FinitePoints D i T) ∧
          (StrongApproximation D i T → StrongApproximation D i S)

end LinearAlgebraicGroups.Specs.Arithmetic.DivisionNormOneArchimedeanReduction
