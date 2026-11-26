import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSymplecticApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (Adeles StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
  (FinitePoints diagonalSubgroup)
open _root_.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
  (Involution PointsOf isometryPoints)
open _root_.Specs.RM03.CSA (isCentralSimple)
open IntegralModels (MatrixRealization)
open CharacterDescent (Cocharacter)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open OppositeRadicals (IsNoncentral)

/-- Global anisotropy of the semisimple group, in terms of rational cocharacters. -/
def GloballyAnisotropic {K : Type u} [Field K] (G : AffineAlgebraicGroup K) : Prop :=
  ¬ ∃ c : Cocharacter G.val, IsNoncentral c

/-- The full adelic quotient and the approximation assertion in the same
closed realization, for either kind of global field. -/
def AdelicConclusions {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) : Prop :=
  ∀ i : MatrixRealization G,
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) ∧
    ∀ S : Finset D.Place, S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
      StrongApproximation D i S

/-- The anisotropic type C application for the full isometry group of a
central simple algebra with symplectic involution. -/
def TypeC : Prop :=
  ∀ {K A L : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Ring A] [Algebra K A] [Field L] [Algebra K L] [Algebra.IsAlgebraic K L],
    isCentralSimple K A → ∀ (s : Involution K A) (n : ℕ), 0 < n →
    SymplecticDivisionForms.SplitComparison
      (SymplecticInvolutionModels.DivisionForms.toDivisionInvolution s) L n →
    ∀ G : AffineAlgebraicGroup K,
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      Nonempty (PointsOf G.val ≅ isometryPoints s) → AdelicConclusions D G

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicSymplecticApproximation
