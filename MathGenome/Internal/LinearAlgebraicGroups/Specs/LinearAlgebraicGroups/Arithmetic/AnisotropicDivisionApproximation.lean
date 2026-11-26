import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OppositeRadicals
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.SimplyConnectedLattice
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.SpinFunctor

open CategoryTheory
open scoped CategoryTheory.MonObj

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicDivisionApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.AdelicGroups (Adeles StrongApproximation)
open _root_.LinearAlgebraicGroups.Arithmetic.ArithmeticLatticeProjection
  (FinitePoints diagonalSubgroup)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (SchemePoints ScalarClifford IsSpinPointRepresentation)
open _root_.Specs.RM03.CSA (isCentralSimple)
open IntegralModels (MatrixRealization)
open CharacterDescent (Cocharacter)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open OppositeRadicals (IsNoncentral)
open OuterTypeAModels (RepresentsNormOne)

/-- Global anisotropy expressed by the absence of noncentral rational cocharacters. -/
def GloballyAnisotropic {K : Type u} [Field K] (G : AffineAlgebraicGroup K) : Prop :=
  ¬ ∃ c : Cocharacter G.val, IsNoncentral c

/-- Compactness of the full adelic quotient and strong approximation at every
finite nonempty omitted set with a noncompact product of local groups. -/
def AdelicConclusions {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) : Prop :=
  ∀ i : MatrixRealization G,
    CompactSpace (Adeles D i ∅ ⧸ diagonalSubgroup D i) ∧
    ∀ S : Finset D.Place, S.Nonempty → ¬ CompactSpace (FinitePoints D i S) →
      StrongApproximation D i S

/-- The norm-one group of a central division algebra over a number field or
a global function field. -/
def InnerTypeA : Prop :=
  ∀ {K A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [DivisionRing A] [Algebra K A] (hA : isCentralSimple K A),
    ∀ {I : Type u} [Fintype I] (b : Module.Basis I K A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      RepresentsNormOne hA b G → AdelicConclusions D G

/-- The even Clifford spin group of an anisotropic nondegenerate ternary form
over a number field. -/
def RankOneQuadraticSpin : Prop :=
  ∀ {K V : Type u} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V),
    LinearMap.ker q.polarBilin = ⊥ → (∀ x, q x = 0 → x = 0) → Module.finrank K V = 3 →
    ∀ (G : AffineAlgebraicGroup K)
      (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      IsSpinPointRepresentation q G.val e →
      AdelicConclusions (GlobalFieldData.number.{u,v} inferInstance) G

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicDivisionApproximation
