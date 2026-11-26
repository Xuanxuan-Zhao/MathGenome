import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.CharacteristicTwoQuadraticPairs
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import Mathlib.RingTheory.MatrixAlgebra

open CategoryTheory Matrix
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped TensorProduct CategoryTheory.MonObj

universe u

namespace LinearAlgebraicGroups.Specs.Arithmetic.SplitQuadraticPairSpinComparison

open RM03.Brauer.SemilinearDescent (AlgebraAction)
open NontrialitarianSpinModels (DescendedQuadraticPair SpinModel symmetricPart)
open CharacteristicTwoQuadraticPairs (algebraReducedTrace PreservesSemitrace)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open IsotropicSpinGeneration (HyperbolicPair HasSpinCocharacterFormula)
open CharacterDescent (Cocharacter)
open _root_.LinearAlgebraicGroups.CocharacterDynamics (LimitDecomposition oppositeCocharacter)
open OppositeRadicals (IsNoncentral)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (IsSpinPointRepresentation IsVectorAction ScalarClifford)

noncomputable section

variable {F K I : Type u} [Field F] [Field K] [Algebra F K]
  [Fintype I] [DecidableEq I]
  {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)}
  {D : DescendedQuadraticPair ρ} {G : AffineAlgebraicGroup F}
  {n : ℕ} (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)

/-- The scalar form in the field division-factor case, with the matrix
and semitrace equations of the actual descended pair. -/
structure RecoveredForm where
  rank : n = 2 * Fintype.card I
  gram : (Matrix (Fin n) (Fin n) F)ˣ
  representative : ρ.fixedSubalgebra
  form : QuadraticForm F (Fin n → F)
  adjoint : ∀ x, e (D.involution.toLinearMap x) = gram.inv * (e x).transpose * gram.val
  traceOne : representative + D.involution.toLinearMap representative = 1
  semitrace : ∀ x : symmetricPart D.involution,
    D.semitrace x = algebraReducedTrace D.centralSimple (representative * x.val)
  diagonal : ∀ x, form x = x ⬝ᵥ (gram.val *ᵥ (e representative *ᵥ x))
  polar : form.polarBilin = Matrix.toLinearMap₂' F gram.val
  regular : form.polarBilin.Nondegenerate
  isometries : ∀ g : ρ.fixedSubalgebraˣ,
    (∀ x, form (e g.val *ᵥ x) = form x) ↔
      D.involution.toLinearMap g.val * g.val = 1 ∧ PreservesSemitrace D g

/-- Matrix coordinates induced by the given field division-factor presentation
over a test algebra. -/
def testMatrix (R : TestAlgebra F) :
    (R ⊗[F] ρ.fixedSubalgebra) ≃ₐ[R] Matrix (Fin n) (Fin n) R :=
  (Algebra.TensorProduct.congr (AlgEquiv.refl : R ≃ₐ[R] R) e).trans
    { (matrixEquivTensor (Fin n) F R).symm.toRingEquiv with
      commutes' := fun r => by
        change (matrixEquivTensor (Fin n) F R).symm (r ⊗ₜ[F] 1) = _
        rw [matrixEquivTensor_apply_symm, Matrix.map_one _ (map_zero _) (map_one _),
          Algebra.algebraMap_eq_smul_one] }

/-- The Clifford representation of the same spin scheme, with its actual
vector projection in the coordinates of the descended matrix algebra. -/
def CompatibleRepresentation (M : SpinModel G D) (P : RecoveredForm (D := D) e)
    (a : ∀ R : TestAlgebra F, Points G.val.X R →* (ScalarClifford P.form R)ˣ) : Prop :=
  IsSpinPointRepresentation P.form G.val a ∧
  ∀ (R : TestAlgebra F) (p : Points G.val.X R),
    ∃ g : (R ⊗[F] (Fin n → F)) ≃ₗ[R] (R ⊗[F] (Fin n → F)),
      IsVectorAction P.form R (a R p) g ∧
      let b := (Pi.basisFun F (Fin n)).baseChange R
      LinearMap.toMatrix b b g.toLinearMap =
        testMatrix e R (M.fullPoints R
          (p ≫ (M.projection ≫ M.inclusion).hom.hom)).val

/-- Comparison for the recovered scalar quadratic form over every test algebra. -/
def SplitSpinComparison : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
    {G : AffineAlgebraicGroup F} (M : SpinModel G D)
    (n : ℕ) (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)
    (P : RecoveredForm (D := D) e),
    ∃ a, CompatibleRepresentation e M P a

/-- Local generation of the original group by the contracting subgroups of
opposite spin cocharacters in the field division-factor case. -/
def LocalSplitSpinGeneration : Prop :=
  ∀ {F K I : Type u} [Field F] [CharP F 2] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field K] [Algebra F K]
    [FiniteDimensional F K] [IsGalois F K] [Fintype I] [DecidableEq I]
    {ρ : AlgebraAction F K (Matrix (I ⊕ I) (I ⊕ I) K)} {D : DescendedQuadraticPair ρ}
    {G : AffineAlgebraicGroup F} (M : SpinModel G D),
    IsAbsolutelyAlmostSimple G →
    ∀ (n : ℕ), 8 ≤ n →
    ∀ (e : ρ.fixedSubalgebra ≃ₐ[F] Matrix (Fin n) (Fin n) F)
      (P : RecoveredForm (D := D) e),
      ∃ (a : ∀ R : TestAlgebra F, Points G.val.X R →* (ScalarClifford P.form R)ˣ)
        (h : HyperbolicPair P.form) (c : Cocharacter G.val),
        CompatibleRepresentation e M P a ∧ HasSpinCocharacterFormula h a c ∧ IsNoncentral c ∧
        ∃ (B : LimitDecomposition c) (C : LimitDecomposition (oppositeCocharacter c)),
          SubgroupSections B.contracting (𝟙_ (SchemeOver F)) ⊔
            SubgroupSections C.contracting (𝟙_ (SchemeOver F)) = ⊤

end
end LinearAlgebraicGroups.Specs.Arithmetic.SplitQuadraticPairSpinComparison
