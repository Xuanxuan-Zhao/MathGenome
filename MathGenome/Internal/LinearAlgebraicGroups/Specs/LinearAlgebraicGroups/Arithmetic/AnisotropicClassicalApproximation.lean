import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicDivisionApproximation
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.AnisotropicSpinQuotients
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.IsotropicSpinGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Composition.OctonionAutomorphisms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.OuterTypeAModels
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SymplecticInvolutionModels
import Mathlib.GroupTheory.Index

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj Matrix

universe u v

namespace LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicClassicalApproximation

open _root_.LinearAlgebraicGroups.Arithmetic (GlobalFieldData)
open _root_.LinearAlgebraicGroups.Arithmetic.SymplecticIsometryDescent
  (Involution PointsOf isometryPoints)
open _root_.LinearAlgebraicGroups.Arithmetic.LocalOuterTypeAAlgebras (conjugateTranspose)
open _root_.LinearAlgebraicGroups.UnitaryNormEquations (SecondKind)
open _root_.LinearAlgebraicGroups.Albert.SpinSpecification
  (SchemePoints ScalarClifford IsSpinPointRepresentation)
open _root_.LinearAlgebraicGroups.Composition.Specification (OctonionNormConditions)
open _root_.LinearAlgebraicGroups.Composition.OctonionAutomorphismSpecification (AutomorphismGroup)
open _root_.Specs.RM03.CSA (isCentralSimple degree)
open RelativeRootIrreducibility (IsAbsolutelyAlmostSimple)
open SimplyConnectedLattice (GeometricallySimplyConnected)
open OuterTypeAModels (RepresentsNormOne RepresentsUnitary)
open AnisotropicSpinQuotients (RegularModel)
open IsotropicSpinGeneration (IsIsotropic)

/-- Global anisotropy of the semisimple group, in terms of rational cocharacters. -/
abbrev GloballyAnisotropic {K : Type u} [Field K] (G : AffineAlgebraicGroup K) : Prop :=
  AnisotropicDivisionApproximation.GloballyAnisotropic G

/-- The full adelic quotient and the approximation assertion in the same
closed realization, for either kind of global field. -/
abbrev AdelicConclusions {K : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    (G : AffineAlgebraicGroup K) : Prop :=
  AnisotropicDivisionApproximation.AdelicConclusions D G

/-- The anisotropic inner type A application for the norm-one group of
a central division algebra. -/
def InnerTypeA : Prop :=
  ∀ {K A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [DivisionRing A] [Algebra K A] (hA : isCentralSimple K A),
    ∀ {I : Type u} [Fintype I] (b : Module.Basis I K A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      RepresentsNormOne hA b G → AdelicConclusions D G

/-- The anisotropic outer type A application for the special unitary
group of a central simple algebra over its quadratic diagram field. -/
def OuterTypeA : Prop :=
  ∀ {K E A : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [Field E] [Algebra K E] [Algebra.IsSeparable K E] [Ring A]
    [Algebra K A] [Algebra E A] [IsScalarTower K E A],
    Module.finrank K E = 2 →
    ∀ {I : Type u} [Fintype I] (hA : isCentralSimple E A), 3 ≤ degree E A →
    ∀ (b : Module.Basis I E A) (s : SecondKind K E A) (G : AffineAlgebraicGroup K),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      RepresentsUnitary hA b s G → AdelicConclusions D G

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

/-- The anisotropic quadratic spin models of dimension at least five,
with either of the regular polar forms in characteristic two. -/
def QuadraticSpin : Prop :=
  ∀ {K V : Type u} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (D : GlobalFieldData.{u,v} K) (q : QuadraticForm K V) (r : Option V),
    RegularModel q r → (∀ x, q x = 0 → x = 0) → 5 ≤ Module.finrank K V →
    ∀ (G : AffineAlgebraicGroup K)
      (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      IsSpinPointRepresentation q G.val e → AdelicConclusions D G

/-- The dimension-three number-field case of quadratic spin, corresponding
to the norm-one group of the even Clifford quaternion algebra. -/
def RankOneQuadraticSpin : Prop :=
  ∀ {K V : Type u} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (q : QuadraticForm K V),
    RegularModel q none → (∀ x, q x = 0 → x = 0) → Module.finrank K V = 3 →
    ∀ (G : AffineAlgebraicGroup K)
      (e : ∀ L : CommAlgCat.{u} K, SchemePoints G.val L →* (ScalarClifford q L)ˣ),
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      IsSpinPointRepresentation q G.val e →
      AdelicConclusions (GlobalFieldData.number.{u,v} inferInstance) G

/-- The anisotropic octonion automorphism group application. -/
def Octonion : Prop :=
  ∀ {K C : Type u} [Field K] (D : GlobalFieldData.{u,v} K)
    [NonAssocRing C] [Module K C] [IsScalarTower K C C] [SMulCommClass K C C]
    (q : QuadraticForm K C) (A : AutomorphismGroup K C),
    OctonionNormConditions q → (∀ x, q x = 0 → x = 0) →
    ∀ G : AffineAlgebraicGroup K,
      IsAbsolutelyAlmostSimple G → GeometricallySimplyConnected G → GloballyAnisotropic G →
      Nonempty (G.val ≅ A.group) → AdelicConclusions D G

/-- A nondegenerate Hermitian space of dimension at least three over a
separable quadratic local field extension is isotropic in any characteristic. -/
def LocalUnitaryIsotropy : Prop :=
  ∀ {F E : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [Field E] [Algebra F E] [Algebra.IsSeparable F E],
    Module.finrank F E = 2 →
    ∀ (σ : E ≃ₐ[F] E), σ ≠ 1 → ∀ n : ℕ, 3 ≤ n →
      ∀ H : (Matrix (Fin n) (Fin n) E)ˣ,
        conjugateTranspose σ H.val = H.val →
        ∃ x : Fin n → E, x ≠ 0 ∧ dotProduct (σ ∘ x) (H.val *ᵥ x) = 0

/-- The nonzero norm subgroup of a separable quadratic extension of
a characteristic-two nonarchimedean local field has index two. -/
def CharacteristicTwoQuadraticNormIndex : Prop :=
  ∀ {F E : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [CharP F 2]
    [Field E] [Algebra F E] [Algebra.IsSeparable F E],
    Module.finrank F E = 2 →
      (Units.map (Algebra.norm F : E →* F)).range.index = 2

/-- Local isotropy of all regular spin forms in the dimension range of
the application, including both characteristic-two cases. -/
def LocalSpinIsotropy : Prop :=
  ∀ {F V : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (q : QuadraticForm F V) (r : Option V),
    RegularModel q r → 5 ≤ Module.finrank F V → IsIsotropic q

end LinearAlgebraicGroups.Specs.Arithmetic.AnisotropicClassicalApproximation
