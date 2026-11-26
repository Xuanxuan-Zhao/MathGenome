import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.ApproximationOfLocalWords
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.InnerTypeALocalGeneration
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.InnerTypeA

noncomputable section

set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

open AlgebraicGeometry CategoryTheory Opposite
open scoped TensorProduct

universe u v

namespace LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA.Spec

open AdelicGroups ApproximationOfLocalWords
open InnerTypeALocalGeneration.Spec (matrixCentralSimple)
open LocalNormOneCommutators.Spec (elementaryGroup)
open LinearAlgebraicGroups.Specs (AffineAlgebraicGroup)
open LinearAlgebraicGroups.Specs.IntegralModels (MatrixRealization)
open LinearAlgebraicGroups.Specs.StandardGroups (HopfOperations spectrum)
open LinearAlgebraicGroups.Descent.InnerTypeA.Specification (NormOneCoordinates normOneIdeal)
open _root_.Specs.RM03.CSA (isCentralSimple)
open _root_.Specs.RM03.CSA.NormOneGroup (normAt)

variable {K A : Type u} [Field K] [Ring A] [Algebra K A]
  {ι : Type u} [Fintype ι] (hA : isCentralSimple K A) (b : Module.Basis ι K A)

/-- The norm equation model, with the identification of points in algebra coordinates. -/
structure NormOnePresentation where
  operations : HopfOperations K (NormOneCoordinates hA b)
  point : letI := operations.hopf
    ∀ R : TestAlgebra K,
      ((groupPointsFunctor K).obj (spectrum K (NormOneCoordinates hA b)).val).obj R ≃
        {x : R ⊗[K] A // normAt hA b x = 1}
  point_one : letI := operations.hopf
    ∀ R, (point R 1).1 = 1
  point_mul : letI := operations.hopf
    ∀ R x y, (point R (x * y)).1 = (point R x).1 * (point R y).1
  point_natural : letI := operations.hopf
    ∀ {R S : TestAlgebra K} (f : R ⟶ S)
      (x : ((groupPointsFunctor K).obj (spectrum K (NormOneCoordinates hA b)).val).obj R),
      (point S (((groupPointsFunctor K).obj (spectrum K (NormOneCoordinates hA b)).val).map f x)).1 =
        Algebra.TensorProduct.map f.hom (AlgHom.id K A) (point R x).1
  coordinate : letI := operations.hopf
    ∀ (R : TestAlgebra K) (f : NormOneCoordinates hA b →ₐ[K] R) (l : ι),
      (b.baseChange R).repr
          (point R ((testSpec K).map (CommAlgCat.ofHom f).op)).1 l =
        f (Ideal.Quotient.mk (normOneIdeal hA b) (MvPolynomial.X l))

abbrev NormOnePresentation.group {hA : isCentralSimple K A} {b : Module.Basis ι K A}
    (P : NormOnePresentation hA b) : AffineAlgebraicGroup K :=
  letI := P.operations.hopf
  spectrum K (NormOneCoordinates hA b)

variable {D : Type u} [Ring D] [Algebra K D] {m r : ℕ}

/-- The two distinct block indices of an elementary block subgroup. -/
abbrev BlockIndex (m : ℕ) := ULift.{u} { ij : Fin m × Fin m // ij.1 ≠ ij.2 }

/-- The elementary matrix (1+aE_{ij}) over a test algebra, in tensor coordinates. -/
def blockElement {R : Type u} [CommRing R] [Algebra K R]
    (d : Module.Basis (Fin r) K D) (ij : BlockIndex.{u} m) (a : Fin r → R) :
    R ⊗[K] Matrix (Fin m) (Fin m) D :=
  1 + ∑ l, a l ⊗ₜ[K] Matrix.single ij.down.1.1 ij.down.1.2 (d l)

/-- The conclusions for the local subgroups and the diagonal in the restricted product. -/
def LocalAndAdelicConclusions {G : AffineAlgebraicGroup K} (places : GlobalFieldData.{u,v} K)
    (D : Type u) [Ring D] [Algebra K D] (m r : ℕ)
    (f : BlockIndex.{u} m → (ParameterSpace K r ⟶ G.val.X)) : Prop :=
  Nonempty (MatrixRealization G) ∧
    ∀ i : MatrixRealization G,
      (∀ w : places.Place, Dense (generatedAt (G := G) (ι := BlockIndex.{u} m) (n := fun _ => r) f places i w :
        Set (LocalPoints places i w))) ∧
      (∀ (w : places.Place) (s : ℕ), 0 < s →
        Nonempty ((places.Completion w ⊗[K] D) ≃ₐ[places.Completion w]
          Matrix (Fin s) (Fin s) (places.Completion w)) →
        generatedAt (G := G) (ι := BlockIndex.{u} m) (n := fun _ => r) f places i w = ⊤) ∧
      (∀ w : places.Place, ¬ CompactSpace (LocalPoints places i w)) ∧
      ∀ S : Finset places.Place, S.Nonempty → StrongApproximation places i S

/-- The reduced-norm-one group of a matrix algebra over a global central division
algebra satisfies strong approximation away from a finite nonempty set of places.
The parametrizations are the block transvections on every test algebra. -/
def IsotropicInnerTypeAStrongApproximation : Prop :=
  ∀ {K : Type u} [Field K] (places : GlobalFieldData.{u,v} K)
    {D : Type u} [DivisionRing D] [Algebra K D] (hD : isCentralSimple K D)
    (m : ℕ) (hm : 2 ≤ m),
    let A := Matrix (Fin m) (Fin m) D
    let hA := matrixCentralSimple hD (by omega : 0 < m)
    ∀ (d : Module.Basis (Fin (Module.finrank K D)) K D)
      (b : Module.Basis (ULift.{u} (Fin (Module.finrank K A))) K A),
      ∃ (P : NormOnePresentation hA b)
        (f : BlockIndex.{u} m → (ParameterSpace K (Module.finrank K D) ⟶ P.group.val.X)),
        (∀ (R : TestAlgebra K) (j : BlockIndex.{u} m) (a : Fin (Module.finrank K D) → R),
          (P.point R (evaluate (f j) a)).1 = blockElement d j a) ∧
        LocalAndAdelicConclusions (G := P.group) places D m (Module.finrank K D) f

end LinearAlgebraicGroups.Arithmetic.IsotropicInnerTypeA.Spec
