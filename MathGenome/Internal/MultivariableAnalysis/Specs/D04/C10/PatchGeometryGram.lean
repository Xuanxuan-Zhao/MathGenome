import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C02.DerivativeInterfaces
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.LinearVolume
import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.LinearAlgebra.CrossProduct
import Mathlib.Topology.Maps.Basic

/-! Regular patches and the metric Gram factor (paper, 10:patch and 10:gram).
All derivatives are the shared ambient total derivative restricted to an open
parameter domain. No global injectivity follows from regularity. -/
noncomputable section
open Set
open scoped RealInnerProductSpace Matrix
namespace Specs.D04.C10.PatchGeometryGram
open Specs.D04.C01.EuclideanInterfaces.Model
namespace Model

def RegularPatch {k n : ℕ} (U : Set (E k)) (φ : E k → E n) : Prop :=
  IsOpen U ∧ ContDiffOn ℝ 1 φ U ∧ ∀ x ∈ U, Function.Injective (fderiv ℝ φ x)

def EmbeddedPatch {k n : ℕ} (U : Set (E k)) (φ : E k → E n) : Prop :=
  RegularPatch U φ ∧ Topology.IsEmbedding (fun x : U => φ x)

def tangentPlane {k n : ℕ} (φ : E k → E n) (x : E k) : Submodule ℝ (E n) :=
  LinearMap.range (fderiv ℝ φ x).toLinearMap

def columns {k n : ℕ} (A : E k →ₗ[ℝ] E n) : Fin k → E n :=
  fun j => A (standardBasis k j)

def gramMatrix {k n : ℕ} (A : E k →ₗ[ℝ] E n) : Matrix (Fin k) (Fin k) ℝ :=
  (matrixOfLinearMap A).transpose * matrixOfLinearMap A

def gramFactor {k n : ℕ} (A : E k →ₗ[ℝ] E n) : ℝ :=
  Real.sqrt (gramMatrix A).det

def patchGram {k n : ℕ} (φ : E k → E n) (x : E k) :=
  gramMatrix (fderiv ℝ φ x).toLinearMap

def patchJacobian {k n : ℕ} (φ : E k → E n) (x : E k) : ℝ :=
  gramFactor (fderiv ℝ φ x).toLinearMap

/-- The standard oriented coordinate cross product, transported to the shared L2 space. -/
def cross (a b : E 3) : E 3 :=
  WithLp.toLp 2 (crossProduct (WithLp.ofLp a) (WithLp.ofLp b))

def unitNormal (φ : E 2 → E 3) (x : E 2) : E 3 :=
  let c := cross (columns (fderiv ℝ φ x).toLinearMap 0)
    (columns (fderiv ℝ φ x).toLinearMap 1)
  ‖c‖⁻¹ • c

def IsUnitNormal (P : Submodule ℝ (E 3)) (v : E 3) : Prop :=
  ‖v‖ = 1 ∧ ∀ w ∈ P, ⟪v, w⟫ = 0

/-- Square coordinates in an orthonormal basis of the actual column image. -/
def imageCoordinates {k n : ℕ} (A : E k →ₗ[ℝ] E n)
    (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) : E k →ₗ[ℝ] E k :=
  b.repr.toLinearEquiv.toLinearMap.comp A.rangeRestrict

/-- Euclidean k-volume in an orthonormal image frame, using the shared Riemann volume. -/
def flatVolume {k n : ℕ} (P : Submodule ℝ (E n))
    (b : OrthonormalBasis (Fin k) ℝ P) (S : Set P) : ℝ :=
  Specs.D04.C06.JordanRegions.Model.volume (b.repr '' S)

/-- The unit parameter cube, including the singleton cube in dimension zero. -/
def unitCube (k : ℕ) : Set (E k) := {u | ∀ i, 0 ≤ u i ∧ u i ≤ 1}

/-- Flat volume in the affine image plane, centered at c. -/
def flatAffineVolume {k n : ℕ} (A : E k →ₗ[ℝ] E n)
    (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) (c : E n)
    (S : Set (E n)) : ℝ :=
  flatVolume A.range b ((fun v : A.range => c + (v : E n)) ⁻¹' S)

end Model
open Model

abbrev RegularPatchType := {k n : ℕ} → Set (E k) → (E k → E n) → Prop
def RegularPatchValue : RegularPatchType := @Model.RegularPatch

abbrev EmbeddedPatchType := {k n : ℕ} → Set (E k) → (E k → E n) → Prop
def EmbeddedPatchValue : EmbeddedPatchType := @Model.EmbeddedPatch

abbrev tangentPlaneType := {k n : ℕ} → (E k → E n) → E k → Submodule ℝ (E n)
def tangentPlaneValue : tangentPlaneType := @Model.tangentPlane

abbrev columnsType := {k n : ℕ} → (E k →ₗ[ℝ] E n) → Fin k → E n
def columnsValue : columnsType := @Model.columns

abbrev gramMatrixType := {k n : ℕ} → (E k →ₗ[ℝ] E n) → Matrix (Fin k) (Fin k) ℝ
def gramMatrixValue : gramMatrixType := @Model.gramMatrix

abbrev gramFactorType := {k n : ℕ} → (E k →ₗ[ℝ] E n) → ℝ
def gramFactorValue : gramFactorType := @Model.gramFactor

abbrev patchGramType := {k n : ℕ} → (E k → E n) → E k → Matrix (Fin k) (Fin k) ℝ
def patchGramValue : patchGramType := @Model.patchGram

abbrev patchJacobianType := {k n : ℕ} → (E k → E n) → E k → ℝ
def patchJacobianValue : patchJacobianType := @Model.patchJacobian

abbrev crossType := E 3 → E 3 → E 3
def crossValue : crossType := @Model.cross

abbrev unitNormalType := (E 2 → E 3) → E 2 → E 3
def unitNormalValue : unitNormalType := @Model.unitNormal

abbrev IsUnitNormalType := Submodule ℝ (E 3) → E 3 → Prop
def IsUnitNormalValue : IsUnitNormalType := @Model.IsUnitNormal

abbrev imageCoordinatesType := {k n : ℕ} → (A : E k →ₗ[ℝ] E n) → OrthonormalBasis (Fin k) ℝ (LinearMap.range A) → (E k →ₗ[ℝ] E k)
def imageCoordinatesValue : imageCoordinatesType := @Model.imageCoordinates

abbrev flatVolumeType := {k n : ℕ} → (P : Submodule ℝ (E n)) → OrthonormalBasis (Fin k) ℝ P → Set P → ℝ
def flatVolumeValue : flatVolumeType := @Model.flatVolume

def regular_rankType : Prop :=
  ∀ {k n : ℕ} {U : Set (E k)} {φ : E k → E n},
  RegularPatch U φ ↔ IsOpen U ∧ ContDiffOn ℝ 1 φ U ∧
    ∀ x ∈ U, Module.finrank ℝ (tangentPlane φ x) = k

def columns_independentType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n),
  LinearIndependent ℝ (columns A) ↔ Function.Injective A

def gram_entriesType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n),
  gramMatrix A = Matrix.gram ℝ (columns A)

def gram_positiveType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n),
  Function.Injective A → 0 < gramFactor A

def cross_independentType : Prop :=
  ∀ a b : E 3, cross a b ≠ 0 ↔ LinearIndependent ℝ ![a, b]

def cross_rankType : Prop :=
  ∀ (A : E 2 →ₗ[ℝ] E 3),
  cross (columns A 0) (columns A 1) ≠ 0 ↔ Function.Injective A

def normal_choicesType : Prop :=
  ∀ {U : Set (E 2)} {φ : E 2 → E 3}, RegularPatch U φ →
  ∀ x ∈ U, ∀ v : E 3, IsUnitNormal (tangentPlane φ x) v ↔
    v = unitNormal φ x ∨ v = -unitNormal φ x

def gram_twoType : Prop :=
  ∀ {n : ℕ} (A : E 2 →ₗ[ℝ] E n),
  gramFactor A = Real.sqrt (‖columns A 0‖ ^ 2 * ‖columns A 1‖ ^ 2 -
    ⟪columns A 0, columns A 1⟫ ^ 2)

def gram_crossType : Prop :=
  ∀ (A : E 2 →ₗ[ℝ] E 3),
  gramFactor A = ‖cross (columns A 0) (columns A 1)‖

def image_basis_existsType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n), Function.Injective A →
  Nonempty (OrthonormalBasis (Fin k) ℝ (LinearMap.range A))

def gram_image_coordinatesType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)),
  gramMatrix A = (matrixOfLinearMap (imageCoordinates A b)).transpose *
    matrixOfLinearMap (imageCoordinates A b)

def gram_image_factorType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)),
  gramFactor A = |(imageCoordinates A b).det|

def image_basis_independentType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b c : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)),
  |(imageCoordinates A b).det| = |(imageCoordinates A c).det|

def flat_volume_scalingType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A))
  (S : Set (E k)), Specs.D04.C06.JordanRegions.Model.Jordan S →
  Specs.D04.C06.JordanRegions.Model.Jordan (b.repr '' (A.rangeRestrict '' S)) ∧
  flatVolume (LinearMap.range A) b (A.rangeRestrict '' S) =
    gramFactor A * Specs.D04.C06.JordanRegions.Model.volume S

def affine_jacobianType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n) (c : E n) (x : E k),
  patchJacobian (fun u => c + A u) x = gramFactor A

def gram_oneType : Prop :=
  ∀ {n : ℕ} (A : E 1 →ₗ[ℝ] E n), gramFactor A = ‖columns A 0‖

def gram_topType : Prop :=
  ∀ {n : ℕ} (A : E n →ₗ[ℝ] E n), gramFactor A = |A.det|

def gram_zeroType : Prop :=
  ∀ {n : ℕ} (A : E 0 →ₗ[ℝ] E n), gramFactor A = 1

abbrev unitCubeType := (k : ℕ) → Set (E k)
def unitCubeValue : unitCubeType := @Model.unitCube

abbrev flatAffineVolumeType := {k n : ℕ} → (A : E k →ₗ[ℝ] E n) → OrthonormalBasis (Fin k) ℝ (LinearMap.range A) → E n → Set (E n) → ℝ
def flatAffineVolumeValue : flatAffineVolumeType := @Model.flatAffineVolume

def unitCube_volumeType : Prop :=
  ∀ k : ℕ, Specs.D04.C06.JordanRegions.Model.Jordan (unitCube k) ∧
  Specs.D04.C06.JordanRegions.Model.volume (unitCube k) = 1

def flat_parallelepipedType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) (c : E n),
  flatAffineVolume A b c ((fun u => c + A u) '' unitCube k) = gramFactor A

def flat_parallelepiped_independentType : Prop :=
  ∀ {k n : ℕ} (A : E k →ₗ[ℝ] E n)
  (b d : OrthonormalBasis (Fin k) ℝ (LinearMap.range A)) (c : E n),
  flatAffineVolume A b c ((fun u => c + A u) '' unitCube k) =
    flatAffineVolume A d c ((fun u => c + A u) '' unitCube k)

end Specs.D04.C10.PatchGeometryGram
