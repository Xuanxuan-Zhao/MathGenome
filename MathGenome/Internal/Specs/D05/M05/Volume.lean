import MathGenome.Internal.Specs.D05.M05.Orientation
import MathGenome.Internal.Specs.D05.M12.OnBasis
import MathGenome.Internal.Specs.D05.Foundations.VolumeChange
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! K05.05.volume, paper.tex:908–911.

The reference basis records the orientation; independence means independence
among orthonormal bases in the same upstream orientation class. Columns are
`b.toMatrix v`, so the original, column Leibniz determinant is used verbatim.
The algebraic definitions make sense for every real basis. For geometric
interpretation the reference basis is orthonormal. Complete Lebesgue measure
is expressed in those coordinates, using the upstream coordinate space and
its completed product Lebesgue measure. There is no positive-dimension or
finite-measure premise. Singular images have a separate nullity statement.
-/
noncomputable section
open MeasureTheory Set

namespace Specs.D05.M05.Volume
open _root_.D05.M05 _root_.D05.VolumeElementary
open Specs.D05.M04.ChangeBasis Specs.D05.M05.Orientation
universe u

def signedVolume_type : Type (u + 1) :=
  {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n : ℕ} →
    Module.Basis (Fin n) ℝ V → (Fin n → V) → ℝ

def signedVolume_value : signedVolume_type.{u} :=
  fun b v => determinant (b.toMatrix v)

def ordinaryVolume_type : Type (u + 1) := signedVolume_type.{u}
def ordinaryVolume_value : ordinaryVolume_type.{u} :=
  fun b v => |signedVolume_value b v|

def unitCube_type := (n : ℕ) → Set (CoordinateSpace n)
def unitCube_value : unitCube_type := fun n => Icc 0 1

def parallelepiped_type : Type (u + 1) :=
  {V : Type u} → [AddCommGroup V] → [Module ℝ V] → {n : ℕ} →
    (Fin n → V) → Set V

def parallelepiped_value : parallelepiped_type.{u} :=
  fun v => (fun t => ∑ j, t j • v j) '' unitCube_value _

/-- Rows are coordinate indices; columns retain the order of the vectors. -/
def coordinate_columns : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (v : Fin n → V) (i j : Fin n),
    b.toMatrix v i j = b.repr (v j) i

def signedVolume_eq_basis_det : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (v : Fin n → V),
    signedVolume_value b v = b.det v

/-- Coordinate conversion is orthogonal, proved from orthonormality. -/
def conversion_orthogonal : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
    _root_.D05.orthonormalFamily (F := ℝ) c →
    (changeMatrix_value b c).transpose * changeMatrix_value b c = 1

def conversion_det_sq : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
    _root_.D05.orthonormalFamily (F := ℝ) c →
    (determinant (changeMatrix_value b c)) ^ 2 = 1

def oriented_conversion_det_one : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
    _root_.D05.orthonormalFamily (F := ℝ) c →
    sameOrientation_value b c → determinant (changeMatrix_value b c) = 1

/-- Determinant one for the conversion, together with its action on arbitrary
column families, proves reference independence even for dependent vectors. -/
def signedVolume_basis_independent : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
    _root_.D05.orthonormalFamily (F := ℝ) c → sameOrientation_value b c →
    ∀ v : Fin n → V, signedVolume_value b v = signedVolume_value c v

/-- Ordinary volume is independent even of the reference orientation. -/
def ordinaryVolume_basis_independent : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b c : Module.Basis (Fin n) ℝ V),
    _root_.D05.orthonormalFamily (F := ℝ) b →
    _root_.D05.orthonormalFamily (F := ℝ) c →
    ∀ v : Fin n → V, ordinaryVolume_value b v = ordinaryVolume_value c v

def columns_linear_image : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V →ₗ[ℝ] V) (v : Fin n → V),
    b.toMatrix (T ∘ v) = LinearMap.toMatrix b b T * b.toMatrix v

/-- No invertibility hypothesis: singular linear maps collapse volume. -/
def signedVolume_linear_image : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V →ₗ[ℝ] V) (v : Fin n → V),
    signedVolume_value b (T ∘ v) = LinearMap.det T * signedVolume_value b v

def ordinaryVolume_linear_image : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (T : V →ₗ[ℝ] V) (v : Fin n → V),
    ordinaryVolume_value b (T ∘ v) = |LinearMap.det T| * ordinaryVolume_value b v

def unitCube_measure : Prop := ∀ n : ℕ,
  MeasurableSet (unitCube_value n) ∧
    (volume : Measure (CoordinateSpace n)).completion (unitCube_value n) = 1

/-- The actual parallelepiped in V, not just a formal matrix, is the image
of the cube, and taking coordinates gives precisely matrix multiplication. -/
def parallelepiped_coordinates : Prop :=
  ∀ {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V) (v : Fin n → V),
    b.equivFun '' parallelepiped_value v = (b.toMatrix v).mulVec '' unitCube_value n

/-- Complete Lebesgue volume in orthonormal coordinates agrees with the
absolute determinant, including singular parallelepipeds and n = 0. -/
def parallelepiped_measure : Prop :=
  ∀ {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] {n : ℕ}
    (b : Module.Basis (Fin n) ℝ V), _root_.D05.orthonormalFamily (F := ℝ) b →
    ∀ v : Fin n → V,
    NullMeasurableSet (b.equivFun '' parallelepiped_value v)
      (volume : Measure (CoordinateSpace n)) ∧
    (volume : Measure (CoordinateSpace n)).completion
      (b.equivFun '' parallelepiped_value v) = ENNReal.ofReal (ordinaryVolume_value b v)

/-- Invertible coordinate maps act on every complete-measurable set,
including sets of infinite measure. -/
def invertible_measure_scaling : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), IsUnit A →
    ∀ E : Set (CoordinateSpace n), NullMeasurableSet E (volume : Measure (CoordinateSpace n)) →
    NullMeasurableSet (A.mulVec '' E) (volume : Measure (CoordinateSpace n)) ∧
    (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) =
      ENNReal.ofReal |A.det| * (volume : Measure (CoordinateSpace n)).completion E

/-- A singular image lies in a proper null subspace; no measurability
assumption on the input set and no expression involving 0 times infinity. -/
def singular_null_image : Prop := ∀ (n : ℕ)
    (A : Matrix (Fin n) (Fin n) ℝ), A.det = 0 → ∀ E : Set (CoordinateSpace n),
    ∃ U : Submodule ℝ (CoordinateSpace n),
      U ≠ ⊤ ∧ A.mulVec '' E ⊆ (U : Set (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (U : Set (CoordinateSpace n)) = 0 ∧
      NullMeasurableSet (A.mulVec '' E) (volume : Measure (CoordinateSpace n)) ∧
      (volume : Measure (CoordinateSpace n)).completion (A.mulVec '' E) = 0

/-- The algebraic and measure normalizations agree in dimension zero. -/
def empty_volumes : Prop :=
  (∀ {V : Type*} [AddCommGroup V] [Module ℝ V]
    (b : Module.Basis (Fin 0) ℝ V) (v : Fin 0 → V),
    signedVolume_value b v = 1 ∧ ordinaryVolume_value b v = 1) ∧
  (∀ x : CoordinateSpace 0,
    (volume : Measure (CoordinateSpace 0)).completion ({x} : Set (CoordinateSpace 0)) = 1)

end Specs.D05.M05.Volume
