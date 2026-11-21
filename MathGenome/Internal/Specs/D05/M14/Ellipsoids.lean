import MathGenome.Internal.Specs.D05.M14.Svd
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Independent statements of K05.14.ellipsoids, paper.tex:2628–2646.
An invertible endomorphism is represented by a linear equivalence. The axes
are real positive lengths over both scalar fields. Complete real Lebesgue
measure is used only on real spaces, with its canonical orthonormal
normalization. No positive dimension or nonempty index assumption is made.
-/

noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace D05.Ellipsoids
variable {F V : Type*} [RCLike F] [NormedAddCommGroup V] [InnerProductSpace F V]

/-- The principal-axis quadratic expression in actual orthonormal coordinates. -/
def energy {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ) (v : V) : ℝ :=
  ∑ i, ‖b.repr v i‖ ^ 2 / a i ^ 2

def closedEllipsoid {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) : Set V := {v | energy b a v ≤ 1}

def openEllipsoid {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
    (a : Fin n → ℝ) : Set V := {v | energy b a v < 1}
end D05.Ellipsoids

namespace Specs.D05.M14.Ellipsoids
universe u v
open _root_.D05.Ellipsoids

/-- Bridge to the two displayed sum-of-generators sets in the paper. -/
def coordinate_description : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ),
    closedEllipsoid b a = {v | ∃ y : Fin n → F,
      v = ∑ i, y i • b i ∧ (∑ i, ‖y i‖ ^ 2 / a i ^ 2) ≤ 1} ∧
    openEllipsoid b a = {v | ∃ y : Fin n → F,
      v = ∑ i, y i • b i ∧ (∑ i, ‖y i‖ ^ 2 / a i ^ 2) < 1}

def positive_axes : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V) (i : Fin (Module.finrank F V)),
      0 < T.toLinearMap.singularValues i

/-- Both equalities for any full SVD, with no decomposition premise on existence below. -/
def svd_ball_images : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V) (d : _root_.D05.SingularValueDecomposition T.toLinearMap),
      T '' {v : V | ‖v‖ ≤ 1} = closedEllipsoid d.codomainBasis
        (fun i => T.toLinearMap.singularValues i) ∧
      T '' {v : V | ‖v‖ < 1} = openEllipsoid d.codomainBasis
        (fun i => T.toLinearMap.singularValues i)

def exists_ball_images : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V),
      ∃ d : _root_.D05.SingularValueDecomposition T.toLinearMap,
      (∀ i : Fin (Module.finrank F V), 0 < T.toLinearMap.singularValues i) ∧
      T '' {v : V | ‖v‖ ≤ 1} = closedEllipsoid d.codomainBasis
        (fun i => T.toLinearMap.singularValues i) ∧
      T '' {v : V | ‖v‖ < 1} = openEllipsoid d.codomainBasis
        (fun i => T.toLinearMap.singularValues i)

/-- The original endomorphism formulation, with invertibility as bijectivity. -/
def bijective_ball_images : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V →ₗ[F] V), Function.Bijective T →
      ∃ d : _root_.D05.SingularValueDecomposition T,
      (∀ i : Fin (Module.finrank F V), 0 < T.singularValues i) ∧
      T '' {v : V | ‖v‖ ≤ 1} = closedEllipsoid d.codomainBasis
        (fun i => T.singularValues i) ∧
      T '' {v : V | ‖v‖ < 1} = openEllipsoid d.codomainBasis
        (fun i => T.singularValues i)

def diagonal_realization : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ),
      (∀ i, 0 < a i) → ∃ S : V ≃ₗ[F] V,
      (∀ i, S (b i) = (a i : F) • b i) ∧
      S '' {v : V | ‖v‖ ≤ 1} = closedEllipsoid b a ∧
      S '' {v : V | ‖v‖ < 1} = openEllipsoid b a

/-- The same principal axes and lengths serve both the open and closed images. -/
def image_ellipsoid : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V) {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
      (a : Fin n → ℝ), (∀ i, 0 < a i) →
      ∃ (f : OrthonormalBasis (Fin (Module.finrank F V)) F V)
        (s : Fin (Module.finrank F V) → ℝ),
      (∀ i, 0 < s i) ∧ T '' closedEllipsoid b a = closedEllipsoid f s ∧
      T '' openEllipsoid b a = openEllipsoid f s

def translated_image : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V) (c : V) (E : Set V),
      T '' ((fun v => c + v) '' E) = (fun v => T c + v) '' (T '' E)

def translated_ellipsoid : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ (T : V ≃ₗ[F] V) (c : V) {n : ℕ}
      (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ), (∀ i, 0 < a i) →
      ∃ (f : OrthonormalBasis (Fin (Module.finrank F V)) F V)
        (s : Fin (Module.finrank F V) → ℝ), (∀ i, 0 < s i) ∧
      T '' ((fun v => c + v) '' closedEllipsoid b a) =
        (fun v => T c + v) '' closedEllipsoid f s ∧
      T '' ((fun v => c + v) '' openEllipsoid b a) =
        (fun v => T c + v) '' openEllipsoid f s

/-- Real semiaxis endpoints and complex coordinate disks, including the strict boundary. -/
def axis_sections : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) F V)
      (a : Fin n → ℝ), (∀ i, 0 < a i) → ∀ (i : Fin n) (z : F),
      (z • b i ∈ closedEllipsoid b a ↔ ‖z‖ ≤ a i) ∧
      (z • b i ∈ openEllipsoid b a ↔ ‖z‖ < a i)

def ellipsoid_topology : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    ∀ {n : ℕ} (b : OrthonormalBasis (Fin n) F V) (a : Fin n → ℝ),
      IsClosed (closedEllipsoid b a) ∧ IsOpen (openEllipsoid b a)

/-- Complete real volume and the determinant bridge; arbitrary measurable sets are allowed. -/
def real_volume_scaling : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    ∀ (T : V ≃ₗ[ℝ] V) (E : Set V),
      NullMeasurableSet E (volume : Measure V) →
      NullMeasurableSet (T '' E) (volume : Measure V) ∧
      (volume : Measure V).completion (T '' E) =
        ENNReal.ofReal (_root_.D05.singularValues T.toLinearMap).prod *
          (volume : Measure V).completion E ∧
      (_root_.D05.singularValues T.toLinearMap).prod = |T.toLinearMap.det|

def real_ball_volumes : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    ∀ (T : V ≃ₗ[ℝ] V),
      MeasurableSet ({v : V | ‖v‖ ≤ 1}) ∧ MeasurableSet ({v : V | ‖v‖ < 1}) ∧
      MeasurableSet (T '' {v : V | ‖v‖ ≤ 1}) ∧
      MeasurableSet (T '' {v : V | ‖v‖ < 1}) ∧
      (volume : Measure V).completion (T '' {v : V | ‖v‖ ≤ 1}) =
        ENNReal.ofReal (_root_.D05.singularValues T.toLinearMap).prod *
          (volume : Measure V).completion {v : V | ‖v‖ ≤ 1} ∧
      (volume : Measure V).completion (T '' {v : V | ‖v‖ < 1}) =
        ENNReal.ofReal (_root_.D05.singularValues T.toLinearMap).prod *
          (volume : Measure V).completion {v : V | ‖v‖ < 1}

def zero_dimension : Prop :=
  ∀ {F : Type u} {V : Type v} [RCLike F] [NormedAddCommGroup V]
    [InnerProductSpace F V] [FiniteDimensional F V],
    Module.finrank F V = 0 → ∀ (T : V ≃ₗ[F] V)
      (b : OrthonormalBasis (Fin (Module.finrank F V)) F V)
      (a : Fin (Module.finrank F V) → ℝ),
      {v : V | ‖v‖ ≤ 1} = {0} ∧ {v : V | ‖v‖ < 1} = {0} ∧
      closedEllipsoid b a = {0} ∧ openEllipsoid b a = {0} ∧
      (_root_.D05.singularValues T.toLinearMap).prod = 1

def zero_real_volume : Prop :=
  ∀ {V : Type v} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V],
    Module.finrank ℝ V = 0 →
      (volume : Measure V).completion ({0} : Set V) = 1 ∧
      (volume : Measure V).completion {v : V | ‖v‖ ≤ 1} = 1 ∧
      (volume : Measure V).completion {v : V | ‖v‖ < 1} = 1

end Specs.D05.M14.Ellipsoids
