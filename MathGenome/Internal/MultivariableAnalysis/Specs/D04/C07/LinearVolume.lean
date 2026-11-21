import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.RegionSubstitution
import Mathlib.LinearAlgebra.Determinant

/-! Linear volume scaling (`d04:07:linear-volume`). These statements use
exactly the shared bounded-region Riemann integral, including dimension zero.
The singular assertion does not assume the image to be Jordan measurable. -/
noncomputable section
open Set
namespace Specs.D04.C07.LinearVolume
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C06.JordanRegions.Model
open Specs.D04.C06.NullCovers.Model

def singular_imageType : Prop :=
  ∀ {n : ℕ} (A : E n →ₗ[ℝ] E n), A.det = 0 →
    ∀ S : Set (E n), Bornology.IsBounded S →
      Bornology.IsBounded (closure (A '' S)) ∧
      closure (A '' S) ⊆ (LinearMap.range A : Set (E n)) ∧
      LinearMap.range A ≠ ⊤ ∧ ContentZero (closure (A '' S)) ∧
      (Jordan (closure (A '' S)) ∧ volume (closure (A '' S)) = 0) ∧
      Jordan (A '' S) ∧ volume (A '' S) = 0

def linear_volumeType : Prop :=
  ∀ {n : ℕ} (A : E n →ₗ[ℝ] E n) (S : Set (E n)), Jordan S →
    Jordan (A '' S) ∧ volume (A '' S) = |A.det| * volume S

/-- Ordinary substitution in any invertible linear coordinates. The
unweighted pullback is itself Riemann integrable in exactly the same cases. -/
def linear_substitutionType : Prop :=
  ∀ {n : ℕ} (A : E n ≃ₗ[ℝ] E n) (S : Set (E n)), Jordan S →
    ∀ f : (A '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x => f ⟨A x, mem_image_of_mem A x.property⟩
      RegionBounded g ∧ (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) →
          regionIntegral f = |(A : E n →ₗ[ℝ] E n).det| * regionIntegral g)

def basis_determinantType : Prop :=
  ∀ {n : ℕ} (b : Module.Basis (Fin n) ℝ (E n)),
    let A : E n ≃ₗ[ℝ] E n := (coordinates n).trans b.equivFun.symm
    (A : E n →ₗ[ℝ] E n).det = Matrix.det (fun i j => b j i)

/-- The coordinate map takes a Euclidean coordinate column to the linear
combination of an arbitrary basis with that column's coefficients. -/
def basis_substitutionType : Prop :=
  ∀ {n : ℕ} (b : Module.Basis (Fin n) ℝ (E n)) (S : Set (E n)), Jordan S →
    let A : E n ≃ₗ[ℝ] E n := (coordinates n).trans b.equivFun.symm
    (∀ u : E n, A u = ∑ i, u i • b i) ∧
    Jordan (A '' S) ∧ volume (A '' S) = |(A : E n →ₗ[ℝ] E n).det| * volume S ∧
    ∀ f : (A '' S) → ℝ, RegionBounded f →
      let g : S → ℝ := fun x => f ⟨A x, mem_image_of_mem A x.property⟩
      (RegionIntegrable f ↔ RegionIntegrable g) ∧
        ((RegionIntegrable f ∨ RegionIntegrable g) →
          regionIntegral f = |(A : E n →ₗ[ℝ] E n).det| * regionIntegral g)

def zero_dimensionType : Prop :=
  (∀ A : E 0 →ₗ[ℝ] E 0, A.det = 1 ∧
    ∀ S : Set (E 0), volume (A '' S) = volume S) ∧
    volume (univ : Set (E 0)) = 1
end Specs.D04.C07.LinearVolume
