import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.OrthogonalCoordinateOperators
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C07.CoordinateCharts

/-! Paper d04:11:coordinates. All derivatives on the right are in parameter
coordinates; physical components use the normalized derivative columns.
An arbitrary open subdomain of one angular branch is allowed. In particular
this includes every open angle interval shorter than 2π without requiring
field regularity outside its image. The spherical order is (r,θ,φ). -/
noncomputable section
open Set
namespace Specs.D04.C11.CylindricalSphericalOperators
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
open Specs.D04.C11.OrthogonalCoordinateOperators.Model
open Specs.D04.C07.CoordinateCharts.Model

def cylindrical_factorsType : Prop :=
  ∀ u : E 3, 0 < u 0 → scaleFactor cylindrical u = ![1, u 0, 1]

def spherical_factorsType : Prop :=
  ∀ u : E 3, 0 < u 0 → 0 < u 1 → u 1 < Real.pi →
    scaleFactor spherical u = ![1, u 0, u 0 * Real.sin (u 1)]

def cylindrical_divergenceType : Prop :=
  ∀ (α : ℝ) (U : Set (E 3)), IsOpen U → U ⊆ cylindricalDomain α →
  ∀ (F : E 3 → E 3), CrOn 1 (cylindrical '' U) F → ∀ u ∈ U,
    divergence F (cylindrical u) =
      (u 0)⁻¹ * scalarPartialDerivative (fun v => v 0 * physicalComponent cylindrical F v 0) u 0 +
      (u 0)⁻¹ * scalarPartialDerivative (fun v => physicalComponent cylindrical F v 1) u 1 +
      scalarPartialDerivative (fun v => physicalComponent cylindrical F v 2) u 2

def cylindrical_laplacianType : Prop :=
  ∀ (α : ℝ) (U : Set (E 3)), IsOpen U → U ⊆ cylindricalDomain α →
  ∀ (f : E 3 → ℝ), CrOn 2 (cylindrical '' U) f → ∀ u ∈ U,
    laplacian f (cylindrical u) =
      (u 0)⁻¹ * scalarPartialDerivative
        (fun v => v 0 * scalarPartialDerivative (f ∘ cylindrical) v 0) u 0 +
      ((u 0)^2)⁻¹ * scalarPartialDerivative
        (fun v => scalarPartialDerivative (f ∘ cylindrical) v 1) u 1 +
      scalarPartialDerivative (fun v => scalarPartialDerivative (f ∘ cylindrical) v 2) u 2

def spherical_divergenceType : Prop :=
  ∀ (α : ℝ) (U : Set (E 3)), IsOpen U → U ⊆ sphericalDomain α →
  ∀ (F : E 3 → E 3), CrOn 1 (spherical '' U) F → ∀ u ∈ U,
    divergence F (spherical u) =
      ((u 0)^2)⁻¹ * scalarPartialDerivative
        (fun v => (v 0)^2 * physicalComponent spherical F v 0) u 0 +
      (u 0 * Real.sin (u 1))⁻¹ * scalarPartialDerivative
        (fun v => Real.sin (v 1) * physicalComponent spherical F v 1) u 1 +
      (u 0 * Real.sin (u 1))⁻¹ * scalarPartialDerivative
        (fun v => physicalComponent spherical F v 2) u 2

def spherical_laplacianType : Prop :=
  ∀ (α : ℝ) (U : Set (E 3)), IsOpen U → U ⊆ sphericalDomain α →
  ∀ (f : E 3 → ℝ), CrOn 2 (spherical '' U) f → ∀ u ∈ U,
    laplacian f (spherical u) =
      ((u 0)^2)⁻¹ * scalarPartialDerivative
        (fun v => (v 0)^2 * scalarPartialDerivative (f ∘ spherical) v 0) u 0 +
      ((u 0)^2 * Real.sin (u 1))⁻¹ * scalarPartialDerivative
        (fun v => Real.sin (v 1) * scalarPartialDerivative (f ∘ spherical) v 1) u 1 +
      ((u 0)^2 * (Real.sin (u 1))^2)⁻¹ * scalarPartialDerivative
        (fun v => scalarPartialDerivative (f ∘ spherical) v 2) u 2

end Specs.D04.C11.CylindricalSphericalOperators
