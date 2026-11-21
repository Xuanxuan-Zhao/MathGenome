import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C11.EuclideanVectorOperators

/-! Independent statement of d04:11:orthogonal. Ambient functions represent
restrictions to the two open domains. Indices 0,1,2 represent u₁,u₂,u₃.
The inverse is required only on the stated domains, with exactly C² regularity. -/
noncomputable section
open Set
open scoped BigOperators
namespace Specs.D04.C11.OrthogonalCoordinateOperators
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C02.DerivativeInterfaces.Model
open Specs.D04.C02.DerivativeBridge.Model
open Specs.D04.C11.EuclideanVectorOperators.Model
namespace Model

def coordinateColumn (φ : E 3 → E 3) (u : E 3) (i : Fin 3) : E 3 :=
  totalDerivative φ u (standardBasis 3 i)

def scaleFactor (φ : E 3 → E 3) (u : E 3) (i : Fin 3) : ℝ :=
  ‖coordinateColumn φ u i‖

def unitVector (φ : E 3 → E 3) (u : E 3) (i : Fin 3) : E 3 :=
  (scaleFactor φ u i)⁻¹ • coordinateColumn φ u i

def volumeFactor (φ : E 3 → E 3) (u : E 3) : ℝ :=
  ∏ i : Fin 3, scaleFactor φ u i

def physicalComponent (φ F : E 3 → E 3) (u : E 3) (i : Fin 3) : ℝ :=
  inner ℝ (F (φ u)) (unitVector φ u i)

/-- The three positively cyclic index triples. -/
def CyclicTriple (i j l : Fin 3) : Prop :=
  (i = 0 ∧ j = 1 ∧ l = 2) ∨ (i = 1 ∧ j = 2 ∧ l = 0) ∨
    (i = 2 ∧ j = 0 ∧ l = 1)

structure OrthogonalChart (U V : Set (E 3)) (φ : E 3 → E 3) : Prop where
  open_source : IsOpen U
  open_target : IsOpen V
  maps_to : MapsTo φ U V
  regularity : CrOn 2 U φ
  inverse : ∃ ψ : E 3 → E 3, MapsTo ψ V U ∧ LeftInvOn ψ φ U ∧
    RightInvOn ψ φ V ∧ CrOn 2 V ψ
  positive : ∀ u ∈ U, 0 < Matrix.det (jacobian φ u)
  orthogonal : ∀ u ∈ U, Pairwise (fun i j =>
    inner ℝ (coordinateColumn φ u i) (coordinateColumn φ u j) = 0)
  nonzero : ∀ u ∈ U, ∀ i, coordinateColumn φ u i ≠ 0

end Model
open Model

def orthogonal_gradientType : Prop :=
  ∀ (U V : Set (E 3)) (φ : E 3 → E 3), OrthogonalChart U V φ →
  ∀ (f : E 3 → ℝ), CrOn 1 V f → ∀ u ∈ U,
    scalarGradient f (φ u) = ∑ i : Fin 3,
      (scalarPartialDerivative (f ∘ φ) u i / scaleFactor φ u i) • unitVector φ u i

def orthogonal_divergenceType : Prop :=
  ∀ (U V : Set (E 3)) (φ : E 3 → E 3), OrthogonalChart U V φ →
  ∀ (F : E 3 → E 3), CrOn 1 V F → ∀ u ∈ U,
    divergence F (φ u) = (volumeFactor φ u)⁻¹ * ∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor φ v / scaleFactor φ v i *
        physicalComponent φ F v i) u i

def orthogonal_curlType : Prop :=
  ∀ (U V : Set (E 3)) (φ : E 3 → E 3), OrthogonalChart U V φ →
  ∀ (F : E 3 → E 3), CrOn 1 V F → ∀ u ∈ U,
  ∀ i j l : Fin 3, CyclicTriple i j l →
    inner ℝ (curl F (φ u)) (unitVector φ u i) =
      (scalarPartialDerivative (fun v => scaleFactor φ v l * physicalComponent φ F v l) u j -
        scalarPartialDerivative (fun v => scaleFactor φ v j * physicalComponent φ F v j) u l) /
          (scaleFactor φ u j * scaleFactor φ u l)

def orthogonal_laplacianType : Prop :=
  ∀ (U V : Set (E 3)) (φ : E 3 → E 3), OrthogonalChart U V φ →
  ∀ (f : E 3 → ℝ), CrOn 2 V f → ∀ u ∈ U,
    laplacian f (φ u) = (volumeFactor φ u)⁻¹ * ∑ i : Fin 3,
      scalarPartialDerivative (fun v => volumeFactor φ v / (scaleFactor φ v i)^2 *
        scalarPartialDerivative (f ∘ φ) v i) u i

end Specs.D04.C11.OrthogonalCoordinateOperators
