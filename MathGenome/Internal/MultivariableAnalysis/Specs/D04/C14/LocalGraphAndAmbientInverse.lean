import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C14.EmbeddedManifoldCharts
import MathGenome.Internal.MultivariableAnalysis.Specs.D04.C04.InverseFunction
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-! Local graph assertion in d04:14:charts. The graph is expressed without
reordering the unselected coordinates: `x = g (q (P x))`, with `P (g (q v)) = v`.
Thus each unselected coordinate is a C^r function of the selected coordinates.
The projected domain is explicitly `Y ∩ q ⁻¹' V`; at a half-space point it
need not itself be a coordinate half-space. No transition theorem is assumed. -/
noncomputable section
open Set
open scoped ContDiff
namespace Specs.D04.C14.LocalGraphAndAmbientInverse
open Specs.D04.C01.EuclideanInterfaces.Model
open Specs.D04.C14.EmbeddedManifoldCharts.Model
open Specs.D04.C04.InverseFunction
namespace Model

/-- Select k distinct ambient coordinates, in their chosen order. -/
def coordinateProjection {k n : ℕ} (s : Fin k ↪ Fin n) : E n →L[ℝ] E k :=
  LinearMap.toContinuousLinearMap
    { toFun := fun x => WithLp.toLp 2 (fun i => x (s i))
      map_add' := by intro x y; rfl
      map_smul' := by intro c x; rfl }

/-- The Euclidean inverse theorem is applied to the extension, before
restriction to the original (possibly half-space) domain. -/
structure LocalGraphWitness (r : ℕ∞ω) {k n : ℕ} (V : Set (E k))
    (φ : E k → E n) (u : E k) (s : Fin k ↪ Fin n)
    (W : Set (E k)) (g : E k → E n) (X Y : Set (E k)) (q : E k → E k) : Prop where
  extension_open : IsOpen W
  extension_center : u ∈ W
  extension_agrees : EqOn g φ (V ∩ W)
  extension_regular : ContDiffOn ℝ r g W
  inverse : InverseNeighborhood W (coordinateProjection s ∘ g) u X Y q
  inverse_regular : ContDiffOn ℝ r q Y
  graph_regular : ContDiffOn ℝ r (g ∘ q) Y
  graph_coordinates : EqOn (coordinateProjection s ∘ (g ∘ q)) id Y
  projected_domain : (coordinateProjection s ∘ φ) '' (V ∩ X) = Y ∩ q ⁻¹' V
  graph_image : φ '' (V ∩ X) =
    {x | coordinateProjection s x ∈ (coordinateProjection s ∘ φ) '' (V ∩ X) ∧
      x = g (q (coordinateProjection s x))}
  inverse_ambient_regular : ContDiffOn ℝ r (q ∘ coordinateProjection s)
    (coordinateProjection s ⁻¹' Y)
  inverse_maps : MapsTo (q ∘ coordinateProjection s) (φ '' (V ∩ X)) (V ∩ X)
  inverse_left : LeftInvOn (q ∘ coordinateProjection s) φ (V ∩ X)
  inverse_right : RightInvOn (q ∘ coordinateProjection s) φ (φ '' (V ∩ X))

end Model
open Model

abbrev coordinateProjectionType := {k n : ℕ} → (Fin k ↪ Fin n) → E n →L[ℝ] E k
def coordinateProjectionValue : coordinateProjectionType := @Model.coordinateProjection

def independent_coordinate_projectionType : Prop :=
  ∀ {k n : ℕ} (A : E k →L[ℝ] E n), Function.Injective A →
    ∃ (s : Fin k ↪ Fin n) (B : E k ≃L[ℝ] E k),
      B.toContinuousLinearMap = (coordinateProjection s).comp A

def local_graph_and_ambient_inverseType : Prop :=
  ∀ {r : ℕ∞ω} {k n : ℕ} (V : Set (E k)) (φ : E k → E n) (u : E k)
    (half : Bool), ManifoldRegularity r → k ≤ n →
    (half = true → 0 < k) →
    (∃ O : Set (E k), IsOpen O ∧ V = parameterSpace k half ∩ O) →
    FullRankLocalExtension r V φ → u ∈ V →
    ∃ (s : Fin k ↪ Fin n) (W : Set (E k)) (g : E k → E n)
      (X Y : Set (E k)) (q : E k → E k), LocalGraphWitness r V φ u s W g X Y q

/-- Dimension zero is evaluation at the unique parameter point, with an
empty-coordinate projection and a constant inverse. -/
def zero_parameter_graphType : Prop :=
  ∀ {n : ℕ} (V : Set (E 0)) (φ : E 0 → E n) (u : E 0), u ∈ V →
    V = univ ∧ φ '' V = {φ u} ∧
    ∀ (s : Fin 0 ↪ Fin n), (coordinateProjection s ∘ φ) '' V = univ ∧
      LeftInvOn (fun _ : E n => (0 : E 0)) φ V ∧
      RightInvOn (fun _ : E n => (0 : E 0)) φ (φ '' V)

end Specs.D04.C14.LocalGraphAndAmbientInverse
