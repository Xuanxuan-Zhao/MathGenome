import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarVolumeIntegration
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarDensityComparison

/-! Bishop--Gromov, paper.tex 4404–4490. The model volume parameter ranges
through all the actual same-dimensional Euclidean, round spherical and induced
hyperboloid realizations of the upstream model-ball integration interface.
`IsModelVolume` selects geometric models, and contains no comparison assumption.
All volumes are the original Borel Riemannian measure of open metric balls. -/
set_option autoImplicit false
noncomputable section
open scoped ENNReal Topology

namespace P202.BishopGromovData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CompletenessData
  P202.SpaceFormData P202.ModelPolarData P202.PolarIntegrationData

/-- The actual model-ball profiles in all three signs of curvature. The
positive scale a realizes curvature ±1/a², so every real curvature is covered.
These are exactly the models quantified in `model_volumeType`. -/
def IsModelVolume (n : ℕ) (k : ℝ) (V : ℝ → ℝ≥0∞) : Prop :=
  (k = 0 ∧ ∃ G : EuclideanModel n, G.Conclusion ∧
    ∃ p : E n, V = modelVolume G.metric p) ∨
  (∃ a : ℝ, 0 < a ∧ k = (a ^ 2)⁻¹ ∧
    ∃ (A : EuclideanModel (n+1)) (B : SphericalModel n a A), B.Conclusion ∧
    ∃ p : Sphere n a, V = modelVolume B.metric p) ∨
  (∃ a : ℝ, 0 < a ∧ k = -(a ^ 2)⁻¹ ∧
    ∃ (S : SmoothManifold n .euclidean (P202.HyperboloidData.Hyperboloid n a))
      (g : RiemannianMetric S) (C : Connection (tangentBundle S)),
      HasProjectionChart S ∧ P202.HyperboloidData.IsInduced g ∧ IsLeviCivita g C ∧
      LengthMetricComplete g ∧
      ∃ p : P202.HyperboloidData.Hyperboloid n a, V = modelVolume g p)

/-- Real quotient of the finite actual ball volumes. -/
def volumeRatio {n : ℕ} {M : Type*} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) (p : M)
    (V : ℝ → ℝ≥0∞) (r : ℝ) : ℝ :=
  (ballVolume g p r).toReal / (V r).toReal

end P202.BishopGromovData

namespace P202Specs.Geometry.BishopGromov
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.CompletenessData P202.PolarComparisonData P202.BishopGromovData
open Set Filter
universe u

/-- Complete theorem, including the initial limit and the value and comparison
at the finite spherical endpoint. No claim is made beyond that endpoint. -/
def bishop_gromovType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S), 2 ≤ n →
    LengthMetricComplete g →
    ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ k : ℝ, RicciLowerBound g R k →
    ∀ V : ℝ → ℝ≥0∞, IsModelVolume n k V → ∀ p : M,
      AntitoneOn (volumeRatio g p V) (comparisonInterval k) ∧
      Tendsto (volumeRatio g p V) (𝓝[>] (0 : ℝ)) (𝓝 1) ∧
      ∀ hk : 0 < k,
        let b := Real.pi / Real.sqrt k
        Tendsto (volumeRatio g p V) (𝓝[<] b) (𝓝 (volumeRatio g p V b)) ∧
        ∀ r ∈ comparisonInterval k, volumeRatio g p V b ≤ volumeRatio g p V r

end P202Specs.Geometry.BishopGromov
