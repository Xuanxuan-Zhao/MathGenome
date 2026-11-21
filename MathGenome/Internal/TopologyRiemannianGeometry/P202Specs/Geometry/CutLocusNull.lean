import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.CutPolarDomain
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RiemannianVolume

/-! The canonical Borel volume and the full cut-locus nullity assertion,
paper.tex, Lemma `lem:p202-cut-null` (4383–4402). -/
set_option autoImplicit false
noncomputable section

namespace P202.CutNullData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData
universe u

/-- The unique regular Borel measure representing integration against the
actual smooth positive Riemannian density. -/
def volume {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S) :
    @MeasureTheory.Measure M (borel M) :=
  (P202.Geometry.RiemannianVolume.measure_representation_exists g).choose

end P202.CutNullData

namespace P202Specs.Geometry.CutLocusNull
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.ExponentialData
  P202.CompletenessData P202.CutTimeData
universe u

/-- No orientability hypothesis; positive dimension includes dimension one.
The auxiliary connection and maximal geodesic family are arbitrary correct
ones, whose existence is already proved upstream. -/
def cut_locus_nullType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S),
    0 < n → LengthMetricComplete g →
    ∀ C : Connection (tangentBundle S), IsLeviCivita g C →
    ∀ F : CurveFamily (Phase S), IsMaximalFamily S C F →
    ∀ p : M, P202.CutNullData.volume g (cutLocus g F p) = 0

end P202Specs.Geometry.CutLocusNull
