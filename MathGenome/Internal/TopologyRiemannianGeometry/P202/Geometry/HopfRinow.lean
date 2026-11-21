import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.HopfRinow
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricGeodesicCompleteness
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CompleteExponentialMinimizers

/-! Hopf–Rinow (Theorem 6.10). The geometric continuation and attainment
arguments are upstream; here compact balls give metric completeness and the
three conditions and the single-center strengthening are assembled. -/
set_option autoImplicit false

namespace P202.Geometry.HopfRinow
open SmoothManifolds.AtlasData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.GeodesicData
  P202.ExponentialData P202.CompletenessData P202.CompleteExponentialData
  P202.HopfRinowData
open Set
universe u

abbrev GeodesicallyComplete := @P202.HopfRinowData.GeodesicallyComplete

/-- The source convention for boundedness agrees with metric boundedness. -/
theorem closedBoundedCompact_iff :
    P202Specs.Geometry.HopfRinow.closedBoundedCompact_iffType.{u} := by
  intro n M t S g p d htop hd
  let d' : MetricSpace M := d.replaceTopology htop.symm
  letI : MetricSpace M := d'
  have heq : d' = d := MetricSpace.replaceTopology_eq d htop.symm
  have hd' : ∀ x y : M, dist x y = lengthDistance g x y := hd
  have hb (K : Set M) : Bornology.IsBounded K ↔
      ∃ R : ℝ, ∀ q ∈ K, lengthDistance g p q ≤ R := by
    rw [CompleteExponentialMinimizers.bounded_iff_distance_bound p K]
    simp_rw [hd']
  change ClosedBoundedCompact g p ↔
    ∀ K : Set M, IsClosed K → @Bornology.IsBounded M d.toBornology K → IsCompact K
  rw [← heq]
  exact ⟨fun h K hK hB => h K hK ((hb K).mp hB),
    fun h K hK hB => h K hK ((hb K).mpr hB)⟩

variable {n : ℕ} {M : Type u} [TopologicalSpace M] [ConnectedSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Compactness of closed bounded sets, measured from just one center,
implies completeness. The only metric installed is the original length metric
with exactly the original topology. -/
theorem complete_of_closedBoundedCompact (g : RiemannianMetric S) (p : M)
    (hproper : ClosedBoundedCompact g p) : LengthMetricComplete g := by
  obtain ⟨d, htop, hd⟩ := CompleteExponentialMinimizers.lengthDistance_metric g
  let d' : MetricSpace M := d.replaceTopology htop.symm
  letI : MetricSpace M := d'
  have hd' : ∀ x y : M, dist x y = lengthDistance g x y := hd
  letI : ProperSpace M := ⟨by
    intro x R
    apply hproper (Metric.closedBall x R) Metric.isClosed_closedBall
    refine ⟨dist p x + R, ?_⟩
    intro q hq
    rw [← hd']
    calc
      dist p q ≤ dist p x + dist x q := dist_triangle p x q
      _ ≤ dist p x + R := add_le_add le_rfl
        (by simpa only [Metric.mem_closedBall, dist_comm] using hq)⟩
  exact ⟨d', rfl, hd', inferInstance⟩

/-- Geodesic completeness puts every vector in the actual time-one domain. -/
theorem full_exponential_of_geodesicallyComplete
    (C : Connection (tangentBundle S)) (hcomplete : GeodesicallyComplete S C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    FullExponentialAt F p := by
  intro v
  change 1 ∈ (F.interval ⟨p, v⟩).carrier
  rw [hcomplete _ _ _ (hF ⟨p, v⟩)]
  exact mem_univ _

/-- A single full exponential gives metric completeness via compact balls. -/
theorem complete_of_full_exponential (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (hp : FullExponentialAt F p) : LengthMetricComplete g := by
  exact complete_of_closedBoundedCompact g p
    (CompleteExponentialMinimizers.complete_exponential_minimizers S g C hC F hF p hp).2.2

/-- Global maximal geodesics imply completeness of the length metric. -/
theorem complete_of_geodesicallyComplete (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hcomplete : GeodesicallyComplete S C) : LengthMetricComplete g := by
  obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  exact complete_of_full_exponential g C hC F hF p
    (full_exponential_of_geodesicallyComplete C hcomplete F hF p)

/-- Completeness gives both minimizing segments at every center and
compactness of every closed bounded subset. -/
theorem complete_conclusions (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hcomplete : LengthMetricComplete g)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M) :
    MinimizingGeodesicsFrom g C F p ∧ ClosedBoundedCompact g p := by
  have hgeo : GeodesicallyComplete S C :=
    MetricGeodesicCompleteness.metric_complete_geodesically_complete S g C hC hcomplete
  have hp := full_exponential_of_geodesicallyComplete C hgeo F hF p
  have h := CompleteExponentialMinimizers.complete_exponential_minimizers S g C hC F hF p hp
  exact ⟨h.1, h.2.2⟩

/-- The complete equivalence and the single-center strengthening, without
positive-dimension restrictions or uniqueness of distant minimizers. -/
theorem hopf_rinow : P202Specs.Geometry.HopfRinow.hopf_rinowType.{u} := by
  intro n M _ _ S g C hC
  have hforward : LengthMetricComplete g → GeodesicallyComplete S C :=
    MetricGeodesicCompleteness.metric_complete_geodesically_complete S g C hC
  have hproper : LengthMetricComplete g → ∀ p : M, ClosedBoundedCompact g p := by
    intro hc p
    obtain ⟨F, hF⟩ := ExponentialNormalCoordinates.family_exists S C
    exact (complete_conclusions g C hC hc F hF p).2
  refine ⟨⟨hforward, complete_of_geodesicallyComplete g C hC⟩,
    ⟨hproper, ?_⟩, ?_, ?_⟩
  · intro hp
    obtain ⟨p⟩ := (inferInstance : Nonempty M)
    exact complete_of_closedBoundedCompact g p (hp p)
  · intro hc F hF p
    exact (complete_conclusions g C hC hc F hF p).1
  · intro F hF p hp
    have hc := complete_of_full_exponential g C hC F hF p hp
    exact ⟨hc, hforward hc, hproper hc,
      fun q => (complete_conclusions g C hC hc F hF q).1⟩

end P202.Geometry.HopfRinow
