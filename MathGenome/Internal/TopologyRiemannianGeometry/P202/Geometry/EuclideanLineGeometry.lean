import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.EuclideanLineGeometry
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LeviCivita
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SectionalRecovery
import MathGenome.Internal.SmoothManifolds.SmoothManifolds.Ch03.RegularDomains

set_option autoImplicit false
set_option maxHeartbeats 500000
namespace P202.Geometry.EuclideanLineGeometry
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleMetricData
  SmoothManifolds.RegularDomainData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData
  P202.CurvatureData P202.RicciData P202.MyersData
open Set Filter
open scoped Topology

/-- A global tangent chart transports the ordinary Euclidean scalar product
onto the original tangent fibers. -/
noncomputable def globalChartMetric (S : SmoothManifold 1 .euclidean ℝ)
    (c : TangentIndex S) (hc : c.val.source = univ) : RiemannianMetric S where
  form := SmoothManifolds.BundleMetrics.localForm (tangentBundle S) c
  symmetric := SmoothManifolds.BundleMetrics.localForm_symmetric (tangentBundle S) c
  positive := by
    intro p v hv
    apply SmoothManifolds.BundleMetrics.localForm_positive (tangentBundle S) c p _ v hv
    rw [(tangentRealization S).baseSet, hc]
    exact mem_univ p
  smooth := by
    intro i j k p hp
    apply SmoothManifolds.BundleMetrics.localForm_gram_smoothAt (tangentBundle S) i c j k p hp
    rw [(tangentRealization S).baseSet, hc]
    exact mem_univ p

/-- The intrinsic coordinate map evaluates on the same scalar germ as dx. -/
theorem real_coordinate_derivative (S : SmoothManifold 1 .euclidean ℝ)
    (hs : realChart ∈ S.smoothStructure.val) (p : ℝ) (v : TangentSpace S p) :
    SmoothManifolds.BundleMetrics.coordinateMap (tangentBundle S) ⟨realChart, hs⟩ p v 0 =
      scalarDerivative S (fun y : ℝ => y) p v := by
  have hp : p ∈ realChart.source := mem_univ _
  rw [SmoothManifolds.BundleMetrics.coordinateMap_of_mem (tangentBundle S)
    ⟨realChart, hs⟩ p (by rw [(tangentRealization S).baseSet]; exact hp)]
  rw [(tangentRealization S).coordinates ⟨realChart, hs⟩ p hp]
  obtain ⟨coords, hcoords, heval⟩ :=
    (tangentStructure S).fiberCoordinates.isCoordinates realChart hs p hp
  rw [heval]
  have hf : SmoothManifolds.PartitionData.ScalarContDiffAt (⊤ : ℕ∞)
      S.smoothStructure.val (fun y : ℝ => y) p := by
    apply SmoothManifolds.scalarContDiffAt_of_chart S.smoothStructure.property.1 hs hp
    refine ⟨univ, isOpen_univ, mem_univ _, (fun z : Euclidean 1 => z 0),
      (contDiff_apply ℝ (fun _ : Fin 1 => ℝ) 0).contDiffOn, ?_⟩
    exact Eventually.of_forall (fun _ => rfl)
  have hg : scalarGerm S (fun y : ℝ => y) p = coords 0 := by
    apply Subtype.ext
    simp only [scalarGerm, dite_eq_left hf]
    exact (hcoords 0).symm
  change v.val (coords 0) = v.val (scalarGerm S (fun y : ℝ => y) p)
  rw [hg]

/-- Curvature vanishes on any one-dimensional Riemannian manifold. -/
theorem curvature_zero (S : SmoothManifold 1 .euclidean ℝ)
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (p : ℝ) : R.val p = 0 := by
  have hform := SectionalRecovery.curvature_constant g C hC R hR p 0 (by
    intro x y hi
    let := (SmoothManifolds.tangent_dimension S p).1
    have hh := hi.fintype_card_le_finrank
    rw [(SmoothManifolds.tangent_dimension S p).2] at hh
    norm_num at hh)
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply LinearMap.ext
  intro z
  change R.val p x y z = 0
  by_contra hn
  have hz := hform x y z (R.val p x y z)
  have hp := g.positive p (R.val p x y z) hn
  simp only [curvatureForm, zero_mul] at hz
  exact (ne_of_gt hp) hz

theorem euclidean_line_geometry :
    P202Specs.Geometry.EuclideanLineGeometry.euclidean_line_geometryType := by
  obtain ⟨S, hs⟩ := SmoothManifolds.RegularDomains.standard_real_structure
  let g := globalChartMetric S ⟨realChart, hs⟩ rfl
  obtain ⟨C, hC, _⟩ := LeviCivita.exists_unique g
  obtain ⟨R, hR, _⟩ := CurvatureAlgebra.tensor_exists_unique C
  have hzero (p : ℝ) : R.val p = 0 := curvature_zero S g C hC R hR p
  have hricci (p : ℝ) : ricci R p = 0 := by
    ext v w
    unfold ricci
    rw [hzero]
    change LinearMap.trace ℝ (TangentSpace S p) 0 = 0
    exact map_zero _
  refine ⟨S, g, C, R, ⟨realChart, hs, rfl, rfl, fun _ => rfl⟩, ?_, hC, hR, hricci, ?_⟩
  · intro p v w
    change SmoothManifolds.BundleMetrics.localForm (tangentBundle S) ⟨realChart, hs⟩ p v w = _
    rw [SmoothManifolds.BundleMetrics.localForm_apply]
    simp only [Fin.sum_univ_one]
    rw [real_coordinate_derivative S hs p v, real_coordinate_derivative S hs p w]
  · intro k hk p v
    rw [hricci]
    norm_num

end P202.Geometry.EuclideanLineGeometry
