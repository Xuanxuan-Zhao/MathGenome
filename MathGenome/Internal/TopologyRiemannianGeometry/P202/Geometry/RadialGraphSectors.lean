import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RadialGraphSectors
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization
import Batteries.Tactic.OpenPrivate
import Mathlib.Geometry.Euclidean.Angle.Oriented.Basic
import Mathlib.Order.Fin.Tuple
import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Fin.Rotate
import Mathlib.Analysis.Normed.Module.Ray
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.Complex.Arg
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Abel

/-! Local radial geometry for paper.tex 5117–5128. Recovered parent helpers
are proved here without importing the pending corner-gluing module. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false
noncomputable section
open Set Complex
open scoped BigOperators
open SmoothManifolds (ModelKind)
open SmoothManifolds.BoundaryData
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.MetricBoundaryTurning
open P202Specs.SurfaceRegionConstruction
universe u
namespace P202.RadialGraphSectors
lemma coe_positiveAngle (theta : Real.Angle) :
    (positiveAngle theta : Real.Angle) = theta := by
  unfold positiveAngle
  split
  · exact Real.Angle.coe_toReal _
  · rw [Real.Angle.coe_add, Real.Angle.coe_toReal, Real.Angle.coe_two_pi, add_zero]

lemma positiveAngle_mem (theta : Real.Angle) :
    positiveAngle theta ∈ Ioc 0 (2 * Real.pi) := by
  obtain ⟨hl, hu⟩ := Real.Angle.toReal_mem_Ioc theta
  unfold positiveAngle
  split <;> constructor <;> linarith [Real.pi_pos]

lemma positiveAngle_coe {r : ℝ} (hr : r ∈ Ioc 0 (2 * Real.pi)) :
    positiveAngle (r : Real.Angle) = r := by
  by_cases hp : r ≤ Real.pi
  · rw [positiveAngle, Real.Angle.toReal_coe_eq_self_iff.mpr
      ⟨by linarith [Real.pi_pos, hr.1], hp⟩, ite_eq_left hr.1]
  · have hreal : (r : Real.Angle).toReal = r - 2 * Real.pi :=
      Real.Angle.toReal_coe_eq_self_sub_two_pi_iff.mpr
        ⟨lt_of_not_ge hp, by linarith [hr.2, Real.pi_pos]⟩
    rw [positiveAngle, hreal, ite_eq_right (by linarith [hr.2])]
    ring

lemma positiveAngle_eq_of_coe {theta : Real.Angle} {r : ℝ}
    (hr : r ∈ Ioc 0 (2 * Real.pi)) (h : (r : Real.Angle) = theta) :
    positiveAngle theta = r := by
  rw [← h, positiveAngle_coe hr]

lemma positiveAngle_sub_of_lt {a b : Real.Angle}
    (h : positiveAngle a < positiveAngle b) :
    positiveAngle (b - a) = positiveAngle b - positiveAngle a := by
  apply positiveAngle_eq_of_coe
  · obtain ⟨ha0, ha2⟩ := positiveAngle_mem a
    obtain ⟨hb0, hb2⟩ := positiveAngle_mem b
    exact ⟨sub_pos.mpr h, by linarith⟩
  · rw [Real.Angle.coe_sub, coe_positiveAngle, coe_positiveAngle]

lemma positiveAngle_sub_of_le {a b : Real.Angle}
    (h : positiveAngle b ≤ positiveAngle a) :
    positiveAngle (b - a) = positiveAngle b - positiveAngle a + 2 * Real.pi := by
  apply positiveAngle_eq_of_coe
  · obtain ⟨ha0, ha2⟩ := positiveAngle_mem a
    obtain ⟨hb0, hb2⟩ := positiveAngle_mem b
    constructor <;> linarith
  · rw [Real.Angle.coe_add, Real.Angle.coe_sub, coe_positiveAngle,
      coe_positiveAngle, Real.Angle.coe_two_pi, add_zero]

lemma exists_sorting_equiv {n : ℕ} (f : Fin n → ℝ) (hf : Function.Injective f) :
    ∃ e : Equiv.Perm (Fin n), StrictMono (f ∘ e) := by
  classical
  let F : Finset ℝ := Finset.univ.image f
  have hF : F.card = n := by simp [F, Finset.card_image_of_injective _ hf]
  let r : Fin n ≃ F := Equiv.ofBijective
    (fun i => ⟨f i, Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩⟩)
    ⟨fun i j h => hf (congrArg Subtype.val h), by
      rintro ⟨x, hx⟩
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      exact ⟨i, rfl⟩⟩
  let e : Equiv.Perm (Fin n) := (F.orderIsoOfFin hF).toEquiv.trans r.symm
  refine ⟨e, ?_⟩
  have he (i : Fin n) : f (e i) = (F.orderIsoOfFin hF i).val := by
    change (r (r.symm _)).val = _
    rw [r.apply_symm_apply]
    rfl
  intro i j hij
  simp only [Function.comp_apply, he]
  exact (F.orderIsoOfFin hF).strictMono hij

lemma positiveAngle_lt_two_pi {theta : Real.Angle} (h : theta ≠ 0) :
    positiveAngle theta < 2 * Real.pi := by
  apply (positiveAngle_mem theta).2.lt_of_ne
  intro he
  apply h
  rw [← coe_positiveAngle theta, he, Real.Angle.coe_two_pi]

lemma sum_adjacent_differences {n : ℕ} (f : Fin (n + 1) → ℝ) :
    (∑ i : Fin n, (f i.succ - f i.castSucc)) = f (Fin.last n) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ f
  have h1 := Fin.sum_univ_castSucc f
  linarith

section VectorAngles
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

lemma phase_injective {n : ℕ} (o : Orientation ℝ V (Fin 2))
    (v : Fin n → V) (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i j, SameRay ℝ (v i) (v j) → i = j)
    (w : V) (hw : w ≠ 0) :
    Function.Injective (fun i => positiveAngle (o.oangle w (v i))) := by
  intro i j h
  have ha := congrArg (fun r : ℝ => (r : Real.Angle)) h
  simp only [coe_positiveAngle] at ha
  apply hd i j
  apply o.oangle_eq_zero_iff_sameRay.mp
  rw [← o.oangle_sub_left hw (hv i) (hv j), ha, sub_self]

/-- Arbitrary finitely many distinct rays admit an actual metric cyclic order.
No angle sum or sector incidence certificate is a hypothesis. -/
theorem exists_cyclic_angle_sum {n : ℕ} (hn : 0 < n)
    (o : Orientation ℝ V (Fin 2)) (v : Fin n → V)
    (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i j, SameRay ℝ (v i) (v j) → i = j) :
    ∃ e : Equiv.Perm (Fin n),
      StrictMono (fun i => positiveAngle (o.oangle (v ⟨0, hn⟩) (v (e i)))) ∧
      (∑ i, positiveAngle (o.oangle (v (e i)) (v (e (finRotate n i))))) =
        2 * Real.pi := by
  let z : Fin n := ⟨0, hn⟩
  let phase (i : Fin n) : Real.Angle := o.oangle (v z) (v i)
  obtain ⟨e, he⟩ := exists_sorting_equiv (fun i => positiveAngle (phase i))
    (phase_injective o v hv hd (v z) (hv z))
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have hgap (i : Fin (m + 1)) :
      positiveAngle (o.oangle (v (e i)) (v (e (finRotate (m + 1) i)))) =
        positiveAngle (phase (e (finRotate (m + 1) i))) - positiveAngle (phase (e i)) +
          if i = Fin.last m then 2 * Real.pi else 0 := by
    rw [← o.oangle_sub_left (hv z) (hv (e i)) (hv (e (finRotate _ i)))]
    change positiveAngle (phase (e (finRotate _ i)) - phase (e i)) = _
    by_cases hi : i = Fin.last m
    · rw [ite_eq_left hi, positiveAngle_sub_of_le]
      apply he.monotone
      simpa only [hi, finRotate_last] using (Fin.zero_le (Fin.last m))
    · rw [ite_eq_right hi, add_zero, positiveAngle_sub_of_lt]
      exact he ((lt_finRotate_iff_ne_last i).mpr hi)
  refine ⟨e, he, ?_⟩
  simp_rw [hgap]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hperm := Equiv.sum_comp (finRotate (m + 1)) (fun i => positiveAngle (phase (e i)))
  rw [hperm]
  simp

/-- Distinct rays give strictly smaller-than-full metric gaps. -/
lemma positiveAngle_oangle_lt_two_pi (o : Orientation ℝ V (Fin 2))
    {v w : V} (h : ¬SameRay ℝ v w) :
    positiveAngle (o.oangle v w) < 2 * Real.pi :=
  positiveAngle_lt_two_pi (mt o.oangle_eq_zero_iff_sameRay.mp h)

/-- Inserting a genuine interior ray splits its metric sector additively.
The premise describes angular membership, rather than assuming an angle sum. -/
lemma positiveAngle_oangle_add_of_between (o : Orientation ℝ V (Fin 2))
    {u v w : V} (hu : u ≠ 0) (hv : v ≠ 0) (hw : w ≠ 0)
    (h : positiveAngle (o.oangle u w) < positiveAngle (o.oangle u v)) :
    positiveAngle (o.oangle u w) + positiveAngle (o.oangle w v) =
      positiveAngle (o.oangle u v) := by
  rw [← o.oangle_sub_left hu hw hv, positiveAngle_sub_of_lt h]
  ring

/-- Closed oriented tangent half-planes give principal phases in [0, pi]. -/
lemma phase_mem_of_halfPlane (o : Orientation ℝ V (Fin 2)) {w v : V}
    (h : 0 ≤ o.areaForm w v) : (o.oangle w v).toReal ∈ Icc 0 Real.pi := by
  refine ⟨?_, Real.Angle.toReal_le_pi _⟩
  rw [Orientation.oangle, Complex.arg_coe_angle_toReal_eq_arg, Complex.arg_nonneg_iff]
  simpa [Orientation.kahler_apply_apply] using h

/-- Arbitrary distinct rays in a closed tangent half-plane, including its
actual two boundary rays, have metric adjacent gaps summing to pi. -/
theorem exists_halfPlane_angle_sum {n : ℕ}
    (o : Orientation ℝ V (Fin 2)) (v : Fin (n + 2) → V)
    (hv : ∀ i, v i ≠ 0)
    (hd : ∀ i j, SameRay ℝ (v i) (v j) → i = j)
    (w : V) (hw : w ≠ 0)
    (hhalf : ∀ i, 0 ≤ o.areaForm w (v i))
    (i0 i1 : Fin (n + 2)) (h0 : v i0 = w) (h1 : v i1 = -w) :
    ∃ e : Equiv.Perm (Fin (n + 2)),
      StrictMono (fun i => (o.oangle w (v (e i))).toReal) ∧
      (∑ i : Fin (n + 1),
        positiveAngle (o.oangle (v (e i.castSucc)) (v (e i.succ)))) = Real.pi := by
  let phase (i : Fin (n + 2)) := (o.oangle w (v i)).toReal
  have hb (i : Fin (n + 2)) : phase i ∈ Icc 0 Real.pi :=
    phase_mem_of_halfPlane o (hhalf i)
  have hinj : Function.Injective phase := by
    intro i j h
    apply hd i j
    apply o.oangle_eq_zero_iff_sameRay.mp
    have ha : o.oangle w (v i) = o.oangle w (v j) := Real.Angle.toReal_injective h
    rw [← o.oangle_sub_left hw (hv i) (hv j), ha, sub_self]
  obtain ⟨e, he⟩ := exists_sorting_equiv phase hinj
  have hp0 : phase i0 = 0 := by simp [phase, h0]
  have hp1 : phase i1 = Real.pi := by
    simp only [phase, h1, o.oangle_neg_self_right hw, Real.Angle.toReal_pi]
  have he0 : phase (e 0) = 0 := by
    obtain ⟨j, hj⟩ := e.surjective i0
    have hm := he.monotone (Fin.zero_le j)
    change phase (e 0) ≤ phase (e j) at hm
    rw [hj, hp0] at hm
    exact le_antisymm hm (hb (e 0)).1
  have he1 : phase (e (Fin.last (n + 1))) = Real.pi := by
    obtain ⟨j, hj⟩ := e.surjective i1
    have hm := he.monotone (Fin.le_last j)
    change phase (e j) ≤ phase (e (Fin.last (n + 1))) at hm
    rw [hj, hp1] at hm
    exact le_antisymm (hb (e (Fin.last (n + 1)))).2 hm
  refine ⟨e, he, ?_⟩
  have hgap (i : Fin (n + 1)) :
      positiveAngle (o.oangle (v (e i.castSucc)) (v (e i.succ))) =
        phase (e i.succ) - phase (e i.castSucc) := by
    apply positiveAngle_eq_of_coe
    · refine ⟨sub_pos.mpr (he (Fin.castSucc_lt_succ (i := i))), ?_⟩
      have hleft := (hb (e i.castSucc)).1
      have hright := (hb (e i.succ)).2
      linarith [Real.pi_pos]
    · rw [Real.Angle.coe_sub, Real.Angle.coe_toReal, Real.Angle.coe_toReal,
        o.oangle_sub_left hw (hv _) (hv _)]
  simp_rw [hgap]
  rw [sum_adjacent_differences (fun i => phase (e i)), he1, he0, sub_zero]

/-- The preceding cyclic result survives every injective change of tangent
coordinates, with no conformality assumption on that coordinate change. -/
theorem exists_cyclic_angle_sum_linearImage
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ} (hn : 0 < n) (o : Orientation ℝ V (Fin 2))
    (L : W ≃ₗ[ℝ] V) (d : Fin n → W)
    (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1) :
    ∃ e : Equiv.Perm (Fin n),
      StrictMono (fun i => positiveAngle (o.oangle (L (d ⟨0, hn⟩)) (L (d (e i))))) ∧
      (∑ i, positiveAngle (o.oangle (L (d (e i))) (L (d (e (finRotate n i)))))) =
        2 * Real.pi := by
  apply exists_cyclic_angle_sum hn o (fun i => L (d i))
  · intro i
    apply L.map_ne_zero_iff.mpr
    exact norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  · intro i j hij
    apply hd
    exact ((SameRay.sameRay_map_iff L).mp hij).eq_of_norm_eq (by rw [hu, hu])
end VectorAngles

open private occupiedChartVectorEquiv occupiedChartVectorEquiv_apply from
  MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GlobalGaussBonnetLocalization

open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleOperationsData
open P202.MetricData P202.SurfaceBoundaryData
open P202Specs.PlanarRegionTopology P202Specs.MetricBoundaryTurning

section ChartAngles
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}

/-- Literal chart metric angles have the full-plane cyclic sum for every
finite injective family of unit coordinate rays. The metric can be arbitrary. -/
theorem chart_positiveMetricAngle_cyclic_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c)
    {n : ℕ} (hn : 0 < n) (d : Fin n → Plane)
    (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1) :
    ∃ e : Equiv.Perm (Fin n),
      (∑ i, positiveMetricAngle g o c hc x (d (e i)) (d (e (finRotate n i)))) =
        2 * Real.pi := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let L := occupiedChartVectorEquiv c hc x hx
  let op := planeOrientation g o p
  obtain ⟨e, _, he⟩ := exists_cyclic_angle_sum_linearImage hn op L d hd hu
  refine ⟨e, ?_⟩
  have hangle (u v : Plane) : positiveMetricAngle g o c hc x u v =
      positiveAngle (op.oangle (L u) (L v)) := by
    rw [occupiedChartVectorEquiv_apply,
      occupiedChartVectorEquiv_apply]
    rfl
  simpa only [hangle] using he

/-- Literal metric half-plane sectors for arbitrary distinct coordinate rays.
The closed half-plane is specified by the actual tangent area form and its
boundary consists of the two supplied opposite rays. -/
theorem chart_positiveMetricAngle_halfPlane_sum
    (g : RiemannianMetric S) (o : SmoothManifolds.OrientationData.Orientation S)
    (c : ModelChart 2 .euclidean M) (hc : c ∈ S.smoothStructure.val)
    (x : Plane) (hx : x ∈ P202Specs.ChartRegionStokes.chartTarget c)
    {n : ℕ} (d : Fin (n + 2) → Plane)
    (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (w : Plane) (hw : w ≠ 0)
    (hhalf : ∀ i, 0 ≤ orientedArea g o (chartPoint c x)
      (chartVector c hc x w) (chartVector c hc x (d i)))
    (i0 i1 : Fin (n + 2)) (h0 : d i0 = w) (h1 : d i1 = -w) :
    ∃ e : Equiv.Perm (Fin (n + 2)),
      (∑ i : Fin (n + 1), positiveMetricAngle g o c hc x
        (d (e i.castSucc)) (d (e i.succ))) = Real.pi := by
  let p := chartPoint c x
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let L := occupiedChartVectorEquiv c hc x hx
  let op := planeOrientation g o p
  have hv (i : Fin (n + 2)) : L (d i) ≠ 0 := by
    apply L.map_ne_zero_iff.mpr
    exact norm_ne_zero_iff.mp (by rw [hu]; exact one_ne_zero)
  have hr (i j : Fin (n + 2)) (hij : SameRay ℝ (L (d i)) (L (d j))) : i = j := by
    apply hd
    exact ((SameRay.sameRay_map_iff L).mp hij).eq_of_norm_eq (by rw [hu, hu])
  have hhalf' (i : Fin (n + 2)) : 0 ≤ op.areaForm (L w) (L (d i)) := by
    change 0 ≤ orientedArea g o p (L w) (L (d i))
    rw [occupiedChartVectorEquiv_apply, occupiedChartVectorEquiv_apply]
    exact hhalf i
  obtain ⟨e, _, he⟩ := exists_halfPlane_angle_sum op (fun i => L (d i)) hv hr
    (L w) (L.map_ne_zero_iff.mpr hw) hhalf' i0 i1
    (congrArg L h0) (by rw [h1, map_neg])
  refine ⟨e, ?_⟩
  have hangle (u v : Plane) : positiveMetricAngle g o c hc x u v =
      positiveAngle (op.oangle (L u) (L v)) := by
    rw [occupiedChartVectorEquiv_apply, occupiedChartVectorEquiv_apply]
    rfl
  simpa only [hangle] using he

end ChartAngles
section BoundaryStarDirections
open SmoothManifolds.BoundaryData P202Specs.PlaneTurning
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
  {G : EmbeddedGraph S} {p : M}

/-- A genuine boundary center lies on the coordinate seam in every star chart. -/
lemma graphStar_center_second_eq_zero (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S) :
    coordinates s.chart p 1 = 0 := by
  have hf := (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem p
    s.mem_source).mp hp
  exact hf

lemma graphStar_direction_second_nonneg (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) (i : Fin s.rayCount) : 0 ≤ s.direction i 1 := by
  have h := s.rays_in_model i (s.radius / 2) (by linarith [s.radius_pos])
    (by linarith [s.radius_pos])
  change 0 ≤ (coordinates s.chart p + (s.radius / 2) • s.direction i) 1 at h
  simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
    graphStar_center_second_eq_zero s hp, zero_add] at h
  exact nonneg_of_mul_nonneg_right h (by linarith [s.radius_pos])

/-- Any unit direction in the boundary line is one of the actual star rays.
The boundary containment hypothesis, rather than a special arrangement shape,
provides both seam rays. -/
lemma graphStar_boundary_direction_mem (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) (hB : intrinsicBoundary S ⊆ G.carrier)
    (w : Plane) (hw : ‖w‖ = 1) (hw1 : w 1 = 0) :
    ∃ i : Fin s.rayCount, s.direction i = w := by
  let r := s.radius / 2
  have hr : 0 < r := by dsimp [r]; linarith [s.radius_pos]
  have hrlt : r < s.radius := by dsimp [r]; linarith [s.radius_pos]
  have hmodel : toPlane.symm (coordinates s.chart p + r • w) ∈ modelSet 2 .halfSpace := by
    change 0 ≤ (coordinates s.chart p + r • w) 1
    simp only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul, hw1, mul_zero,
      graphStar_center_second_eq_zero s hp, add_zero, le_refl]
  let z : ModelSpace 2 .halfSpace := ⟨toPlane.symm (coordinates s.chart p + r • w), hmodel⟩
  have hzball : toPlane z.val ∈ Metric.ball (coordinates s.chart p) s.radius := by
    change ‖toPlane (toPlane.symm _) - coordinates s.chart p‖ < s.radius
    rw [toPlane.apply_symm_apply, add_sub_cancel_left, norm_smul,
      Real.norm_eq_abs, abs_of_pos hr, hw, mul_one]
    exact hrlt
  have hz : z ∈ s.chart.target := s.ball_in_target z hzball
  let x := s.chart.symm z
  have hxs : x ∈ s.chart.source := s.chart.map_target hz
  have hxcoord : coordinates s.chart x = coordinates s.chart p + r • w := by
    change toPlane (s.chart (s.chart.symm z)).val = _
    rw [s.chart.right_inv hz]
    exact toPlane.apply_symm_apply _
  have hxB : x ∈ intrinsicBoundary S := by
    apply (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem x hxs).mpr
    change (s.chart x).val (Fin.last 1) = 0
    have he := congrArg (fun v : Plane => v 1) hxcoord
    change (s.chart x).val (Fin.last 1) = _ at he
    simpa only [PiLp.add_apply, PiLp.smul_apply, smul_eq_mul,
      graphStar_center_second_eq_zero s hp, hw1, mul_zero, add_zero] using he
  have hxball : coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius := by
    rw [hxcoord]
    simpa only [z, toPlane.apply_symm_apply] using hzball
  have hxne : x ≠ p := by
    intro he
    have hzero : r • w = 0 := by
      rw [he] at hxcoord
      exact (add_eq_left.mp hxcoord.symm)
    have hwne : w ≠ 0 := norm_ne_zero_iff.mp (hw.trans_ne one_ne_zero)
    exact hwne ((smul_eq_zero.mp hzero).resolve_left hr.ne')
  obtain hxp | ⟨i, t, ht, _, he⟩ := (s.graph_eq x hxs hxball).mp (hB hxB)
  · exact (hxne hxp).elim
  have heq : r • w = t • s.direction i := by
    exact add_left_cancel (hxcoord.symm.trans he)
  have hrt : r = t := by
    have hn := congrArg norm heq
    simpa only [norm_smul, Real.norm_eq_abs, abs_of_pos hr, abs_of_pos ht,
      hw, s.direction_unit i, mul_one] using hn
  refine ⟨i, ?_⟩
  rw [← hrt] at heq
  exact (smul_right_injective _ hr.ne' heq).symm

/-- Exactly two star rays are tangent to the genuine smooth boundary. Every
other ray lies strictly inside its coordinate half-plane. -/
lemma graphStar_boundary_rays (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) (hB : intrinsicBoundary S ⊆ G.carrier) :
    ∃ i₀ i₁ : Fin s.rayCount, i₀ ≠ i₁ ∧
      s.direction i₀ = reference ∧ s.direction i₁ = -reference ∧
      ∀ i, 0 ≤ s.direction i 1 ∧
        (s.direction i 1 = 0 ↔ i = i₀ ∨ i = i₁) := by
  have href : ‖reference‖ = 1 := by norm_num [reference, EuclideanSpace.norm_eq]
  have href1 : reference 1 = 0 := by norm_num [reference]
  obtain ⟨i₀, h₀⟩ := graphStar_boundary_direction_mem s hp hB reference href href1
  obtain ⟨i₁, h₁⟩ := graphStar_boundary_direction_mem s hp hB (-reference)
    (by simpa only [norm_neg] using href) (by simp [href1])
  refine ⟨i₀, i₁, ?_, h₀, h₁, ?_⟩
  · intro he
    have h := h₀.symm.trans ((congrArg s.direction he).trans h₁)
    have := congrArg (fun v : Plane => v 0) h
    norm_num [reference] at this
  · intro i
    refine ⟨graphStar_direction_second_nonneg s hp i, ?_⟩
    constructor
    · intro hi
      have hn := congrArg (fun r : ℝ => r ^ 2) (s.direction_unit i)
      rw [EuclideanSpace.norm_sq_eq] at hn
      simp only [Fin.sum_univ_two, hi, mul_zero, sq, one_mul, add_zero,
        Real.norm_eq_abs, abs_mul_abs_self] at hn
      have hx : s.direction i 0 = 1 ∨ s.direction i 0 = -1 := by
        have hf : (s.direction i 0 - 1) * (s.direction i 0 + 1) = 0 := by nlinarith
        rcases mul_eq_zero.mp hf with hf | hf
        · exact Or.inl (by linarith)
        · exact Or.inr (by linarith)
      rcases hx with hx | hx
      · left
        apply s.direction_injective
        rw [h₀]
        ext j
        fin_cases j <;> simp [reference, hx, hi]
      · right
        apply s.direction_injective
        rw [h₁]
        ext j
        fin_cases j <;> simp [reference, hx, hi]
    · rintro (rfl | rfl) <;> simp [h₀, h₁, href1]

/-- Boundary containment forces at least two distinct incident rays. -/
lemma graphStar_boundary_two_le_rayCount (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) (hB : intrinsicBoundary S ⊆ G.carrier) :
    2 ≤ s.rayCount := by
  obtain ⟨i₀, i₁, hne, _⟩ := graphStar_boundary_rays s hp hB
  by_contra h
  have hn : s.rayCount ≤ 1 := by omega
  have he : i₀ = i₁ := by apply Fin.ext; omega
  exact hne he
end BoundaryStarDirections
lemma exists_adjacent {n : ℕ} (c : Fin (n + 1) → ℝ)
    (hc : StrictMono c) {x : ℝ} (hx : c 0 < x ∧ x < c (Fin.last n))
    (hne : ∀ i, x ≠ c i) :
    ∃ i : Fin n, x ∈ Ioo (c i.castSucc) (c i.succ) := by
  classical
  have hex : ∃ i, x < c i := ⟨Fin.last n, hx.2⟩
  let j := Fin.find (fun i => x < c i) hex
  have hj : x < c j := Fin.find_spec hex
  have hj0 : j ≠ 0 := by
    intro h
    rw [h] at hj
    linarith [hx.1]
  let i := j.pred hj0
  refine ⟨i, ?_, ?_⟩
  · have hlt : i.castSucc < j := by
      rw [← Fin.succ_pred j hj0]
      exact Fin.castSucc_lt_succ
    have hn := Fin.find_min hex hlt
    change ¬ x < c i.castSucc at hn
    exact lt_of_le_of_ne (le_of_not_gt hn) (hne _).symm
  · simpa only [i, Fin.succ_pred] using hj

lemma disjoint_adjacent {n : ℕ} (c : Fin (n + 1) → ℝ) (hc : StrictMono c) :
    Pairwise (fun i j : Fin n => Disjoint (Ioo (c i.castSucc) (c i.succ))
      (Ioo (c j.castSucc) (c j.succ))) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro x hx hy
  rcases lt_or_gt_of_ne hij with h | h
  · have hle : i.succ ≤ j.castSucc := by exact_mod_cast h
    exact (not_lt_of_ge (hc.monotone hle)) (lt_trans hy.1 hx.2)
  · have hle : j.succ ≤ i.castSucc := by exact_mod_cast h
    exact (not_lt_of_ge (hc.monotone hle)) (lt_trans hx.1 hy.2)

lemma componentSet_mk {X : Type*} [TopologicalSpace X] (U : Set X) (x : U) :
    componentSet U (ConnectedComponents.mk x) = connectedComponentIn U x.val := by
  unfold componentSet
  rw [connectedComponentIn_eq_image x.property]
  apply congrArg (fun t : Set U => Subtype.val '' t)
  ext y
  exact @ConnectedComponents.coe_eq_coe' U _ y x

lemma exists_components_equiv {X : Type*} [TopologicalSpace X] (U : Set X)
    {ι : Type*} (C : ι → Set X) (hn : ∀ i, (C i).Nonempty)
    (hsub : ∀ i, C i ⊆ U)
    (hdis : Pairwise (fun i j => Disjoint (C i) (C j)))
    (hcover : ∀ x ∈ U, ∃ i, x ∈ C i)
    (hcomp : ∀ i x, x ∈ C i → connectedComponentIn U x = C i) :
    ∃ E : ConnectedComponents U ≃ ι, ∀ a, componentSet U a = C (E a) := by
  classical
  choose p hp using hn
  let q (i : ι) : U := ⟨p i, hsub i (hp i)⟩
  let f (i : ι) : ConnectedComponents U := ConnectedComponents.mk (q i)
  have hf (i : ι) : componentSet U (f i) = C i :=
    (componentSet_mk U (q i)).trans (hcomp i (p i) (hp i))
  have hinj : Function.Injective f := by
    intro i j hij
    by_contra hne
    have hC : C i = C j := (hf i).symm.trans ((congrArg (componentSet U) hij).trans (hf j))
    exact (Set.disjoint_left.mp (hdis hne)) (hp i) (hC ▸ hp i)
  have hsur : Function.Surjective f := by
    intro a
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    obtain ⟨i, hi⟩ := hcover x x.property
    refine ⟨i, ?_⟩
    apply ConnectedComponents.coe_eq_coe'.mpr
    have hmem : x.val ∈ connectedComponentIn U (p i) := by
      rw [hcomp i _ (hp i)]
      exact hi
    rw [connectedComponentIn_eq_image (q i).property] at hmem
    obtain ⟨y, hy, he⟩ := hmem
    have hyx : y = x := Subtype.ext he
    subst y
    exact (connectedComponent_eq hy).symm ▸ mem_connectedComponent
  let E := Equiv.ofBijective f ⟨hinj, hsur⟩
  refine ⟨E.symm, ?_⟩
  intro a
  have H := hf (E.symm a)
  rw [show f (E.symm a) = a from E.apply_symm_apply a] at H
  exact H


section RadialSectorTopology
open Complex
open scoped Real _root_.Topology
namespace AngularSector



lemma norm_polar {p : ℝ × ℝ} (hp : 0 < p.1) : ‖polar p‖ = p.1 := by
  simp [polar, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp,
    Complex.norm_exp_ofReal_mul_I]

lemma arg_polar {p : ℝ × ℝ} (hp : 0 < p.1) (hθ : p.2 ∈ Ioc (-Real.pi) Real.pi) :
    arg (polar p) = p.2 := by
  rw [polar, Complex.arg_real_mul _ hp, Complex.exp_mul_I]
  exact Complex.arg_cos_add_sin_mul_I hθ

lemma sector_eq_polar_image {r a b : ℝ} (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) :
    sector r a b = polar '' (Ioo 0 r ×ˢ Ioo a b) := by
  ext z
  constructor
  · rintro ⟨hz, hr, hθ⟩
    refine ⟨(‖z‖, arg z), ⟨⟨norm_pos_iff.mpr hz, hr⟩, hθ⟩, ?_⟩
    exact Complex.norm_mul_exp_arg_mul_I z
  · rintro ⟨p, ⟨hp, hθ⟩, rfl⟩
    have hn := norm_polar hp.1
    refine ⟨norm_ne_zero_iff.mp (by rw [hn]; exact hp.1.ne'), ?_, ?_⟩
    · rw [hn]
      exact hp.2
    · rw [arg_polar hp.1 ⟨lt_of_le_of_lt ha hθ.1, le_trans hθ.2.le hb⟩]
      exact hθ

lemma continuous_polar : Continuous polar := by
  unfold polar
  fun_prop

lemma isPreconnected_sector {r a b : ℝ} (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi) :
    IsPreconnected (sector r a b) := by
  rw [sector_eq_polar_image ha hb]
  exact (isPreconnected_Ioo.prod isPreconnected_Ioo).image _ continuous_polar.continuousOn

lemma sector_subset_slitPlane {r a b : ℝ} (hb : b ≤ Real.pi) :
    sector r a b ⊆ Complex.slitPlane := by
  rintro z ⟨hz, hr, hθ⟩
  rw [Complex.mem_slitPlane_iff_arg]
  exact ⟨ne_of_lt (lt_of_lt_of_le hθ.2 hb), hz⟩

/-- A sector with no missing rays is exactly one actual component.  The
endpoint exclusions are obtained from the neighboring removed rays; they are
also automatic for endpoints -pi and pi. -/
lemma connectedComponentIn_eq_sector {U : Set ℂ} {r a b : ℝ} {x : ℂ}
    (ha : -Real.pi ≤ a) (hb : b ≤ Real.pi)
    (hslit : U ⊆ Complex.slitPlane) (hnorm : ∀ z ∈ U, ‖z‖ < r)
    (hexcl_a : ∀ z ∈ U, arg z ≠ a) (hexcl_b : ∀ z ∈ U, arg z ≠ b)
    (hfill : sector r a b ⊆ U) (hx : x ∈ sector r a b) :
    connectedComponentIn U x = sector r a b := by
  have hsubset := connectedComponentIn_subset U x
  have hconn : IsPreconnected (connectedComponentIn U x) :=
    isPreconnected_connectedComponentIn
  have hcont : ContinuousOn arg (connectedComponentIn U x) :=
    Complex.continuousOn_arg.mono (hsubset.trans hslit)
  have hxc : x ∈ connectedComponentIn U x := mem_connectedComponentIn (hfill hx)
  apply Subset.antisymm
  · intro z hz
    refine ⟨Complex.slitPlane_ne_zero (hslit (hsubset hz)), hnorm z (hsubset hz), ?_, ?_⟩
    · exact hconn.lt_of_ne hcont (fun z hz => hexcl_a z (hsubset hz)) ⟨x, hxc, hx.2.2.1⟩ hz
    · exact hconn.gt_of_ne hcont (fun z hz => hexcl_b z (hsubset hz)) ⟨x, hxc, hx.2.2.2⟩ hz
  · exact (isPreconnected_sector ha hb).subset_connectedComponentIn hx hfill


/-- Removed finite rays determine all the actual components, after selecting
neighbors in the sorted argument list. No sector/corner incidence is assumed. -/
lemma rayComplement_component_eq_sector {ι : Type*} {r a b : ℝ}
    (d : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (hcut : ∃ i, arg (d i) = Real.pi)
    (ha : a = -Real.pi ∨ ∃ i, a = arg (d i))
    (hb : ∃ i, b = arg (d i))
    (hgap : ∀ i, arg (d i) ∉ Ioo a b)
    {x : ℂ} (hx : x ∈ sector r a b) :
    connectedComponentIn (rayComplement r d) x = sector r a b := by
  have ha' : -Real.pi ≤ a := by
    rcases ha with rfl | ⟨i, rfl⟩
    · exact le_rfl
    · exact (Complex.neg_pi_lt_arg _).le
  have hb' : b ≤ Real.pi := by
    obtain ⟨i, rfl⟩ := hb
    exact Complex.arg_le_pi _
  have hno (z : ℂ) (hz : z ∈ rayComplement r d) (i : ι) : arg z ≠ arg (d i) := by
    intro h
    exact hz.2.2 i (Complex.sameRay_of_arg_eq h)
  apply connectedComponentIn_eq_sector ha' hb' ?_ (fun z hz => hz.2.1) ?_ ?_ ?_ hx
  · intro z hz
    rw [Complex.mem_slitPlane_iff_arg]
    obtain ⟨i, hi⟩ := hcut
    exact ⟨fun h => hno z hz i (h.trans hi.symm), hz.1⟩
  · intro z hz
    rcases ha with rfl | ⟨i, rfl⟩
    · exact (Complex.neg_pi_lt_arg _).ne'
    · exact hno z hz i
  · intro z hz
    obtain ⟨i, rfl⟩ := hb
    exact hno z hz i
  · intro z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    intro i hi
    have he : arg z = arg (d i) :=
      (Complex.sameRay_iff.mp hi).resolve_left hz.1 |>.resolve_left (hd i)
    exact hgap i (he ▸ hz.2.2)

/-- Every point in a finite ray complement lies in a unique neighboring
argument gap, and that gap is its actual connected component. -/
lemma exists_rayComplement_component_sector {ι : Type*} [Fintype ι] {r : ℝ}
    (d : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (hcut : ∃ i, arg (d i) = Real.pi) {x : ℂ}
    (hx : x ∈ rayComplement r d) :
    ∃ a b : ℝ, a < arg x ∧ arg x < b ∧
      (a = -Real.pi ∨ ∃ i, a = arg (d i)) ∧
      (∃ i, b = arg (d i)) ∧
      (∀ i, arg (d i) ∉ Ioo a b) ∧
      connectedComponentIn (rayComplement r d) x = sector r a b := by
  classical
  let cuts : Finset ℝ := insert (-Real.pi) (Finset.univ.image (fun i => arg (d i)))
  let below := cuts.filter (fun t => t < arg x)
  let above := cuts.filter (fun t => arg x < t)
  have hnox (i : ι) : arg x ≠ arg (d i) := by
    intro h
    exact hx.2.2 i (Complex.sameRay_of_arg_eq h)
  have hbelow : below.Nonempty := by
    refine ⟨-Real.pi, Finset.mem_filter.mpr ⟨?_, Complex.neg_pi_lt_arg _⟩⟩
    exact Finset.mem_insert_self _ _
  have habove : above.Nonempty := by
    obtain ⟨i, hi⟩ := hcut
    refine ⟨Real.pi, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
    · exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩)
    · exact (Complex.arg_le_pi x).lt_of_ne (fun h => hnox i (h.trans hi.symm))
  let a := below.max' hbelow
  let b := above.min' habove
  have ha := Finset.mem_filter.mp (Finset.max'_mem below hbelow)
  have hb := Finset.mem_filter.mp (Finset.min'_mem above habove)
  change a ∈ cuts ∧ a < arg x at ha
  change b ∈ cuts ∧ arg x < b at hb
  have hleft : a = -Real.pi ∨ ∃ i, a = arg (d i) := by
    rcases Finset.mem_insert.mp ha.1 with h | h
    · exact Or.inl h
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact Or.inr ⟨i, hi.symm⟩
  have hright : ∃ i, b = arg (d i) := by
    rcases Finset.mem_insert.mp hb.1 with h | h
    · have := Complex.neg_pi_lt_arg x
      linarith [hb.2]
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact ⟨i, hi.symm⟩
  have hgap : ∀ i, arg (d i) ∉ Ioo a b := by
    intro i hi
    rcases lt_or_gt_of_ne (hnox i).symm with h | h
    · have hm : arg (d i) ∈ below := Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), h⟩
      have hle : arg (d i) ≤ a := Finset.le_max' below _ hm
      exact (not_lt_of_ge hle) hi.1
    · have hm : arg (d i) ∈ above := Finset.mem_filter.mpr
        ⟨Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩), h⟩
      have hle : b ≤ arg (d i) := Finset.min'_le above _ hm
      exact (not_lt_of_ge hle) hi.2
  refine ⟨a, b, ha.2, hb.2, hleft, hright, hgap, ?_⟩
  exact rayComplement_component_eq_sector d hd hcut hleft hright hgap
    ⟨hx.1, hx.2.1, ha.2, hb.2⟩

lemma unit_mul_mem_rayComplement_iff {ι : Type*} (d : ι → ℂ) (c : ℂ)
    (hc : ‖c‖ = 1) (r : ℝ) (z : ℂ) :
    c * z ∈ rayComplement r (fun i => c * d i) ↔ z ∈ rayComplement r d := by
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
  have hsame (i : ι) : SameRay ℝ (c * z) (c * d i) ↔ SameRay ℝ z (d i) := by
    exact Function.Injective.sameRay_map_iff (f := LinearMap.mulLeft ℝ c)
      (mul_right_injective₀ hc0)
  simp only [rayComplement, mem_ofPred_eq, mul_ne_zero_iff,
    norm_mul, hc, one_mul, hsame]
  simp [hc0]

/-- An arbitrary nonempty finite family of unit rays has genuine angular-gap
components. The branch cut is constructed from a selected removed ray. -/
lemma exists_rotated_component_sector {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (hd : ∀ i, ‖d i‖ = 1) (i₀ : ι) {r : ℝ} {x : ℂ}
    (hx : x ∈ rayComplement r d) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * d i₀ = -1 ∧
      ∃ a b : ℝ, a < arg (c * x) ∧ arg (c * x) < b ∧
        ((fun z => c * z) '' connectedComponentIn (rayComplement r d) x) = sector r a b := by
  let c : ℂ := -star (d i₀)
  have hc : ‖c‖ = 1 := by simp [c, hd]
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
  have hbase : c * d i₀ = -1 := by
    dsimp [c]
    rw [neg_mul]
    change -(starRingEnd ℂ (d i₀) * d i₀) = -1
    rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hd]
    norm_num
  have hdn (i : ι) : c * d i ≠ 0 := mul_ne_zero hc0
    (norm_ne_zero_iff.mp ((hd i).trans_ne one_ne_zero))
  have hcut : ∃ i, arg (c * d i) = Real.pi := ⟨i₀, by rw [hbase, Complex.arg_neg_one]⟩
  have hx' := (unit_mul_mem_rayComplement_iff d c hc r x).mpr hx
  obtain ⟨a, b, ha, hb, _, _, _, hcomp⟩ :=
    exists_rayComplement_component_sector (fun i => c * d i) hdn hcut hx'
  refine ⟨c, hc, hbase, a, b, ha, hb, ?_⟩
  let H : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c hc0
  have himage : H '' rayComplement r d = rayComplement r (fun i => c * d i) := by
    ext z
    obtain ⟨y, rfl⟩ := H.surjective z
    rw [H.injective.mem_set_image]
    exact (unit_mul_mem_rayComplement_iff d c hc r y).symm
  change H '' connectedComponentIn (rayComplement r d) x = _
  rw [H.image_connectedComponentIn hx, himage]
  exact hcomp


/-- In the upper half-plane with both genuine boundary rays removed, each
actual local component is one positive argument interval between neighboring
rays. Interior rays remain completely arbitrary. -/
lemma exists_upperRayComplement_component_sector {ι : Type*} [Fintype ι]
    (d : ι → ℂ) (hd : ∀ i, d i ≠ 0)
    (hleft : ∃ i, arg (d i) = 0) (hright : ∃ i, arg (d i) = Real.pi)
    {r : ℝ} {x : ℂ} (hx : x ∈ upperRayComplement r d) :
    ∃ a b : ℝ, 0 ≤ a ∧ b ≤ Real.pi ∧ a < arg x ∧ arg x < b ∧
      connectedComponentIn (upperRayComplement r d) x = sector r a b := by
  obtain ⟨a, b, ha, hb, hamin, hbmax, hgap, hcomp⟩ :=
    exists_rayComplement_component_sector d hd hright hx.1
  have ha0 : 0 ≤ a := by
    by_contra h
    have ha0 := lt_of_not_ge h
    obtain ⟨i, hi⟩ := hleft
    apply hgap i
    rw [hi]
    exact ⟨ha0, lt_trans hx.2 hb⟩
  have hbpi : b ≤ Real.pi := by
    obtain ⟨i, rfl⟩ := hbmax
    exact Complex.arg_le_pi _
  have hfill : sector r a b ⊆ upperRayComplement r d := by
    intro z hz
    have hzfull : z ∈ rayComplement r d := by
      rw [← hcomp] at hz
      exact connectedComponentIn_subset _ _ hz
    exact ⟨hzfull, lt_of_le_of_lt ha0 hz.2.2.1⟩
  have hslit : upperRayComplement r d ⊆ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff_arg]
    obtain ⟨i, hi⟩ := hright
    refine ⟨?_, hz.1.1⟩
    intro he
    exact hz.1.2.2 i (Complex.sameRay_of_arg_eq (he.trans hi.symm))
  have hexcl (z : ℂ) (hz : z ∈ upperRayComplement r d) (i : ι) : arg z ≠ arg (d i) := by
    intro he
    exact hz.1.2.2 i (Complex.sameRay_of_arg_eq he)
  refine ⟨a, b, ha0, hbpi, ha, hb, ?_⟩
  apply connectedComponentIn_eq_sector (le_trans (by linarith [Real.pi_pos]) ha0)
    hbpi hslit (fun z hz => hz.1.2.1) ?_ ?_ hfill ⟨hx.1.1, hx.1.2.1, ha, hb⟩
  · intro z hz
    rcases hamin with rfl | ⟨i, rfl⟩
    · exact (Complex.neg_pi_lt_arg _).ne'
    · exact hexcl z hz i
  · intro z hz
    obtain ⟨i, rfl⟩ := hbmax
    exact hexcl z hz i

lemma exists_indexed_sectors {n : ℕ} {U : Set ℂ} {r : ℝ} (hr : 0 < r)
    (c : Fin (n + 1) → ℝ) (hc : StrictMono c)
    (ha : -Real.pi ≤ c 0) (hb : c (Fin.last n) ≤ Real.pi)
    (hslit : U ⊆ Complex.slitPlane) (hnorm : ∀ z ∈ U, ‖z‖ < r)
    (hexcl : ∀ z ∈ U, ∀ k, arg z ≠ c k)
    (hrange : ∀ z ∈ U, c 0 < arg z ∧ arg z < c (Fin.last n))
    (hfill : ∀ i : Fin n, sector r (c i.castSucc) (c i.succ) ⊆ U) :
    ∃ E : ConnectedComponents U ≃ Fin n,
      ∀ a, componentSet U a = sector r (c (E a).castSucc) (c (E a).succ) := by
  let C (i : Fin n) := sector r (c i.castSucc) (c i.succ)
  have hbounds (i : Fin n) : -Real.pi ≤ c i.castSucc ∧ c i.succ ≤ Real.pi :=
    ⟨ha.trans (hc.monotone (Fin.zero_le _)), (hc.monotone (Fin.le_last _)).trans hb⟩
  have hcomp (i : Fin n) (x : ℂ) (hx : x ∈ C i) : connectedComponentIn U x = C i :=
    connectedComponentIn_eq_sector (hbounds i).1 (hbounds i).2 hslit hnorm
      (fun z hz => hexcl z hz _) (fun z hz => hexcl z hz _) (hfill i) hx
  apply exists_components_equiv U C ?_ hfill ?_ ?_ hcomp
  · intro i
    have hab := hc (Fin.castSucc_lt_succ (i := i))
    have hmid : (c i.castSucc + c i.succ) / 2 ∈ Ioo (c i.castSucc) (c i.succ) := by
      constructor <;> linarith
    rw [show C i = polar '' (Ioo 0 r ×ˢ Ioo (c i.castSucc) (c i.succ)) from
      sector_eq_polar_image (hbounds i).1 (hbounds i).2]
    exact Set.image_nonempty.mpr ⟨(r / 2, (c i.castSucc + c i.succ) / 2),
      ⟨by constructor <;> linarith, hmid⟩⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro x hx hy
    exact Set.disjoint_left.mp (disjoint_adjacent c hc hij) hx.2.2 hy.2.2
  · intro x hx
    obtain ⟨i, hi⟩ := exists_adjacent c hc (hrange x hx) (hexcl x hx)
    exact ⟨i, Complex.slitPlane_ne_zero (hslit hx), hnorm x hx, hi⟩


lemma args_injective {n : ℕ} (d : Fin n → ℂ) (hd : Function.Injective d)
    (hu : ∀ i, ‖d i‖ = 1) : Function.Injective (fun i => arg (d i)) := by
  intro i j hij
  apply hd
  exact (Complex.sameRay_of_arg_eq hij).eq_of_norm_eq (by rw [hu, hu])

lemma no_cut_in_gap {n : ℕ} (c : Fin (n + 1) → ℝ) (hc : StrictMono c)
    (i : Fin n) (j : Fin (n + 1)) : c j ∉ Ioo (c i.castSucc) (c i.succ) := by
  intro h
  have h1 := hc.lt_iff_lt.mp h.1
  have h2 := hc.lt_iff_lt.mp h.2
  have := i.isLt
  simp only [Fin.lt_def, Fin.val_castSucc, Fin.val_succ] at h1 h2
  omega

/-- Sorted genuine removed rays, with the chosen ray at the branch cut,
index every component exactly once, even for a single removed ray. -/
lemma exists_rayComplement_components {n : ℕ} {r : ℝ} (hr : 0 < r)
    (d : Fin (n + 1) → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (hcut : ∃ i, arg (d i) = Real.pi) :
    ∃ e : Equiv.Perm (Fin (n + 1)),
      let c : Fin (n + 2) → ℝ := Fin.cons (-Real.pi) (fun i => arg (d (e i)))
      StrictMono c ∧ c (Fin.last (n + 1)) = Real.pi ∧
      ∃ E : ConnectedComponents (rayComplement r d) ≃ Fin (n + 1),
        ∀ a, componentSet (rayComplement r d) a =
          sector r (c (E a).castSucc) (c (E a).succ) := by
  obtain ⟨e, he⟩ := exists_sorting_equiv (fun i => arg (d i)) (args_injective d hd hu)
  let c : Fin (n + 2) → ℝ := Fin.cons (-Real.pi) (fun i => arg (d (e i)))
  have hc : StrictMono c := Fin.strictMono_cons.mpr
    ⟨fun i => Complex.neg_pi_lt_arg _, he⟩
  have hlast : c (Fin.last (n + 1)) = Real.pi := by
    obtain ⟨i, hi⟩ := hcut
    have hle := he.monotone (Fin.le_last (e.symm i))
    change arg (d (e (e.symm i))) ≤ arg (d (e (Fin.last n))) at hle
    rw [e.apply_symm_apply, hi] at hle
    change arg (d (e (Fin.last n))) = Real.pi
    exact le_antisymm (Complex.arg_le_pi _) hle
  have hexcl (z : ℂ) (hz : z ∈ rayComplement r d) (j : Fin (n + 2)) : arg z ≠ c j := by
    refine Fin.cases ?_ (fun k => ?_) j
    · exact (Complex.neg_pi_lt_arg z).ne'
    · intro hj
      exact hz.2.2 (e k) (Complex.sameRay_of_arg_eq hj)
  have hslit : rayComplement r d ⊆ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff_arg]
    exact ⟨by simpa only [hlast] using hexcl z hz (Fin.last (n + 1)), hz.1⟩
  refine ⟨e, hc, hlast, ?_⟩
  apply exists_indexed_sectors hr c hc (by simp [c]) hlast.le hslit
    (fun z hz => hz.2.1) hexcl ?_ ?_
  · intro z hz
    constructor
    · exact Complex.neg_pi_lt_arg _
    · rw [hlast]
      exact (Complex.arg_le_pi _).lt_of_ne (by simpa only [hlast] using hexcl z hz (Fin.last (n + 1)))
  · intro i z hz
    refine ⟨hz.1, hz.2.1, ?_⟩
    intro j hj
    have hd0 : d j ≠ 0 := norm_ne_zero_iff.mp ((hu j).trans_ne one_ne_zero)
    have harg : arg z = arg (d j) :=
      (Complex.sameRay_iff.mp hj).resolve_left hz.1 |>.resolve_left hd0
    apply no_cut_in_gap c hc i (e.symm j).succ
    simpa only [c, Fin.cons_succ, e.apply_symm_apply, ← harg] using hz.2.2



lemma exists_upperRayComplement_components {n : ℕ} {r : ℝ} (hr : 0 < r)
    (d : Fin (n + 2) → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (hhalf : ∀ i, 0 ≤ (d i).im)
    (hleft : ∃ i, arg (d i) = 0) (hright : ∃ i, arg (d i) = Real.pi) :
    ∃ e : Equiv.Perm (Fin (n + 2)),
      let c := fun i => arg (d (e i))
      StrictMono c ∧ c 0 = 0 ∧ c (Fin.last (n + 1)) = Real.pi ∧
      ∃ E : ConnectedComponents (upperRayComplement r d) ≃ Fin (n + 1),
        ∀ a, componentSet (upperRayComplement r d) a =
          sector r (c (E a).castSucc) (c (E a).succ) := by
  obtain ⟨e, he⟩ := exists_sorting_equiv (fun i => arg (d i)) (args_injective d hd hu)
  let c := fun i => arg (d (e i))
  have hc : StrictMono c := he
  have hfirst : c 0 = 0 := by
    obtain ⟨i, hi⟩ := hleft
    have hle := he.monotone (Fin.zero_le (e.symm i))
    change arg (d (e 0)) ≤ arg (d (e (e.symm i))) at hle
    rw [e.apply_symm_apply, hi] at hle
    exact le_antisymm hle (Complex.arg_nonneg_iff.mpr (hhalf (e 0)))
  have hlast : c (Fin.last (n + 1)) = Real.pi := by
    obtain ⟨i, hi⟩ := hright
    have hle := he.monotone (Fin.le_last (e.symm i))
    change arg (d (e (e.symm i))) ≤ arg (d (e (Fin.last (n + 1)))) at hle
    rw [e.apply_symm_apply, hi] at hle
    exact le_antisymm (Complex.arg_le_pi _) hle
  have hexcl (z : ℂ) (hz : z ∈ upperRayComplement r d) (j : Fin (n + 2)) : arg z ≠ c j := by
    intro hj
    exact hz.1.2.2 (e j) (Complex.sameRay_of_arg_eq hj)
  have hslit : upperRayComplement r d ⊆ Complex.slitPlane := by
    intro z hz
    rw [Complex.mem_slitPlane_iff_arg]
    exact ⟨by simpa only [hlast] using hexcl z hz (Fin.last (n + 1)), hz.1.1⟩
  refine ⟨e, hc, hfirst, hlast, ?_⟩
  apply exists_indexed_sectors hr c hc (by rw [hfirst]; linarith [Real.pi_pos])
    hlast.le hslit (fun z hz => hz.1.2.1) hexcl ?_ ?_
  · intro z hz
    constructor
    · rw [hfirst]; exact hz.2
    · rw [hlast]
      exact (Complex.arg_le_pi _).lt_of_ne
        (by simpa only [hlast] using hexcl z hz (Fin.last (n + 1)))
  · intro i z hz
    refine ⟨⟨hz.1, hz.2.1, ?_⟩, ?_⟩
    · intro j hj
      have hd0 : d j ≠ 0 := norm_ne_zero_iff.mp ((hu j).trans_ne one_ne_zero)
      have harg : arg z = arg (d j) :=
        (Complex.sameRay_iff.mp hj).resolve_left hz.1 |>.resolve_left hd0
      apply no_cut_in_gap c hc i (e.symm j)
      simpa only [c, e.apply_symm_apply, ← harg] using hz.2.2
    · have h0 := hc.monotone (Fin.zero_le i.castSucc)
      rw [hfirst] at h0
      exact lt_of_le_of_lt h0 hz.2.2.1


lemma isConnected_rayComplement_zero {r : ℝ} (hr : 0 < r) (d : Fin 0 → ℂ) :
    IsConnected (rayComplement r d) := by
  have heq : rayComplement r d = polar '' (Ioo 0 r ×ˢ (univ : Set ℝ)) := by
    ext z
    constructor
    · rintro ⟨hz, hnorm, _⟩
      exact ⟨(‖z‖, arg z), ⟨⟨norm_pos_iff.mpr hz, hnorm⟩, trivial⟩,
        Complex.norm_mul_exp_arg_mul_I z⟩
    · rintro ⟨p, ⟨hp, _⟩, rfl⟩
      refine ⟨?_, ?_, fun i => Fin.elim0 i⟩
      · exact norm_ne_zero_iff.mp (by rw [norm_polar hp.1]; exact hp.1.ne')
      · rw [norm_polar hp.1]; exact hp.2
  rw [heq]
  apply IsConnected.image ?_ _ continuous_polar.continuousOn
  apply IsConnected.prod ?_ isConnected_univ
  exact ⟨⟨r / 2, by constructor <;> linarith⟩, isPreconnected_Ioo⟩

lemma rayComplement_zero_components {r : ℝ} (hr : 0 < r) (d : Fin 0 → ℂ) :
    Nonempty (ConnectedComponents (rayComplement r d) ≃ Fin 1) := by
  letI : ConnectedSpace (rayComplement r d) :=
    isConnected_iff_connectedSpace.mp (isConnected_rayComplement_zero hr d)
  letI : Unique (ConnectedComponents (rayComplement r d)) := (nonempty_unique _).some
  exact ⟨Equiv.ofUnique _ _⟩

end AngularSector
end RadialSectorTopology
section GraphStarImages
namespace GraphStarImage

variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .euclidean M}
  {G : EmbeddedGraph S} {p : M}


lemma graphStar_centered_image (s : GraphStar G p) :
    (fun x => coordinates s.chart x - coordinates s.chart p) ''
      (s.neighborhood \ G.carrier) = planeRayComplement s.radius s.direction := by
  ext z
  constructor
  · rintro ⟨x, ⟨⟨hxs, hxb⟩, hxG⟩, rfl⟩
    have hxn : x ≠ p := by
      intro he
      apply hxG
      exact (s.graph_eq x hxs hxb).mpr (Or.inl he)
    have hzn : coordinates s.chart x - coordinates s.chart p ≠ 0 := by
      intro he
      have hcoord := sub_eq_zero.mp he
      apply hxn
      exact s.chart.injOn hxs s.mem_source
        (Subtype.ext (toPlane.injective hcoord))
    refine ⟨hzn, ?_, ?_⟩
    · exact hxb
    · intro i hi
      have hd : s.direction i ≠ 0 :=
        norm_ne_zero_iff.mp ((s.direction_unit i).trans_ne one_ne_zero)
      obtain ⟨t, ht, he⟩ := hi.exists_pos_right hzn hd
      have htlt : t < s.radius := by
        have hn := congrArg norm he
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, s.direction_unit, mul_one] at hn
        have hb : ‖coordinates s.chart x - coordinates s.chart p‖ < s.radius := hxb
        rwa [hn] at hb
      apply hxG
      apply (s.graph_eq x hxs hxb).mpr
      right
      refine ⟨i, t, ht, htlt, ?_⟩
      exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  · intro hz
    have hmodel : toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 .euclidean := by
      trivial
    let w : ModelSpace 2 .euclidean :=
      ⟨toPlane.symm (coordinates s.chart p + z), hmodel⟩
    have hwball : toPlane w.val ∈ Metric.ball (coordinates s.chart p) s.radius := by
      simpa only [w, toPlane.apply_symm_apply, Metric.mem_ball, dist_eq_norm,
        add_sub_cancel_left] using hz.2.1
    have hwt := s.ball_in_target w hwball
    let x := s.chart.symm w
    have hxs : x ∈ s.chart.source := s.chart.map_target hwt
    have hcoord : coordinates s.chart x = coordinates s.chart p + z := by
      change toPlane (s.chart (s.chart.symm w)).val = _
      rw [s.chart.right_inv hwt]
      exact toPlane.apply_symm_apply _
    have hxb : coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius := by
      rwa [hcoord]
    refine ⟨x, ⟨⟨hxs, hxb⟩, ?_⟩, ?_⟩
    · intro hxG
      obtain he | ⟨i, t, ht, htlt, he⟩ := (s.graph_eq x hxs hxb).mp hxG
      · apply hz.1
        rw [he] at hcoord
        exact (add_eq_left.mp hcoord.symm)
      · have heq : z = t • s.direction i := add_left_cancel (hcoord.symm.trans he)
        apply hz.2.2 i
        rw [heq]
        exact SameRay.sameRay_pos_smul_left _ ht
    · change coordinates s.chart x - coordinates s.chart p = z
      rw [hcoord, add_sub_cancel_left]

end GraphStarImage

end GraphStarImages

section GraphStarModelImages
open SmoothManifolds.BoundaryData
namespace GraphStarModelImage
open GraphStarImage (planeRayComplement)

variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M}
  {G : EmbeddedGraph S} {p : M}

lemma graphStar_centered_image_model (s : GraphStar G p) :
    (fun x => coordinates s.chart x - coordinates s.chart p) ''
      (s.neighborhood \ G.carrier) =
        {z | toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind} ∩
          planeRayComplement s.radius s.direction := by
  ext z
  constructor
  · rintro ⟨x, ⟨⟨hxs, hxb⟩, hxG⟩, rfl⟩
    have hxn : x ≠ p := by
      intro he
      apply hxG
      exact (s.graph_eq x hxs hxb).mpr (Or.inl he)
    have hzn : coordinates s.chart x - coordinates s.chart p ≠ 0 := by
      intro he
      have hcoord := sub_eq_zero.mp he
      apply hxn
      exact s.chart.injOn hxs s.mem_source
        (Subtype.ext (toPlane.injective hcoord))
    refine ⟨?_, hzn, ?_, ?_⟩
    · change toPlane.symm (coordinates s.chart p +
        (coordinates s.chart x - coordinates s.chart p)) ∈ modelSet 2 kind
      rw [add_comm, sub_add_cancel]
      simp only [coordinates, toPlane.symm_apply_apply]
      exact (s.chart x).property
    · exact hxb
    · intro i hi
      have hd : s.direction i ≠ 0 :=
        norm_ne_zero_iff.mp ((s.direction_unit i).trans_ne one_ne_zero)
      obtain ⟨t, ht, he⟩ := hi.exists_pos_right hzn hd
      have htlt : t < s.radius := by
        have hn := congrArg norm he
        simp only [norm_smul, Real.norm_eq_abs, abs_of_pos ht, s.direction_unit, mul_one] at hn
        have hb : ‖coordinates s.chart x - coordinates s.chart p‖ < s.radius := hxb
        rwa [hn] at hb
      apply hxG
      apply (s.graph_eq x hxs hxb).mpr
      right
      refine ⟨i, t, ht, htlt, ?_⟩
      exact sub_eq_iff_eq_add.mp he |>.trans (add_comm _ _)
  · rintro ⟨hmodel, hz⟩
    let w : ModelSpace 2 kind :=
      ⟨toPlane.symm (coordinates s.chart p + z), hmodel⟩
    have hwball : toPlane w.val ∈ Metric.ball (coordinates s.chart p) s.radius := by
      simpa only [w, toPlane.apply_symm_apply, Metric.mem_ball, dist_eq_norm,
        add_sub_cancel_left] using hz.2.1
    have hwt := s.ball_in_target w hwball
    let x := s.chart.symm w
    have hxs : x ∈ s.chart.source := s.chart.map_target hwt
    have hcoord : coordinates s.chart x = coordinates s.chart p + z := by
      change toPlane (s.chart (s.chart.symm w)).val = _
      rw [s.chart.right_inv hwt]
      exact toPlane.apply_symm_apply _
    have hxb : coordinates s.chart x ∈ Metric.ball (coordinates s.chart p) s.radius := by
      rwa [hcoord]
    refine ⟨x, ⟨⟨hxs, hxb⟩, ?_⟩, ?_⟩
    · intro hxG
      obtain he | ⟨i, t, ht, htlt, he⟩ := (s.graph_eq x hxs hxb).mp hxG
      · apply hz.1
        rw [he] at hcoord
        exact (add_eq_left.mp hcoord.symm)
      · have heq : z = t • s.direction i := add_left_cancel (hcoord.symm.trans he)
        apply hz.2.2 i
        rw [heq]
        exact SameRay.sameRay_pos_smul_left _ ht
    · change coordinates s.chart x - coordinates s.chart p = z
      rw [hcoord, add_sub_cancel_left]

section Boundary
variable {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
  {G : EmbeddedGraph S} {p : M}

lemma graphStar_centered_image_halfSpace (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) :
    (fun x => coordinates s.chart x - coordinates s.chart p) ''
      (s.neighborhood \ G.carrier) =
        {z | 0 ≤ z 1} ∩ planeRayComplement s.radius s.direction := by
  rw [graphStar_centered_image_model]
  congr 1
  ext z
  change (0 ≤ (coordinates s.chart p + z) 1) ↔ 0 ≤ z 1
  simp only [PiLp.add_apply, graphStar_center_second_eq_zero s hp, zero_add]

/-- Boundary containment removes every seam point from the actual star
complement, hence upgrades the coordinate half-plane to an open half-plane. -/
lemma graphStar_centered_image_halfSpace_pos (s : GraphStar G p)
    (hp : p ∈ intrinsicBoundary S) (hB : intrinsicBoundary S ⊆ G.carrier) :
    (fun x => coordinates s.chart x - coordinates s.chart p) ''
      (s.neighborhood \ G.carrier) =
        {z | 0 < z 1} ∩ planeRayComplement s.radius s.direction := by
  have hpos : ∀ z ∈ (fun x => coordinates s.chart x - coordinates s.chart p) ''
      (s.neighborhood \ G.carrier), 0 < z 1 := by
    rintro z ⟨x, hx, rfl⟩
    have hxs : x ∈ s.chart.source := hx.1.1
    have hxmodel : 0 ≤ coordinates s.chart x 1 := (s.chart x).property
    have hxne : coordinates s.chart x 1 ≠ 0 := by
      intro he
      apply hx.2
      apply hB
      exact (SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem x hxs).mpr he
    have hxp : 0 < coordinates s.chart x 1 := lt_of_le_of_ne hxmodel hxne.symm
    simpa only [PiLp.sub_apply, graphStar_center_second_eq_zero s hp, sub_zero] using hxp
  ext z
  constructor
  · intro hz
    exact ⟨hpos z hz, ((graphStar_centered_image_halfSpace s hp) ▸ hz).2⟩
  · intro hz
    rw [graphStar_centered_image_halfSpace s hp]
    exact ⟨(show 0 < z 1 from hz.1).le, hz.2⟩

end Boundary
end GraphStarModelImage

end GraphStarModelImages

namespace StarHomeomorph
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

def centeredCoordinatesHomeomorph (s : GraphStar G p) (U : Set M)
    (hU : U ⊆ s.chart.source) :
    U ≃ₜ ((fun x => coordinates s.chart x - coordinates s.chart p) '' U) :=
  ((P202.SurfaceRegionsEuler.coordinatesHomeomorph s.chart U hU).trans
    ((Homeomorph.addRight (-coordinates s.chart p)).image _)).trans
      (Homeomorph.setCongr (by
        rw [Set.image_image]
        rfl))

@[simp] lemma centeredCoordinatesHomeomorph_apply (s : GraphStar G p) (U : Set M)
    (hU : U ⊆ s.chart.source) (x : U) :
    (centeredCoordinatesHomeomorph s U hU x).val =
      coordinates s.chart x.val - coordinates s.chart p := rfl

/-- The actual star complement, with its subspace topology, is the literal
centered punctured disk in the original model with the star rays removed. -/
def starComplementModelHomeomorph (s : GraphStar G p) :
    (s.neighborhood \ G.carrier : Set M) ≃ₜ
      ({z | toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind} ∩
        GraphStarImage.planeRayComplement s.radius s.direction : Set Plane) :=
  (centeredCoordinatesHomeomorph s _ (fun _ hx => hx.1.1)).trans
    (Homeomorph.setCongr (GraphStarModelImage.graphStar_centered_image_model s))

@[simp] lemma starComplementModelHomeomorph_apply (s : GraphStar G p)
    (x : (s.neighborhood \ G.carrier : Set M)) :
    (starComplementModelHomeomorph s x).val =
      coordinates s.chart x.val - coordinates s.chart p := rfl

/-- Boundary containment identifies the actual boundary-star complement
with the strict upper half-disk minus all actual rays. -/
def starComplementHalfSpaceHomeomorph
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (hp : p ∈ SmoothManifolds.BoundaryData.intrinsicBoundary S)
    (hB : SmoothManifolds.BoundaryData.intrinsicBoundary S ⊆ G.carrier) :
    (s.neighborhood \ G.carrier : Set M) ≃ₜ
      ({z : Plane | 0 < z 1} ∩ GraphStarImage.planeRayComplement s.radius s.direction : Set Plane) :=
  (centeredCoordinatesHomeomorph s _ (fun _ hx => hx.1.1)).trans
    (Homeomorph.setCongr
      (GraphStarModelImage.graphStar_centered_image_halfSpace_pos s hp hB))

end StarHomeomorph


section PlaneComplex
open Complex
namespace PlaneComplexBridge


lemma planeComplex_im (z : Plane) : (planeComplex z).im = z 1 := by
  change (Complex.orthonormalBasisOneI.repr.symm z).im = z 1
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  simp

lemma planeComplex_mem_rayComplement_iff {n : ℕ} (d : Fin n → Plane) (r : ℝ) (z : Plane) :
    planeComplex z ∈ AngularSector.rayComplement r (fun i => planeComplex (d i)) ↔
      z ∈ GraphStarImage.planeRayComplement r d := by
  have hsame (i : Fin n) :
      SameRay ℝ (planeComplex z) (planeComplex (d i)) ↔ SameRay ℝ z (d i) :=
    SameRay.sameRay_map_iff planeComplex.toLinearEquiv
  have hn : planeComplex z ≠ 0 ↔ z ≠ 0 := planeComplex.map_ne_zero_iff
  simp only [AngularSector.rayComplement, GraphStarImage.planeRayComplement,
    mem_ofPred_eq, planeComplex.norm_map, hsame]
  rw [hn]

lemma planeComplex_image_rayComplement {n : ℕ} (d : Fin n → Plane) (r : ℝ) :
    planeComplex '' GraphStarImage.planeRayComplement r d =
      AngularSector.rayComplement r (fun i => planeComplex (d i)) := by
  ext z
  obtain ⟨v, rfl⟩ := planeComplex.surjective z
  rw [planeComplex.injective.mem_set_image]
  exact (planeComplex_mem_rayComplement_iff d r v).symm

lemma arg_pos_iff_im_pos_of_slitPlane {z : ℂ} (hz : z ∈ Complex.slitPlane) :
    0 < arg z ↔ 0 < z.im := by
  constructor
  · intro h
    have hb : arg z < Real.pi := (Complex.arg_le_pi _).lt_of_ne
      (Complex.mem_slitPlane_iff_arg.mp hz).1
    have hp := mul_pos (norm_pos_iff.mpr (Complex.slitPlane_ne_zero hz))
      (Real.sin_pos_of_pos_of_lt_pi h hb)
    simpa only [Complex.norm_mul_sin_arg] using hp
  · intro h
    have hn : arg z ≠ 0 := by
      intro he
      exact h.ne' (Complex.arg_eq_zero_iff.mp he).2
    exact lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr h.le) hn.symm

lemma rayComplement_subset_slitPlane {n : ℕ} (d : Fin n → ℂ) (r : ℝ)
    (hcut : ∃ i, arg (d i) = Real.pi) :
    AngularSector.rayComplement r d ⊆ Complex.slitPlane := by
  intro z hz
  rw [Complex.mem_slitPlane_iff_arg]
  obtain ⟨i, hi⟩ := hcut
  refine ⟨?_, hz.1⟩
  intro he
  exact hz.2.2 i (Complex.sameRay_of_arg_eq (he.trans hi.symm))

lemma planeComplex_image_upperRayComplement {n : ℕ} (d : Fin n → Plane) (r : ℝ)
    (hcut : ∃ i, arg (planeComplex (d i)) = Real.pi) :
    planeComplex '' ({z | 0 < z 1} ∩ GraphStarImage.planeRayComplement r d) =
      AngularSector.upperRayComplement r (fun i => planeComplex (d i)) := by
  ext z
  obtain ⟨v, rfl⟩ := planeComplex.surjective z
  rw [planeComplex.injective.mem_set_image]
  change (0 < v 1 ∧ v ∈ GraphStarImage.planeRayComplement r d) ↔
    planeComplex v ∈ AngularSector.rayComplement r (fun i => planeComplex (d i)) ∧
      0 < arg (planeComplex v)
  rw [planeComplex_mem_rayComplement_iff]
  constructor
  · intro hv
    refine ⟨hv.2, ?_⟩
    have hs := rayComplement_subset_slitPlane (fun i => planeComplex (d i)) r hcut
      ((planeComplex_mem_rayComplement_iff d r v).mpr hv.2)
    apply (arg_pos_iff_im_pos_of_slitPlane hs).mpr
    rw [planeComplex_im]
    exact hv.1
  · intro hv
    refine ⟨?_, hv.1⟩
    have hs := rayComplement_subset_slitPlane (fun i => planeComplex (d i)) r hcut
      ((planeComplex_mem_rayComplement_iff d r v).mpr hv.1)
    have hp := (arg_pos_iff_im_pos_of_slitPlane hs).mp hv.2
    rwa [planeComplex_im] at hp

end PlaneComplexBridge

end PlaneComplex

noncomputable def componentsEquiv {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) : ConnectedComponents X ≃ ConnectedComponents Y where
  toFun := H.continuous.connectedComponentsMap
  invFun := H.symm.continuous.connectedComponentsMap
  left_inv := by
    intro a
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    simp
  right_inv := by
    intro a
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe a
    simp

@[simp] lemma componentsEquiv_mk {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (H : X ≃ₜ Y) (x : X) :
    componentsEquiv H (ConnectedComponents.mk x) = ConnectedComponents.mk (H x) := rfl

lemma image_componentSet {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {U : Set X} {V : Set Y} (H : U ≃ₜ V) (f : X → Y)
    (hf : ∀ x : U, (H x).val = f x.val) (a : ConnectedComponents U) :
    f '' componentSet U a = componentSet V (componentsEquiv H a) := by
  ext y
  constructor
  · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
    exact ⟨H z, by change ConnectedComponents.mk (H z) = _; rw [← componentsEquiv_mk, hz], hf z⟩
  · rintro ⟨z, hz, rfl⟩
    let x := H.symm z
    refine ⟨x.val, ⟨x, ?_, rfl⟩, ?_⟩
    · apply (componentsEquiv H).injective
      rw [componentsEquiv_mk]
      change ConnectedComponents.mk (H (H.symm z)) = _
      rw [H.apply_symm_apply]
      exact hz
    · exact (hf x).symm.trans (congrArg Subtype.val (H.apply_symm_apply z))

section RadiusRestriction
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

def restrictStarRadius (s : GraphStar G p) (r : ℝ) (hr : 0 < r) (hle : r ≤ s.radius) :
    GraphStar G p where
  chart := s.chart
  chart_mem := s.chart_mem
  mem_source := s.mem_source
  radius := r
  radius_pos := hr
  ball_in_target := fun z hz => s.ball_in_target z (lt_of_lt_of_le hz hle)
  rayCount := s.rayCount
  direction := s.direction
  direction_injective := s.direction_injective
  direction_unit := s.direction_unit
  rays_in_model := fun i t ht htr => s.rays_in_model i t ht (lt_of_lt_of_le htr hle)
  graph_eq := by
    intro x hxs hxb
    rw [s.graph_eq x hxs (lt_of_lt_of_le hxb hle)]
    constructor
    · rintro (hxp | ⟨i, t, ht, htr, hcoord⟩)
      · exact Or.inl hxp
      · refine Or.inr ⟨i, t, ht, ?_, hcoord⟩
        have hn : ‖coordinates s.chart x - coordinates s.chart p‖ = t := by
          rw [hcoord, add_sub_cancel_left, norm_smul, Real.norm_eq_abs,
            abs_of_pos ht, s.direction_unit, mul_one]
        change ‖coordinates s.chart x - coordinates s.chart p‖ < r at hxb
        rwa [hn] at hxb
    · rintro (hxp | ⟨i, t, ht, htr, hcoord⟩)
      · exact Or.inl hxp
      · exact Or.inr ⟨i, t, ht, lt_of_lt_of_le htr hle, hcoord⟩

lemma restrictStarRadius_neighborhood_subset (s : GraphStar G p) (r : ℝ)
    (hr : 0 < r) (hle : r ≤ s.radius) :
    (restrictStarRadius s r hr hle).neighborhood ⊆ s.neighborhood := by
  intro x hx
  exact ⟨hx.1, lt_of_lt_of_le hx.2 hle⟩

lemma exists_interior_halfSpace_star
    {M : Type u} [TopologicalSpace M] {S : SmoothManifold 2 .halfSpace M}
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (hp : p ∉ intrinsicBoundary S) :
    ∃ t : GraphStar G p,
      t.chart = s.chart ∧ t.rayCount = s.rayCount ∧ HEq t.direction s.direction ∧
      t.radius ≤ s.radius ∧ t.neighborhood ⊆ s.neighborhood ∧
      ∀ z : Plane, ‖z‖ < t.radius →
        toPlane.symm (coordinates t.chart p + z) ∈ modelSet 2 .halfSpace := by
  have hheight : 0 < coordinates s.chart p 1 := by
    have hm : 0 ≤ coordinates s.chart p 1 := (s.chart p).property
    have hn : coordinates s.chart p 1 ≠ 0 := by
      intro he
      exact hp ((SmoothManifolds.intrinsicBoundary_iff_chart S s.chart s.chart_mem p
        s.mem_source).mpr he)
    exact lt_of_le_of_ne hm hn.symm
  let r := min s.radius (coordinates s.chart p 1 / 2)
  have hr : 0 < r := lt_min s.radius_pos (half_pos hheight)
  let t := restrictStarRadius s r hr (min_le_left _ _)
  refine ⟨t, rfl, rfl, HEq.rfl, min_le_left _ _,
    restrictStarRadius_neighborhood_subset s r hr (min_le_left _ _), ?_⟩
  intro z hz
  change 0 ≤ (coordinates s.chart p + z) 1
  have hcoord : |z 1| ≤ ‖z‖ := PiLp.norm_apply_le z 1
  have hsmall : r ≤ coordinates s.chart p 1 / 2 := min_le_right _ _
  change ‖z‖ < r at hz
  simp only [PiLp.add_apply]
  have := neg_le_abs (z 1)
  linarith

end RadiusRestriction
namespace AngularSector

lemma exists_rayComplement_components_pos {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (d : Fin n → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (hcut : ∃ i, arg (d i) = Real.pi) :
    ∃ e : Equiv.Perm (Fin n),
      let c : Fin (n + 1) → ℝ := Fin.cons (-Real.pi) (fun i => arg (d (e i)))
      StrictMono c ∧ c (Fin.last n) = Real.pi ∧
      ∃ E : ConnectedComponents (rayComplement r d) ≃ Fin n,
        ∀ a, componentSet (rayComplement r d) a =
          sector r (c (E a).castSucc) (c (E a).succ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  exact exists_rayComplement_components hr d hd hu hcut

def unitRotationHomeomorph {n : ℕ} (r : ℝ) (d : Fin n → ℂ) (c : ℂ) (hc : ‖c‖ = 1) :
    rayComplement r d ≃ₜ rayComplement r (fun i => c * d i) :=
  ((Homeomorph.mulLeft₀ c (norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero))).image _).trans
    (Homeomorph.setCongr (by
      let H : ℂ ≃ₜ ℂ := Homeomorph.mulLeft₀ c
        (norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero))
      change H '' rayComplement r d = _
      ext z
      obtain ⟨y, rfl⟩ := H.surjective z
      rw [H.injective.mem_set_image]
      exact (unit_mul_mem_rayComplement_iff d c hc r y).symm))

@[simp] lemma unitRotationHomeomorph_apply {n : ℕ} (r : ℝ) (d : Fin n → ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) (x : rayComplement r d) :
    (unitRotationHomeomorph r d c hc x).val = c * x.val := rfl

lemma exists_cut_rotation {n : ℕ} (d : Fin n → ℂ) (hu : ∀ i, ‖d i‖ = 1) (i₀ : Fin n) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * d i₀ = -1 := by
  refine ⟨-star (d i₀), by simp [hu], ?_⟩
  rw [neg_mul]
  change -(starRingEnd ℂ (d i₀) * d i₀) = -1
  rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq, hu]
  norm_num

/-- Exact finite component indexing survives an actual subtype homeomorphism;
its coordinate formula is kept in the component-set identity. -/
lemma fullDiskComponents_from_homeomorph {X : Type*} [TopologicalSpace X]
    {U : Set X} {n : ℕ} (hn : 0 < n) {r : ℝ} (hr : 0 < r)
    (d : Fin n → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (H : U ≃ₜ rayComplement r d) (f : X → ℂ) (hf : ∀ x : U, (H x).val = f x.val) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * d ⟨0, hn⟩ = -1 ∧
      ∃ e : Equiv.Perm (Fin n),
        let cuts : Fin (n + 1) → ℝ := Fin.cons (-Real.pi) (fun i => arg (c * d (e i)))
        StrictMono cuts ∧ cuts (Fin.last n) = Real.pi ∧
        ∃ E : ConnectedComponents U ≃ Fin n, ∀ a,
          (fun x => c * f x) '' componentSet U a =
            sector r (cuts (E a).castSucc) (cuts (E a).succ) := by
  obtain ⟨c, hc, hbase⟩ := exists_cut_rotation d hu ⟨0, hn⟩
  have hc0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
  have hd' : Function.Injective (fun i => c * d i) :=
    (mul_right_injective₀ hc0).comp hd
  have hu' (i : Fin n) : ‖c * d i‖ = 1 := by rw [norm_mul, hc, hu, one_mul]
  obtain ⟨e, he, hlast, E, hE⟩ := exists_rayComplement_components_pos hn hr
    (fun i => c * d i) hd' hu' ⟨⟨0, hn⟩, by rw [hbase, Complex.arg_neg_one]⟩
  let K := H.trans (unitRotationHomeomorph r d c hc)
  refine ⟨c, hc, hbase, e, he, hlast, (componentsEquiv K).trans E, ?_⟩
  intro a
  rw [image_componentSet K (fun x => c * f x) (fun x => by
    change c * (H x).val = c * f x.val
    rw [hf]), hE]
  rfl
end AngularSector

namespace AngularSector
lemma halfDiskComponents_from_homeomorph {X : Type*} [TopologicalSpace X]
    {U : Set X} {n : ℕ} {r : ℝ} (hr : 0 < r)
    (d : Fin (n + 2) → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (hhalf : ∀ i, 0 ≤ (d i).im)
    (hleft : ∃ i, arg (d i) = 0) (hright : ∃ i, arg (d i) = Real.pi)
    (H : U ≃ₜ upperRayComplement r d) (f : X → ℂ)
    (hf : ∀ x : U, (H x).val = f x.val) :
    ∃ e : Equiv.Perm (Fin (n + 2)),
      let c := fun i => arg (d (e i))
      StrictMono c ∧ c 0 = 0 ∧ c (Fin.last (n + 1)) = Real.pi ∧
      ∃ E : ConnectedComponents U ≃ Fin (n + 1), ∀ a,
        f '' componentSet U a = sector r (c (E a).castSucc) (c (E a).succ) := by
  obtain ⟨e, he, hfirst, hlast, E, hE⟩ :=
    exists_upperRayComplement_components hr d hd hu hhalf hleft hright
  refine ⟨e, he, hfirst, hlast, (componentsEquiv H).trans E, ?_⟩
  intro a
  rw [image_componentSet H f hf, hE]
  rfl

lemma rayComplement_reindex {ι κ : Type*} (r : ℝ) (d : κ → ℂ) (e : ι ≃ κ) :
    rayComplement r (fun i => d (e i)) = rayComplement r d := by
  ext z
  change (_ ∧ _ ∧ ∀ i, ¬SameRay ℝ z (d (e i))) ↔ (_ ∧ _ ∧ ∀ i, ¬SameRay ℝ z (d i))
  constructor
  · rintro ⟨h0, hr, hd⟩
    exact ⟨h0, hr, fun i => by simpa only [e.apply_symm_apply] using hd (e.symm i)⟩
  · rintro ⟨h0, hr, hd⟩
    exact ⟨h0, hr, fun i => hd (e i)⟩

lemma upperRayComplement_reindex {ι κ : Type*} (r : ℝ) (d : κ → ℂ) (e : ι ≃ κ) :
    upperRayComplement r (fun i => d (e i)) = upperRayComplement r d := by
  rw [upperRayComplement, upperRayComplement, rayComplement_reindex]
end AngularSector

namespace StarHomeomorph
open GraphStarImage PlaneComplexBridge
variable {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}

def starComplementFullDiskHomeomorph (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind) :
    (s.neighborhood \ G.carrier : Set M) ≃ₜ planeRayComplement s.radius s.direction :=
  (starComplementModelHomeomorph s).trans (Homeomorph.setCongr (by
    ext z
    constructor
    · exact fun hz => hz.2
    · exact fun hz => ⟨hfull z hz.2.1, hz⟩))

def planeComplexRayHomeomorph {n : ℕ} (r : ℝ) (d : Fin n → Plane) :
    planeRayComplement r d ≃ₜ AngularSector.rayComplement r (fun i => planeComplex (d i)) :=
  ((planeComplex.toHomeomorph).image _).trans
    (Homeomorph.setCongr (planeComplex_image_rayComplement d r))

def starComplementFullComplexHomeomorph (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind) :
    (s.neighborhood \ G.carrier : Set M) ≃ₜ
      AngularSector.rayComplement s.radius (fun i => planeComplex (s.direction i)) :=
  (starComplementFullDiskHomeomorph s hfull).trans
    (planeComplexRayHomeomorph s.radius s.direction)

@[simp] lemma starComplementFullComplexHomeomorph_apply (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (x : (s.neighborhood \ G.carrier : Set M)) :
    (starComplementFullComplexHomeomorph s hfull x).val =
      planeComplex (coordinates s.chart x.val - coordinates s.chart p) := rfl

lemma planeComplex_reference : planeComplex P202Specs.PlaneTurning.reference = 1 := by
  change Complex.orthonormalBasisOneI.repr.symm _ = _
  rw [Complex.orthonormalBasisOneI_repr_symm_apply]
  norm_num [P202Specs.PlaneTurning.reference]

lemma boundaryStar_negativeCut {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier) :
    ∃ i, arg (planeComplex (s.direction i)) = Real.pi := by
  obtain ⟨i0, i1, _, _, h1, _⟩ := graphStar_boundary_rays s hp hB
  exact ⟨i1, by rw [h1, map_neg, planeComplex_reference, Complex.arg_neg_one]⟩

def starComplementBoundaryComplexHomeomorph {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier) :
    (s.neighborhood \ G.carrier : Set M) ≃ₜ
      AngularSector.upperRayComplement s.radius (fun i => planeComplex (s.direction i)) :=
  ((starComplementHalfSpaceHomeomorph s hp hB).trans
    ((planeComplex.toHomeomorph).image _)).trans
    (Homeomorph.setCongr (planeComplex_image_upperRayComplement s.direction s.radius
      (boundaryStar_negativeCut s hp hB)))

@[simp] lemma starComplementBoundaryComplexHomeomorph_apply {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier) (x : (s.neighborhood \ G.carrier : Set M)) :
    (starComplementBoundaryComplexHomeomorph s hp hB x).val =
      planeComplex (coordinates s.chart x.val - coordinates s.chart p) := rfl
end StarHomeomorph

/-- The components of the actual manifold star complement are precisely the
open angular gaps in a constructed finite cyclic ray order. -/
theorem fullStarComponents {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (hn : 0 < s.rayCount) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c * PlaneComplexBridge.planeComplex (s.direction ⟨0, hn⟩) = -1 ∧
      ∃ e : Equiv.Perm (Fin s.rayCount),
        let cuts : Fin (s.rayCount + 1) → ℝ := Fin.cons (-Real.pi)
          (fun i => arg (c * PlaneComplexBridge.planeComplex (s.direction (e i))))
        StrictMono cuts ∧ cuts (Fin.last s.rayCount) = Real.pi ∧
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin s.rayCount,
          ∀ a, (fun x => c * PlaneComplexBridge.planeComplex
            (coordinates s.chart x - coordinates s.chart p)) ''
              componentSet (s.neighborhood \ G.carrier) a =
                AngularSector.sector s.radius (cuts (E a).castSucc) (cuts (E a).succ) := by
  apply AngularSector.fullDiskComponents_from_homeomorph hn s.radius_pos
    (fun i => PlaneComplexBridge.planeComplex (s.direction i))
    (PlaneComplexBridge.planeComplex.injective.comp s.direction_injective)
    (fun i => by rw [PlaneComplexBridge.planeComplex.norm_map, s.direction_unit])
    (StarHomeomorph.starComplementFullComplexHomeomorph s hfull)
    (fun x => PlaneComplexBridge.planeComplex (coordinates s.chart x - coordinates s.chart p))
  intro x
  rfl

/-- Boundary containment yields the actual n-1 inside gaps, with an exact
component-set bridge all the way to the original surface. -/
theorem boundaryStarComponents {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier) :
    ∃ n : ℕ, ∃ hn : s.rayCount = n + 2,
      let d := fun i : Fin (n + 2) =>
        PlaneComplexBridge.planeComplex (s.direction (Fin.cast hn.symm i))
      ∃ e : Equiv.Perm (Fin (n + 2)),
        let cuts := fun i => arg (d (e i))
        StrictMono cuts ∧ cuts 0 = 0 ∧ cuts (Fin.last (n + 1)) = Real.pi ∧
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin (n + 1),
          ∀ a, (fun x => PlaneComplexBridge.planeComplex
            (coordinates s.chart x - coordinates s.chart p)) ''
              componentSet (s.neighborhood \ G.carrier) a =
                AngularSector.sector s.radius (cuts (E a).castSucc) (cuts (E a).succ) := by
  have htwo := graphStar_boundary_two_le_rayCount s hp hB
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le htwo
  have hn : s.rayCount = n + 2 := by omega
  let e : Fin (n + 2) ≃ Fin s.rayCount := finCongr hn.symm
  let d := fun i => PlaneComplexBridge.planeComplex (s.direction (e i))
  have hd : Function.Injective d :=
    (PlaneComplexBridge.planeComplex.injective.comp s.direction_injective).comp e.injective
  have hu (i) : ‖d i‖ = 1 := by
    dsimp [d]
    rw [PlaneComplexBridge.planeComplex.norm_map, s.direction_unit]
  have hh (i) : 0 ≤ (d i).im := by
    dsimp [d]
    rw [PlaneComplexBridge.planeComplex_im]
    exact graphStar_direction_second_nonneg s hp _
  obtain ⟨i0, i1, _, h0, h1, _⟩ := graphStar_boundary_rays s hp hB
  have hl : ∃ i, arg (d i) = 0 := by
    refine ⟨e.symm i0, ?_⟩
    simp only [d, e.apply_symm_apply, h0, StarHomeomorph.planeComplex_reference,
      Complex.arg_one]
  have hr : ∃ i, arg (d i) = Real.pi := by
    refine ⟨e.symm i1, ?_⟩
    simp only [d, e.apply_symm_apply, h1, map_neg, StarHomeomorph.planeComplex_reference,
      Complex.arg_neg_one]
  let H := (StarHomeomorph.starComplementBoundaryComplexHomeomorph s hp hB).trans
    (Homeomorph.setCongr (AngularSector.upperRayComplement_reindex s.radius
      (fun i => PlaneComplexBridge.planeComplex (s.direction i)) e).symm)
  refine ⟨n, hn, ?_⟩
  apply AngularSector.halfDiskComponents_from_homeomorph s.radius_pos d hd hu hh hl hr H
    (fun x => PlaneComplexBridge.planeComplex (coordinates s.chart x - coordinates s.chart p))
  intro x
  rfl
end P202.RadialGraphSectors
namespace P202.RadialGraphSectors
open GraphStarImage PlaneComplexBridge AngularSector

lemma fullStarZeroComponents {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (hz : s.rayCount = 0) :
    Nonempty (ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin 1) := by
  let d := fun i => planeComplex (s.direction i)
  let e : Fin 0 ≃ Fin s.rayCount := finCongr hz.symm
  let H := (StarHomeomorph.starComplementFullComplexHomeomorph s hfull).trans
    (Homeomorph.setCongr (rayComplement_reindex s.radius d e).symm)
  obtain ⟨E⟩ := rayComplement_zero_components s.radius_pos (fun i => d (e i))
  exact ⟨(componentsEquiv H).trans E⟩

theorem fullStar_component_card {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p)
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind) :
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) =
      if s.rayCount = 0 then 1 else s.rayCount := by
  classical
  split_ifs with hz
  · obtain ⟨E⟩ := fullStarZeroComponents s hfull hz
    simpa using Nat.card_congr E
  · have hn : 0 < s.rayCount := Nat.pos_of_ne_zero hz
    obtain ⟨c, hc, hbase, e, he, hlast, E, hE⟩ := fullStarComponents s hfull hn
    simpa using Nat.card_congr E

theorem boundaryStar_component_card {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} {G : EmbeddedGraph S} {p : M}
    (s : GraphStar G p) (hp : p ∈ intrinsicBoundary S)
    (hB : intrinsicBoundary S ⊆ G.carrier) :
    Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = s.rayCount - 1 := by
  obtain ⟨n, hn, e, he, h0, hlast, E, hE⟩ := boundaryStarComponents s hp hB
  have hcard : Nat.card (ConnectedComponents (s.neighborhood \ G.carrier : Set M)) = n + 1 := by
    simpa using Nat.card_congr E
  omega

open SmoothManifolds.TangentData P202.MetricData P202.SurfaceBoundaryData
/-- Genuine star directions realized by the original inverse chart
differential, for both model kinds and either tangent orientation. -/
theorem starMetricAngle_cyclic_sum {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2)) (hn : 0 < s.rayCount) :
    ∃ e : Equiv.Perm (Fin s.rayCount),
      (∑ i, starMetricAngle g s o (s.direction (e i))
        (s.direction (e (finRotate s.rayCount i)))) = 2 * Real.pi := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  obtain ⟨e, _, he⟩ := exists_cyclic_angle_sum_linearImage hn o (starTangentEquiv s)
    s.direction s.direction_injective s.direction_unit
  exact ⟨e, he⟩

end P202.RadialGraphSectors

namespace P202.RadialGraphSectors
section RadialNormalization
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def radialLinearMap (L : E ≃L[ℝ] F) (x : E) : F := (‖x‖ / ‖L x‖) • L x

lemma radialLinearMap_norm (L : E ≃L[ℝ] F) (x : E) :
    ‖radialLinearMap L x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [radialLinearMap, hx]
  · have hLx : ‖L x‖ ≠ 0 := norm_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr hx)
    rw [radialLinearMap, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)), div_mul_cancel₀ _ hLx]

lemma radialLinearMap_ne_zero (L : E ≃L[ℝ] F) {x : E} (hx : x ≠ 0) :
    radialLinearMap L x ≠ 0 := by
  apply norm_ne_zero_iff.mp
  rw [radialLinearMap_norm]
  exact norm_ne_zero_iff.mpr hx

lemma radialLinearMap_sameRay (L : E ≃L[ℝ] F) (x : E) :
    SameRay ℝ (radialLinearMap L x) (L x) :=
  SameRay.sameRay_nonneg_smul_left _ (div_nonneg (norm_nonneg _) (norm_nonneg _))

lemma radialLinearMap_sameRay_iff (L : E ≃L[ℝ] F) (x y : E) :
    SameRay ℝ (radialLinearMap L x) (radialLinearMap L y) ↔ SameRay ℝ x y := by
  by_cases hx : x = 0
  · simp [hx, radialLinearMap]
  by_cases hy : y = 0
  · simp [hy, radialLinearMap]
  constructor
  · intro h
    apply (SameRay.sameRay_map_iff L.toLinearEquiv).mp
    exact (radialLinearMap_sameRay L x).symm.trans (h.trans (radialLinearMap_sameRay L y) (fun h0 => (radialLinearMap_ne_zero L hy h0).elim))
      (fun h0 => (radialLinearMap_ne_zero L hx h0).elim)
  · intro h
    exact (radialLinearMap_sameRay L x).trans
      (((SameRay.sameRay_map_iff L.toLinearEquiv).mpr h).trans
        (radialLinearMap_sameRay L y).symm (fun h0 => (L.map_ne_zero_iff.mpr hy h0).elim))
      (fun h0 => (L.map_ne_zero_iff.mpr hx h0).elim)

lemma radialLinearMap_inverse (L : E ≃L[ℝ] F) (x : E) :
    radialLinearMap L.symm (radialLinearMap L x) = x := by
  by_cases hx : x = 0
  · simp [radialLinearMap, hx]
  have hnx : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  have hnL : ‖L x‖ ≠ 0 := norm_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr hx)
  have ha : 0 < ‖x‖ / ‖L x‖ := div_pos (norm_pos_iff.mpr hx)
    (norm_pos_iff.mpr (L.map_ne_zero_iff.mpr hx))
  rw [radialLinearMap, radialLinearMap_norm]
  simp only [radialLinearMap, map_smul, L.symm_apply_apply, norm_smul,
    Real.norm_eq_abs, abs_of_pos ha, smul_smul]
  have hc : ‖x‖ / (‖x‖ / ‖L x‖ * ‖x‖) * (‖x‖ / ‖L x‖) = 1 := by
    field_simp
  rw [hc, one_smul]

def radialLinearHomeomorph (L : E ≃L[ℝ] F) : ({0}ᶜ : Set E) ≃ₜ ({0}ᶜ : Set F) where
  toFun x := ⟨radialLinearMap L x, radialLinearMap_ne_zero L x.property⟩
  invFun y := ⟨radialLinearMap L.symm y, radialLinearMap_ne_zero L.symm y.property⟩
  left_inv x := Subtype.ext (radialLinearMap_inverse L x)
  right_inv y := Subtype.ext (radialLinearMap_inverse L.symm y)
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold radialLinearMap
    fun_prop (disch := intro x; exact norm_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr x.property))
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold radialLinearMap
    fun_prop (disch := intro y; exact norm_ne_zero_iff.mpr (L.symm.map_ne_zero_iff.mpr y.property))
/-- The normalized linear change gives an exact homeomorphism of bounded ray
complements, preserving every radial coordinate. -/
def radialRayComplementHomeomorph {ι : Type*} (L : E ≃L[ℝ] F) (r : ℝ) (d : ι → E) :
    ({x : E | x ≠ 0 ∧ ‖x‖ < r ∧ ∀ i, ¬SameRay ℝ x (d i)} : Set E) ≃ₜ
      ({y : F | y ≠ 0 ∧ ‖y‖ < r ∧ ∀ i, ¬SameRay ℝ y (radialLinearMap L (d i))} : Set F) where
  toFun x := ⟨radialLinearMap L x, radialLinearMap_ne_zero L x.property.1,
    by rw [radialLinearMap_norm]; exact x.property.2.1,
    fun i h => x.property.2.2 i ((radialLinearMap_sameRay_iff L _ _).mp h)⟩
  invFun y := ⟨radialLinearMap L.symm y, radialLinearMap_ne_zero L.symm y.property.1,
    by rw [radialLinearMap_norm]; exact y.property.2.1, by
      intro i h
      have hh := (radialLinearMap_sameRay_iff L _ _).mpr h
      have hinv : radialLinearMap L (radialLinearMap L.symm y) = y :=
        radialLinearMap_inverse L.symm y
      rw [hinv] at hh
      exact y.property.2.2 i hh⟩
  left_inv x := Subtype.ext (radialLinearMap_inverse L x)
  right_inv y := Subtype.ext (radialLinearMap_inverse L.symm y)
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold radialLinearMap
    fun_prop (disch := intro x; exact norm_ne_zero_iff.mpr (L.map_ne_zero_iff.mpr x.property.1))
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold radialLinearMap
    fun_prop (disch := intro y; exact norm_ne_zero_iff.mpr (L.symm.map_ne_zero_iff.mpr y.property.1))

@[simp] lemma radialRayComplementHomeomorph_apply {ι : Type*}
    (L : E ≃L[ℝ] F) (r : ℝ) (d : ι → E)
    (x : {x : E | x ≠ 0 ∧ ‖x‖ < r ∧ ∀ i, ¬SameRay ℝ x (d i)}) :
    (radialRayComplementHomeomorph L r d x).val = radialLinearMap L x := rfl

lemma radialLinearMap_injective_on_unit {ι : Type*} (L : E ≃L[ℝ] F)
    (d : ι → E) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1) :
    Function.Injective (fun i => radialLinearMap L (d i)) := by
  intro i j h
  apply hd
  apply SameRay.eq_of_norm_eq _ (by rw [hu, hu])
  apply (radialLinearMap_sameRay_iff L _ _).mp
  change radialLinearMap L (d i) = radialLinearMap L (d j) at h
  rw [h]

lemma radialLinearMap_neg (L : E ≃L[ℝ] F) (x : E) :
    radialLinearMap L (-x) = -radialLinearMap L x := by
  simp [radialLinearMap]

lemma radialLinearMap_smul_pos (L : E ≃L[ℝ] F) (x : E) {t : ℝ} (ht : 0 < t) :
    radialLinearMap L (t • x) = t • radialLinearMap L x := by
  unfold radialLinearMap
  rw [map_smul, norm_smul, norm_smul, Real.norm_eq_abs, abs_of_pos ht]
  rw [mul_div_mul_left _ _ ht.ne', smul_smul, smul_smul, mul_comm]

end RadialNormalization
end P202.RadialGraphSectors


namespace P202.RadialGraphSectors
section MetricBridge
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]

def kahlerEquiv (o : Orientation ℝ V (Fin 2)) (w : V) (hw : w ≠ 0) : V ≃ₗ[ℝ] ℂ :=
  LinearEquiv.ofInjectiveOfFinrankEq (o.kahler w)
    (by
      intro x y h
      apply sub_eq_zero.mp
      apply ((o.kahler_eq_zero_iff w (x - y)).mp ?_).resolve_left hw
      rw [map_sub, h, sub_self])
    ((Fact.out : Module.finrank ℝ V = 2).trans Complex.finrank_real_complex.symm)

@[simp] lemma kahlerEquiv_apply (o : Orientation ℝ V (Fin 2)) (w : V) (hw : w ≠ 0)
    (x : V) : kahlerEquiv o w hw x = o.kahler w x := rfl

lemma kahlerEquiv_oangle (o : Orientation ℝ V (Fin 2)) (w : V) (hw : w ≠ 0)
    {x y : V} (hx : x ≠ 0) (hy : y ≠ 0) :
    o.oangle x y = (Complex.arg (kahlerEquiv o w hw y) : Real.Angle) -
      (Complex.arg (kahlerEquiv o w hw x) : Real.Angle) := by
  change o.oangle x y = o.oangle w y - o.oangle w x
  exact (o.oangle_sub_left hw hx hy).symm

lemma positiveAngle_sub_coe_iff {a b t : ℝ}
    (ha : -Real.pi ≤ a) (hab : a < b) (hb : b ≤ Real.pi)
    (ht : t ∈ Ioo (-Real.pi) Real.pi) :
    positiveAngle ((t : Real.Angle) - (a : Real.Angle)) <
      positiveAngle ((b : Real.Angle) - (a : Real.Angle)) ↔ t ∈ Ioo a b := by
  have hba : b - a ∈ Ioc 0 (2 * Real.pi) := ⟨sub_pos.mpr hab, by linarith⟩
  simp only [← Real.Angle.coe_sub]
  rw [positiveAngle_coe hba]
  by_cases hta : a < t
  · have hta' : t - a ∈ Ioc 0 (2 * Real.pi) := ⟨sub_pos.mpr hta, by linarith [ht.2]⟩
    rw [positiveAngle_coe hta']
    constructor
    · intro h; exact ⟨hta, by linarith⟩
    · intro h; linarith [h.2]
  · have hta' : t - a + 2 * Real.pi ∈ Ioc 0 (2 * Real.pi) := by
      constructor <;> linarith [ht.1]
    have hcoe : ((t - a : ℝ) : Real.Angle) = ((t - a + 2 * Real.pi : ℝ) : Real.Angle) := by
      simp only [Real.Angle.coe_add, Real.Angle.coe_two_pi, add_zero]
    rw [hcoe, positiveAngle_coe hta']
    constructor
    · intro h; exfalso; linarith [ht.1]
    · intro h; exact False.elim (hta h.1)

end MetricBridge
section RadialAngles
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
@[simp] lemma radialLinearMap_arg (L : E ≃L[ℝ] ℂ) (x : E) :
    Complex.arg (radialLinearMap L x) = Complex.arg (L x) := by
  by_cases hx : x = 0
  · simp [hx, radialLinearMap]
  · rw [radialLinearMap, Complex.real_smul]
    exact Complex.arg_real_mul (L x)
      (div_pos (norm_pos_iff.mpr hx) (norm_pos_iff.mpr (L.map_ne_zero_iff.mpr hx)))

lemma unit_mul_arg_sub {c x y : ℂ} (hc : c ≠ 0) (hx : x ≠ 0) (hy : y ≠ 0) :
    (arg (c * y) : Real.Angle) - (arg (c * x) : Real.Angle) =
      (arg y : Real.Angle) - (arg x : Real.Angle) := by
  rw [Complex.arg_mul_coe_angle hc hy, Complex.arg_mul_coe_angle hc hx]
  abel


end RadialAngles

lemma predecessor_cut_angles {n : ℕ} (hn : 0 < n) (f : Fin n → ℝ)
    (hlast : (Fin.cons (-Real.pi) f : Fin (n + 1) → ℝ) (Fin.last n) = Real.pi) (i : Fin n) :
    (f ((finRotate n).symm i) : Real.Angle) =
      (((Fin.cons (-Real.pi) f : Fin (n + 1) → ℝ) i.castSucc : ℝ) : Real.Angle) ∧
    (f ((finRotate n).symm (finRotate n i)) : Real.Angle) =
      (((Fin.cons (-Real.pi) f : Fin (n + 1) → ℝ) i.succ : ℝ) : Real.Angle) := by
  constructor
  · obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
    refine Fin.cases ?_ (fun j => ?_) i
    · have hinv : (finRotate (m + 1)).symm 0 = Fin.last m := by
        apply (finRotate (m + 1)).injective
        simp only [Equiv.apply_symm_apply, finRotate_last]
      rw [hinv]
      change (f (Fin.last m) : Real.Angle) = (-Real.pi : ℝ)
      have hf : f (Fin.last m) = Real.pi := by simpa using hlast
      rw [hf, Real.Angle.coe_neg, Real.Angle.neg_coe_pi]
    · have hinv : (finRotate (m + 1)).symm j.succ = j.castSucc := by
        apply (finRotate (m + 1)).injective
        rw [Equiv.apply_symm_apply]
        exact (finRotate_of_lt j.isLt).symm
      rw [hinv, ← Fin.succ_castSucc, Fin.cons_succ]
  · rw [Equiv.symm_apply_apply, Fin.cons_succ]

lemma cyclic_predecessor_metric_gap {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℂ) (e : Equiv.Perm (Fin n))
    (hc : StrictMono (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ))
    (hlast : (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
      (Fin.last n) = Real.pi)
    (i : Fin n) :
    positiveAngle ((arg (d (e ((finRotate n).symm (finRotate n i)))) : Real.Angle) -
      (arg (d (e ((finRotate n).symm i))) : Real.Angle)) =
        (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ) i.succ -
        (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ) i.castSucc := by
  let c := (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
  obtain ⟨h0, h1⟩ := predecessor_cut_angles hn (fun i => arg (d (e i))) hlast i
  rw [h0, h1, ← Real.Angle.coe_sub]
  apply positiveAngle_coe
  refine ⟨sub_pos.mpr (hc (Fin.castSucc_lt_succ (i := i))), ?_⟩
  have hlow := hc.monotone (Fin.zero_le i.castSucc)
  have hupp := hc.monotone (Fin.le_last i.succ)
  change -Real.pi ≤ c i.castSucc at hlow
  change c i.succ ≤ c (Fin.last n) at hupp
  change c (Fin.last n) = Real.pi at hlast
  change c i.succ - c i.castSucc ≤ 2 * Real.pi
  linarith

lemma cyclic_predecessor_metric_sector {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℂ) (e : Equiv.Perm (Fin n))
    (hc : StrictMono (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ))
    (hlast : (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
      (Fin.last n) = Real.pi)
    {r : ℝ} (hcut : ∃ j, arg (d j) = Real.pi) {z : ℂ}
    (hz : z ∈ AngularSector.rayComplement r d) (i : Fin n) :
    positiveAngle ((arg z : Real.Angle) -
      (arg (d (e ((finRotate n).symm i))) : Real.Angle)) <
      positiveAngle ((arg (d (e ((finRotate n).symm (finRotate n i)))) : Real.Angle) -
        (arg (d (e ((finRotate n).symm i))) : Real.Angle)) ↔
    z ∈ AngularSector.sector r
      ((Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ) i.castSucc)
      ((Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ) i.succ) := by
  let c := (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
  obtain ⟨h0, h1⟩ := predecessor_cut_angles hn (fun i => arg (d (e i))) hlast i
  rw [h0, h1]
  have ht : arg z ∈ Ioo (-Real.pi) Real.pi := by
    refine ⟨Complex.neg_pi_lt_arg _, (Complex.arg_le_pi z).lt_of_ne ?_⟩
    intro h
    obtain ⟨j, hj⟩ := hcut
    exact hz.2.2 j (Complex.sameRay_of_arg_eq (h.trans hj.symm))
  have hlow := hc.monotone (Fin.zero_le i.castSucc)
  have hupp := hc.monotone (Fin.le_last i.succ)
  change -Real.pi ≤ c i.castSucc at hlow
  change c i.succ ≤ c (Fin.last n) at hupp
  change c (Fin.last n) = Real.pi at hlast
  rw [positiveAngle_sub_coe_iff hlow (hc (Fin.castSucc_lt_succ (i := i)))
    (hupp.trans_eq hlast) ht]
  exact ⟨fun h => ⟨hz.1, hz.2.1, h⟩, fun h => h.2.2⟩


lemma cyclic_predecessor_metric_sum {n : ℕ} (hn : 0 < n)
    (d : Fin n → ℂ) (e : Equiv.Perm (Fin n))
    (hc : StrictMono (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ))
    (hlast : (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
      (Fin.last n) = Real.pi) :
    (∑ i : Fin n,
      positiveAngle ((arg (d (e ((finRotate n).symm (finRotate n i)))) : Real.Angle) -
        (arg (d (e ((finRotate n).symm i))) : Real.Angle))) = 2 * Real.pi := by
  simp_rw [cyclic_predecessor_metric_gap hn d e hc hlast]
  let c := (Fin.cons (-Real.pi) (fun i => arg (d (e i))) : Fin (n + 1) → ℝ)
  change (∑ i : Fin n, (c i.succ - c i.castSucc)) = _
  rw [Finset.sum_sub_distrib]
  have h0 := Fin.sum_univ_succ c
  have h1 := Fin.sum_univ_castSucc c
  have hc0 : c 0 = -Real.pi := rfl
  change c (Fin.last n) = Real.pi at hlast
  linarith


 theorem fullStarMetricSectors {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 kind M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (hfull : ∀ z : Plane, ‖z‖ < s.radius →
      toPlane.symm (coordinates s.chart p + z) ∈ modelSet 2 kind)
    (hn : 0 < s.rayCount) :
    ∃ e : Equiv.Perm (Fin s.rayCount),
      ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin s.rayCount,
        (∀ a, componentSet (s.neighborhood \ G.carrier) a =
          starMetricSector g s o (s.direction (e (E a)))
            (s.direction (e (finRotate s.rayCount (E a))))) ∧
        (∑ i, starMetricAngle g s o (s.direction (e i))
          (s.direction (e (finRotate s.rayCount i)))) = 2 * Real.pi := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  let L := starTangentEquiv s
  let w := L (s.direction ⟨0, hn⟩)
  have hdir (i : Fin s.rayCount) : s.direction i ≠ 0 :=
    norm_ne_zero_iff.mp ((s.direction_unit i).trans_ne one_ne_zero)
  have hw : w ≠ 0 := L.map_ne_zero_iff.mpr (hdir _)
  let K : Plane ≃L[ℝ] ℂ := (L.trans (kahlerEquiv o w hw)).toContinuousLinearEquiv
  let d := fun i => radialLinearMap K (s.direction i)
  let f := fun x : M => radialLinearMap K (coordinates s.chart x - coordinates s.chart p)
  let U := (s.neighborhood \ G.carrier : Set M)
  let H : U ≃ₜ AngularSector.rayComplement s.radius d :=
    (StarHomeomorph.starComplementFullDiskHomeomorph s hfull).trans
      (radialRayComplementHomeomorph K s.radius s.direction)
  have hd : Function.Injective d :=
    radialLinearMap_injective_on_unit K s.direction s.direction_injective s.direction_unit
  have hu (i : Fin s.rayCount) : ‖d i‖ = 1 := by
    rw [radialLinearMap_norm, s.direction_unit]
  obtain ⟨c, hc, hbase, e, he, hlast, E, hE⟩ :=
    AngularSector.fullDiskComponents_from_homeomorph hn s.radius_pos d hd hu H f (fun _ => rfl)
  have hc0 : c ≠ 0 := norm_ne_zero_iff.mp (hc.trans_ne one_ne_zero)
  let Q := H.trans (AngularSector.unitRotationHomeomorph s.radius d c hc)
  let ep : Equiv.Perm (Fin s.rayCount) := (finRotate s.rayCount).symm.trans e
  have hangle {v z : Plane} (hv : v ≠ 0) (hz : z ≠ 0) :
      starMetricAngle g s o v z = positiveAngle
        ((arg (c * radialLinearMap K z) : Real.Angle) -
          (arg (c * radialLinearMap K v) : Real.Angle)) := by
    rw [unit_mul_arg_sub hc0 (radialLinearMap_ne_zero K hv)
      (radialLinearMap_ne_zero K hz), radialLinearMap_arg, radialLinearMap_arg]
    change positiveAngle (o.oangle (L v) (L z)) =
      positiveAngle ((arg (kahlerEquiv o w hw (L z)) : Real.Angle) -
        (arg (kahlerEquiv o w hw (L v)) : Real.Angle))
    rw [kahlerEquiv_oangle o w hw (L.map_ne_zero_iff.mpr hv) (L.map_ne_zero_iff.mpr hz)]
  have hQ (x : U) : (Q x).val = c * f x.val := rfl
  have hcomp_sub (a : ConnectedComponents U) : componentSet U a ⊆ U := by
    rintro _ ⟨x, _, rfl⟩
    exact x.property
  have hcoord {x : M} (hx : x ∈ U) :
      coordinates s.chart x - coordinates s.chart p ≠ 0 :=
    (StarHomeomorph.starComplementFullDiskHomeomorph s hfull ⟨x, hx⟩).property.1
  have hsector {x : M} (hx : x ∈ U) (i : Fin s.rayCount) :
      starMetricAngle g s o (s.direction (ep i))
          (coordinates s.chart x - coordinates s.chart p) <
        starMetricAngle g s o (s.direction (ep i))
          (s.direction (ep (finRotate s.rayCount i))) ↔
      c * f x ∈ AngularSector.sector s.radius
        ((Fin.cons (-Real.pi) (fun i => arg (c * d (e i))) : Fin (s.rayCount + 1) → ℝ) i.castSucc)
        ((Fin.cons (-Real.pi) (fun i => arg (c * d (e i))) : Fin (s.rayCount + 1) → ℝ) i.succ) := by
    rw [hangle (hdir _) (hcoord hx), hangle (hdir _) (hdir _)]
    exact cyclic_predecessor_metric_sector hn (fun i => c * d i) e he hlast
      ⟨⟨0, hn⟩, by rw [hbase, Complex.arg_neg_one]⟩ (Q ⟨x, hx⟩).property i
  refine ⟨ep, E, ?_, ?_⟩
  · intro a
    ext x
    constructor
    · intro hx
      have hxU := hcomp_sub a hx
      refine ⟨hxU, (hsector hxU (E a)).mpr ?_⟩
      rw [← hE a]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨hxU, hx⟩
      have him := (hsector hxU (E a)).mp hx
      rw [← hE a] at him
      obtain ⟨y, hy, hxy⟩ := him
      have hyU := hcomp_sub a hy
      have hval : (Q ⟨y, hyU⟩).val = (Q ⟨x, hxU⟩).val := by
        simpa only [hQ] using hxy
      have hsub := Q.injective (Subtype.ext hval)
      have heq : y = x := congrArg Subtype.val hsub
      exact heq ▸ hy
  · have ha (i : Fin s.rayCount) := hangle (hdir (ep i))
      (hdir (ep (finRotate s.rayCount i)))
    simp_rw [ha]
    exact cyclic_predecessor_metric_sum hn (fun i => c * d i) e he hlast

end P202.RadialGraphSectors

namespace P202.RadialGraphSectors
section HalfPlaneHelpers
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]
lemma areaForm_complex_right (o : Orientation ℝ V (Fin 2)) (L : ℂ ≃ₗ[ℝ] V) (z : ℂ) :
    o.areaForm (L 1) (L z) = z.im * o.areaForm (L 1) (L Complex.I) := by
  have heq : z = z.re • (1 : ℂ) + z.im • Complex.I := by
    simpa only [Complex.real_smul, mul_one] using (Complex.re_add_im z).symm
  conv_lhs => rw [heq, map_add, map_smul, map_smul,
    map_add, map_smul, map_smul, o.areaForm_apply_self]
  simp


lemma areaForm_complex_vertical_ne_zero (o : Orientation ℝ V (Fin 2))
    (L : ℂ ≃ₗ[ℝ] V) : o.areaForm (L 1) (L Complex.I) ≠ 0 := by
  intro hz
  have h := areaForm_complex_right o L (L.symm (o.rightAngleRotation (L 1)))
  rw [L.apply_symm_apply, o.areaForm_rightAngleRotation_right, hz, mul_zero] at h
  have h1 : L 1 ≠ 0 := L.map_ne_zero_iff.mpr one_ne_zero
  exact h1 (inner_self_eq_zero.mp h)

lemma exists_kahler_halfPlane (o : Orientation ℝ V (Fin 2)) (L : ℂ ≃ₗ[ℝ] V) :
    ∃ (w : ℂ) (hw : w ≠ 0), (w = 1 ∨ w = -1) ∧
      ∀ z : ℂ, 0 ≤ (kahlerEquiv o (L w) (L.map_ne_zero_iff.mpr hw) (L z)).im ↔ 0 ≤ z.im := by
  have hne := areaForm_complex_vertical_ne_zero o L
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · refine ⟨-1, by simp, Or.inr rfl, ?_⟩
    intro z
    change 0 ≤ (o.kahler (L (-1)) (L z)).im ↔ 0 ≤ z.im
    rw [map_neg, map_neg, LinearMap.neg_apply, Complex.neg_im,
      Orientation.kahler_apply_apply]
    simp only [Complex.add_im, Complex.ofReal_im, zero_add, Complex.smul_im,
      Complex.I_im, smul_eq_mul, mul_one]
    rw [areaForm_complex_right]
    constructor <;> intro h <;> nlinarith
  · refine ⟨1, one_ne_zero, Or.inl rfl, ?_⟩
    intro z
    simp only [kahlerEquiv_apply, Orientation.kahler_apply_apply, Complex.add_im,
      Complex.ofReal_im, zero_add, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.I_re, mul_zero, add_zero]
    rw [areaForm_complex_right]
    exact mul_nonneg_iff_of_pos_right hpos

end HalfPlaneHelpers

lemma linear_im_pos_iff (K : ℂ ≃ₗ[ℝ] ℂ)
    (hK : ∀ z : ℂ, 0 ≤ (K z).im ↔ 0 ≤ z.im) (z : ℂ) :
    0 < (K z).im ↔ 0 < z.im := by
  have h := hK (-z)
  simp only [map_neg, Complex.neg_im, neg_nonneg] at h
  simpa only [not_le] using not_congr h

open AngularSector PlaneComplexBridge in
def radialUpperRayComplementHomeomorph {n : ℕ} (K : ℂ ≃L[ℝ] ℂ)
    (r : ℝ) (d : Fin n → ℂ)
    (hK : ∀ z : ℂ, 0 < (K z).im ↔ 0 < z.im)
    (hcut : ∃ i, arg (d i) = Real.pi)
    (hcut' : ∃ i, arg (radialLinearMap K (d i)) = Real.pi) :
    upperRayComplement r d ≃ₜ upperRayComplement r (fun i => radialLinearMap K (d i)) where
  toFun x :=
    let y := radialRayComplementHomeomorph K r d ⟨x.val, x.property.1⟩
    ⟨y.val, y.property, by
      apply (arg_pos_iff_im_pos_of_slitPlane
        (rayComplement_subset_slitPlane _ r hcut' y.property)).mpr
      have hp := (arg_pos_iff_im_pos_of_slitPlane
        (rayComplement_subset_slitPlane d r hcut x.property.1)).mp x.property.2
      change 0 < (radialLinearMap K x.val).im
      rw [radialLinearMap, Complex.smul_im, smul_eq_mul]
      exact mul_pos (div_pos (norm_pos_iff.mpr x.property.1.1)
        (norm_pos_iff.mpr (K.map_ne_zero_iff.mpr x.property.1.1))) ((hK x.val).mpr hp)⟩
  invFun y :=
    let x := (radialRayComplementHomeomorph K r d).symm ⟨y.val, y.property.1⟩
    ⟨x.val, x.property, by
      apply (arg_pos_iff_im_pos_of_slitPlane
        (rayComplement_subset_slitPlane d r hcut x.property)).mpr
      have hp := (arg_pos_iff_im_pos_of_slitPlane
        (rayComplement_subset_slitPlane _ r hcut' y.property.1)).mp y.property.2
      apply (hK x.val).mp
      change 0 < (K (radialLinearMap K.symm y.val)).im
      rw [radialLinearMap, map_smul, K.apply_symm_apply, Complex.smul_im, smul_eq_mul]
      exact mul_pos (div_pos (norm_pos_iff.mpr y.property.1.1)
        (norm_pos_iff.mpr (K.symm.map_ne_zero_iff.mpr y.property.1.1))) hp⟩
  left_inv x := Subtype.ext (radialLinearMap_inverse K x)
  right_inv y := Subtype.ext (radialLinearMap_inverse K.symm y)
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun x : upperRayComplement r d => radialLinearMap K x.val)
    unfold radialLinearMap
    fun_prop (disch := intro x; exact norm_ne_zero_iff.mpr (K.map_ne_zero_iff.mpr x.property.1.1))
  continuous_invFun := by
    apply Continuous.subtype_mk
    unfold radialLinearMap
    fun_prop (disch := intro y; exact norm_ne_zero_iff.mpr (K.symm.map_ne_zero_iff.mpr y.property.1.1))


section HalfMetricComponents
variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = 2)]
open AngularSector PlaneComplexBridge

lemma halfDiskMetricSectors_from_homeomorph {X : Type*} [TopologicalSpace X]
    {U : Set X} {n : ℕ} {r : ℝ} (hr : 0 < r)
    (d : Fin (n + 2) → ℂ) (hd : Function.Injective d) (hu : ∀ i, ‖d i‖ = 1)
    (hhalf : ∀ i, 0 ≤ (d i).im) (hleft : ∃ i, d i = 1) (hright : ∃ i, d i = -1)
    (H : U ≃ₜ upperRayComplement r d) (f : X → ℂ)
    (hf : ∀ x : U, (H x).val = f x.val)
    (o : Orientation ℝ V (Fin 2)) (L : ℂ ≃ₗ[ℝ] V) :
    ∃ e : Equiv.Perm (Fin (n + 2)),
      ∃ E : ConnectedComponents U ≃ Fin (n + 1),
        (∀ a, P202Specs.SurfaceRegionConstruction.componentSet U a =
          {x | x ∈ U ∧ positiveAngle (o.oangle (L (d (e (E a).castSucc))) (L (f x))) <
            positiveAngle (o.oangle (L (d (e (E a).castSucc))) (L (d (e (E a).succ))))}) ∧
        (∑ i : Fin (n + 1), positiveAngle (o.oangle
          (L (d (e i.castSucc))) (L (d (e i.succ))))) = Real.pi := by
  obtain ⟨w, hw, hwchoice, hKnonneg⟩ := exists_kahler_halfPlane o L
  let K : ℂ ≃L[ℝ] ℂ := (L.trans (kahlerEquiv o (L w) (L.map_ne_zero_iff.mpr hw))).toContinuousLinearEquiv
  let D := fun i => radialLinearMap K (d i)
  have hKim (z : ℂ) : 0 ≤ (K z).im ↔ 0 ≤ z.im := hKnonneg z
  have hKpos (z : ℂ) : 0 < (K z).im ↔ 0 < z.im :=
    linear_im_pos_iff K.toLinearEquiv hKim z
  have hw0 : ∃ i, d i = w := by rcases hwchoice with rfl | rfl <;> assumption
  have hw1 : ∃ i, d i = -w := by
    rcases hwchoice with rfl | rfl
    · exact hright
    · simpa using hleft
  have hKw : arg (K w) = 0 := by
    change arg (o.kahler (L w) (L w)) = 0
    rw [o.kahler_apply_self, ← Complex.ofReal_pow]
    exact Complex.arg_ofReal_of_nonneg (sq_nonneg _)
  have hKwneg : arg (K (-w)) = Real.pi := by
    change arg (o.kahler (L w) (L (-w))) = Real.pi
    rw [map_neg, map_neg, o.kahler_apply_self, ← Complex.ofReal_pow, ← Complex.ofReal_neg]
    exact Complex.arg_ofReal_of_neg (neg_neg_of_pos (sq_pos_of_pos
      (norm_pos_iff.mpr (L.map_ne_zero_iff.mpr hw))))
  have hDleft : ∃ i, arg (D i) = 0 := by
    obtain ⟨i, hi⟩ := hw0
    exact ⟨i, by simp only [D, radialLinearMap_arg, hi, hKw]⟩
  have hDright : ∃ i, arg (D i) = Real.pi := by
    obtain ⟨i, hi⟩ := hw1
    exact ⟨i, by simp only [D, radialLinearMap_arg, hi, hKwneg]⟩
  have hcut : ∃ i, arg (d i) = Real.pi := by
    obtain ⟨i, hi⟩ := hright
    exact ⟨i, by rw [hi, Complex.arg_neg_one]⟩
  have hDhalf (i) : 0 ≤ (D i).im := by
    change 0 ≤ (radialLinearMap K (d i)).im
    rw [radialLinearMap, Complex.smul_im, smul_eq_mul]
    exact mul_nonneg (div_nonneg (norm_nonneg _) (norm_nonneg _)) ((hKim _).mpr (hhalf i))
  have hDunit (i) : ‖D i‖ = 1 := by rw [radialLinearMap_norm, hu]
  have hDinj : Function.Injective D := radialLinearMap_injective_on_unit K d hd hu
  let HK := H.trans (radialUpperRayComplementHomeomorph K r d hKpos hcut hDright)
  let F := fun x => radialLinearMap K (f x)
  have hHK (x : U) : (HK x).val = F x.val := by
    change radialLinearMap K (H x).val = radialLinearMap K (f x.val)
    rw [hf]
  obtain ⟨e, he, hfirst, hlast, E, hE⟩ := halfDiskComponents_from_homeomorph hr
    D hDinj hDunit hDhalf hDleft hDright HK F hHK
  let c := fun i => arg (D (e i))
  have hc : StrictMono c := he
  change c 0 = 0 at hfirst
  change c (Fin.last (n + 1)) = Real.pi at hlast
  have hangle {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
      positiveAngle (o.oangle (L x) (L y)) =
        positiveAngle ((arg (radialLinearMap K y) : Real.Angle) -
          (arg (radialLinearMap K x) : Real.Angle)) := by
    rw [radialLinearMap_arg, radialLinearMap_arg]
    congr 1
    exact kahlerEquiv_oangle o (L w) (L.map_ne_zero_iff.mpr hw)
      (L.map_ne_zero_iff.mpr hx) (L.map_ne_zero_iff.mpr hy)
  have hd0 (i) : d i ≠ 0 := norm_ne_zero_iff.mp ((hu i).trans_ne one_ne_zero)
  have hbound (i : Fin (n + 2)) : c i ∈ Icc 0 Real.pi := by
    refine ⟨?_, Complex.arg_le_pi _⟩
    have h := hc.monotone (Fin.zero_le i)
    rw [hfirst] at h
    exact h
  have hsector (i : Fin (n + 1)) (x : X) (hx : x ∈ U) :
      F x ∈ sector r (c i.castSucc) (c i.succ) ↔
        positiveAngle (o.oangle (L (d (e i.castSucc))) (L (f x))) <
          positiveAngle (o.oangle (L (d (e i.castSucc))) (L (d (e i.succ)))) := by
    have hFx : F x ∈ upperRayComplement r D := by
      rw [← hHK ⟨x, hx⟩]
      exact (HK ⟨x, hx⟩).property
    have hfx0 : f x ≠ 0 := by
      rw [← hf ⟨x, hx⟩]
      exact (H ⟨x, hx⟩).property.1.1
    have ht : arg (F x) ∈ Ioo (-Real.pi) Real.pi := by
      exact ⟨Complex.neg_pi_lt_arg _, (Complex.arg_le_pi _).lt_of_ne
        (Complex.mem_slitPlane_iff_arg.mp (rayComplement_subset_slitPlane D r hDright hFx.1)).1⟩
    rw [hangle (hd0 _) hfx0, hangle (hd0 _) (hd0 _)]
    change (_ ∧ _ ∧ arg (F x) ∈ Ioo (c i.castSucc) (c i.succ)) ↔
      positiveAngle ((arg (F x) : Real.Angle) - (c i.castSucc : Real.Angle)) <
        positiveAngle ((c i.succ : Real.Angle) - (c i.castSucc : Real.Angle))
    rw [positiveAngle_sub_coe_iff (by linarith [(hbound i.castSucc).1, Real.pi_pos])
      (hc (Fin.castSucc_lt_succ (i := i))) (hbound i.succ).2 ht]
    exact ⟨fun h => h.2.2, fun h => ⟨hFx.1.1, hFx.1.2.1, h⟩⟩
  refine ⟨e, E, ?_, ?_⟩
  · intro a
    ext x
    constructor
    · intro hx
      have hxU : x ∈ U := by rcases hx with ⟨y, _, rfl⟩; exact y.property
      refine ⟨hxU, (hsector (E a) x hxU).mp ?_⟩
      rw [← hE a]
      exact ⟨x, hx, rfl⟩
    · rintro ⟨hxU, hx⟩
      have hFx := (hsector (E a) x hxU).mpr hx
      rw [← hE a] at hFx
      obtain ⟨y, hy, hyx⟩ := hFx
      have hyU : y ∈ U := by rcases hy with ⟨z, _, rfl⟩; exact z.property
      have hyx' : y = x := by
        have hxy : (⟨y, hyU⟩ : U) = ⟨x, hxU⟩ := HK.injective (Subtype.ext
          ((hHK ⟨y, hyU⟩).trans (hyx.trans (hHK ⟨x, hxU⟩).symm)))
        exact congrArg Subtype.val hxy
      rwa [← hyx']
  · have hgap (i : Fin (n + 1)) :
        positiveAngle (o.oangle (L (d (e i.castSucc))) (L (d (e i.succ)))) =
          c i.succ - c i.castSucc := by
      rw [hangle (hd0 _) (hd0 _)]
      change positiveAngle ((c i.succ : Real.Angle) - (c i.castSucc : Real.Angle)) = _
      rw [← Real.Angle.coe_sub, positiveAngle_coe]
      exact ⟨sub_pos.mpr (hc (Fin.castSucc_lt_succ (i := i))),
        by linarith [(hbound i.castSucc).1, (hbound i.succ).2, Real.pi_pos]⟩
    simp_rw [hgap]
    rw [sum_adjacent_differences c, hlast, hfirst, sub_zero]
end HalfMetricComponents

/-- The genuine boundary half-disk components are precisely the positive
metric sectors for either tangent orientation. -/
theorem halfStarMetricSectors {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 2 .halfSpace M} (g : RiemannianMetric S)
    {G : EmbeddedGraph S} {p : M} (s : GraphStar G p)
    (o : Orientation ℝ (TangentSpace S p) (Fin 2))
    (hp : p ∈ intrinsicBoundary S) (hB : intrinsicBoundary S ⊆ G.carrier) :
    ∃ n : ℕ, ∃ hn : s.rayCount = n + 2,
      let d := fun i : Fin (n + 2) => s.direction (Fin.cast hn.symm i)
      ∃ e : Equiv.Perm (Fin (n + 2)),
        ∃ E : ConnectedComponents (s.neighborhood \ G.carrier : Set M) ≃ Fin (n + 1),
          (∀ a, componentSet (s.neighborhood \ G.carrier) a =
            starMetricSector g s o (d (e (E a).castSucc)) (d (e (E a).succ))) ∧
          (∑ i : Fin (n + 1), starMetricAngle g s o
            (d (e i.castSucc)) (d (e i.succ))) = Real.pi := by
  letI := (metricCore g p).toNormedAddCommGroup
  letI := InnerProductSpace.ofCore (metricCore g p).toCore
  letI := (SmoothManifolds.tangent_dimension S p).1
  letI : Fact (Module.finrank ℝ (TangentSpace S p) = 2) :=
    ⟨(SmoothManifolds.tangent_dimension S p).2⟩
  have htwo := graphStar_boundary_two_le_rayCount s hp hB
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_le htwo
  have hn : s.rayCount = n + 2 := by omega
  let e0 : Fin (n + 2) ≃ Fin s.rayCount := finCongr hn.symm
  let d := fun i => PlaneComplexBridge.planeComplex (s.direction (e0 i))
  have hd : Function.Injective d :=
    (PlaneComplexBridge.planeComplex.injective.comp s.direction_injective).comp e0.injective
  have hu (i) : ‖d i‖ = 1 := by
    dsimp [d]
    rw [PlaneComplexBridge.planeComplex.norm_map, s.direction_unit]
  have hh (i) : 0 ≤ (d i).im := by
    dsimp [d]
    rw [PlaneComplexBridge.planeComplex_im]
    exact graphStar_direction_second_nonneg s hp _
  obtain ⟨i0, i1, _, h0, h1, _⟩ := graphStar_boundary_rays s hp hB
  have hl : ∃ i, d i = 1 := by
    refine ⟨e0.symm i0, ?_⟩
    simp only [d, e0.apply_symm_apply, h0, StarHomeomorph.planeComplex_reference]
  have hr : ∃ i, d i = -1 := by
    refine ⟨e0.symm i1, ?_⟩
    simp only [d, e0.apply_symm_apply, h1, map_neg, StarHomeomorph.planeComplex_reference]
  let H := (StarHomeomorph.starComplementBoundaryComplexHomeomorph s hp hB).trans
    (Homeomorph.setCongr (AngularSector.upperRayComplement_reindex s.radius
      (fun i => PlaneComplexBridge.planeComplex (s.direction i)) e0).symm)
  let f := fun x => PlaneComplexBridge.planeComplex
    (coordinates s.chart x - coordinates s.chart p)
  have hf (x : (s.neighborhood \ G.carrier : Set M)) : (H x).val = f x.val := rfl
  let L := PlaneComplexBridge.planeComplex.symm.toLinearEquiv.trans (starTangentEquiv s)
  obtain ⟨e, E, hE, hsum⟩ := halfDiskMetricSectors_from_homeomorph s.radius_pos d
    hd hu hh hl hr H f hf o L
  refine ⟨n, hn, e, E, ?_, ?_⟩
  · intro a
    simpa only [starMetricSector, starMetricAngle, d, e0, finCongr_apply, f, L, LinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, PlaneComplexBridge.planeComplex.symm_apply_apply]
      using hE a
  · simpa only [starMetricAngle, d, e0, finCongr_apply, L, LinearEquiv.trans_apply,
      LinearIsometryEquiv.coe_toLinearEquiv, PlaneComplexBridge.planeComplex.symm_apply_apply]
      using hsum


end P202.RadialGraphSectors
