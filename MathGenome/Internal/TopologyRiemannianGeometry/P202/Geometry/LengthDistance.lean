import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LengthDistance
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricFoundation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalShortCurves
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LocalCurveTrapping
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

set_option autoImplicit false

namespace P202.Geometry.LengthDistance
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  P202.MetricData P202.CurveData P202.DistanceData
open Set Filter
open scoped Topology
universe u

abbrev HasPiecewiseC1Path := @P202.DistanceData.HasPiecewiseC1Path
noncomputable abbrev pathLengths := @P202.DistanceData.pathLengths
noncomputable abbrev componentDistance := @P202.DistanceData.componentDistance

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

theorem length_nonneg (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) : 0 ≤ length g c :=
  intervalIntegral.integral_nonneg_of_forall c.ordered fun t =>
    P202.Geometry.SmoothMetrics.tangentNorm_nonneg g (c t) (velocity S c t)

theorem pathLengths_bddBelow (g : RiemannianMetric S) (p q : M) :
    BddBelow (pathLengths g p q) := by
  refine ⟨0, ?_⟩
  rintro L ⟨a, b, c, _, _, rfl⟩
  exact length_nonneg g c

theorem path_refl (p : M) : HasPiecewiseC1Path S p p := by
  obtain ⟨c, hc, _⟩ := P202.Geometry.MetricFoundation.stationary_exists S 0 0 le_rfl p
  exact ⟨0, 0, c, hc 0, hc 0⟩

theorem path_symm {p q : M} (h : HasPiecewiseC1Path S p q) :
    HasPiecewiseC1Path S q p := by
  obtain ⟨a, b, c, hp, hq⟩ := h
  obtain ⟨d, hd, _⟩ := P202.Geometry.MetricFoundation.reversal_exists c
  refine ⟨a, b, d, ?_, ?_⟩
  · simpa only [hd, add_sub_cancel_left] using hq
  · simpa only [hd, add_sub_cancel_right] using hp

theorem pathLengths_refl (g : RiemannianMetric S) (p : M) :
    0 ∈ pathLengths g p p := by
  obtain ⟨c, hc, hL⟩ := P202.Geometry.MetricFoundation.stationary_exists S 0 0 le_rfl p
  exact ⟨0, 0, c, hc 0, hc 0, (hL g).1.symm⟩

theorem pathLengths_symm (g : RiemannianMetric S) (p q : M) :
    pathLengths g p q = pathLengths g q p := by
  have rev (p q : M) : pathLengths g p q ⊆ pathLengths g q p := by
    rintro L ⟨a, b, c, hp, hq, rfl⟩
    obtain ⟨d, hd, hL⟩ := P202.Geometry.MetricFoundation.reversal_length_exists g c
    refine ⟨a, b, d, ?_, ?_, hL.symm⟩
    · simpa only [hd, add_sub_cancel_left] using hq
    · simpa only [hd, add_sub_cancel_right] using hp
  exact Subset.antisymm (rev p q) (rev q p)

/-- Move the parameter interval without changing the curve or its length.
This also handles singleton intervals; no division by their duration occurs. -/
theorem translate_curve (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) (l : ℝ) :
    ∃ d : PiecewiseC1Curve S l (l + (b - a)),
      EqOn d (fun t => c (t - l + a)) (Icc l (l + (b - a))) ∧
      length g d = length g c := by
  let f : ℝ → ℝ := fun t => t - l + a
  have hlr : l ≤ l + (b - a) := by linarith [c.ordered]
  have hmaps : MapsTo f (Icc l (l + (b - a))) (Icc a b) := by
    intro t ht
    dsimp [f]
    constructor <;> linarith [ht.1, ht.2]
  have hmono : StrictMonoOn f (Icc l (l + (b - a))) := by
    intro x hx y hy hxy
    dsimp [f]
    linarith
  have honto : SurjOn f (Icc l (l + (b - a))) (Icc a b) := by
    intro t ht
    refine ⟨t + l - a, ?_, ?_⟩
    · constructor <;> linarith [ht.1, ht.2]
    · dsimp [f]; ring
  let node : Fin 2 → ℝ := fun i => if i = 0 then l else l + (b - a)
  have hnode : Monotone node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [node]
  have hderiv (t : ℝ) : HasDerivAt f 1 t := by
    simpa only [f, id_eq] using ((hasDerivAt_id t).sub_const l).add_const a
  have hregular (i : Fin 1) :
      RegularRealC1On f (Icc (node i.castSucc) (node i.succ)) := by
    intro t ht
    refine ⟨f, ?_, rfl, Filter.EventuallyEq.rfl, ?_⟩
    · exact ((contDiff_id.sub contDiff_const).add contDiff_const).contDiffAt
    · rw [(hderiv t).deriv]; norm_num
  obtain ⟨φ, hφ⟩ := P202.Geometry.PiecewiseCurves.parameter_representation
    c.ordered hlr f hmaps hmono honto 1 node hnode
    (by simp [node]) (by simp [node]) hregular
  obtain ⟨d, hd, hL⟩ := P202.Geometry.MetricFoundation.reparametrization_length_exists g c φ
  refine ⟨d, ?_, hL⟩
  intro t ht
  rw [hd, hφ ht]

theorem pathLengths_add (g : RiemannianMetric S) {p q r : M} {A B : ℝ}
    (hA : A ∈ pathLengths g p q) (hB : B ∈ pathLengths g q r) :
    A + B ∈ pathLengths g p r := by
  obtain ⟨a, b, c, hp, hq, rfl⟩ := hA
  obtain ⟨l, z, d, hq', hr, rfl⟩ := hB
  obtain ⟨e, he, hLe⟩ := translate_curve g d b
  have hstart : e b = d l := by
    simpa only [sub_self, zero_add] using he ⟨le_rfl, by linarith [d.ordered]⟩
  have hend : e (b + (z - l)) = d z := by
    have h := he ⟨by linarith [d.ordered], le_rfl⟩
    convert h using 1 <;> congr 1 <;> ring
  obtain ⟨f, hfc, hfe, hLf⟩ :=
    P202.Geometry.MetricFoundation.concatenation_length g c e (hq.trans (hstart.trans hq').symm)
  exact ⟨a, b + (z - l), f,
    (hfc ⟨le_rfl, c.ordered⟩).trans hp,
    (hfe ⟨by linarith [d.ordered], le_rfl⟩).trans (hend.trans hr),
    by rw [hLf, hLe]⟩

theorem path_trans {p q r : M} (hpq : HasPiecewiseC1Path S p q)
    (hqr : HasPiecewiseC1Path S q r) : HasPiecewiseC1Path S p r := by
  obtain ⟨g⟩ := P202.Geometry.MetricFoundation.exists_metric S
  obtain ⟨a, b, c, hp, hq⟩ := hpq
  obtain ⟨l, z, d, hq', hr⟩ := hqr
  obtain ⟨a', b', e, hp', hr', _⟩ := pathLengths_add g
    ⟨a, b, c, hp, hq, rfl⟩ ⟨l, z, d, hq', hr, rfl⟩
  exact ⟨a', b', e, hp', hr'⟩

theorem path_mem_component {p q : M} (h : HasPiecewiseC1Path S p q) :
    q ∈ connectedComponent p := by
  obtain ⟨a, b, c, rfl, rfl⟩ := h
  exact ((isPreconnected_Icc.image c c.continuousOn).subset_connectedComponent
    (mem_image_of_mem c ⟨le_rfl, c.ordered⟩))
    (mem_image_of_mem c ⟨c.ordered, le_rfl⟩)

theorem pathLengths_empty_of_different_components (g : RiemannianMetric S)
    {p q : M} (h : q ∉ connectedComponent p) : pathLengths g p q = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro L ⟨a, b, c, hp, hq, _⟩
  exact h (path_mem_component ⟨a, b, c, hp, hq⟩)

theorem pathLengths_nonempty_iff (g : RiemannianMetric S) (p q : M) :
    (pathLengths g p q).Nonempty ↔ HasPiecewiseC1Path S p q := by
  constructor
  · rintro ⟨L, a, b, c, hp, hq, _⟩
    exact ⟨a, b, c, hp, hq⟩
  · rintro ⟨a, b, c, hp, hq⟩
    exact ⟨length g c, a, b, c, hp, hq, rfl⟩

/-- The global connectedness argument needs only local existence of coordinate
paths. The conclusion is about the original curve class, not continuous paths. -/
theorem path_exists_of_local
    (hlocal : ∀ p : M, ∃ U : Set M, IsOpen U ∧ p ∈ U ∧
      ∀ q ∈ U, HasPiecewiseC1Path S p q) (p q : M) :
    HasPiecewiseC1Path S p q ↔ q ∈ connectedComponent p := by
  have hopen : IsOpen {q | HasPiecewiseC1Path S p q} := by
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    obtain ⟨U, hU, hqU, hpath⟩ := hlocal q
    exact ⟨U, fun z hz => path_trans hq (hpath z hz), hU, hqU⟩
  have hclosed : IsClosed {q | HasPiecewiseC1Path S p q} := by
    rw [← isOpen_compl_iff]
    apply isOpen_iff_forall_mem_open.mpr
    intro q hq
    obtain ⟨U, hU, hqU, hpath⟩ := hlocal q
    refine ⟨U, ?_, hU, hqU⟩
    intro z hz hpz
    exact hq (path_trans hpz (path_symm (hpath z hz)))
  exact ⟨path_mem_component, fun hq =>
    (IsClopen.connectedComponent_subset ⟨hclosed, hopen⟩ (path_refl p)) hq⟩

/-- Straight segments in small coordinate balls are valid curves even at
boundary points: convexity is applied to the closed half-space model, while
the regularity witness takes values in its ambient Euclidean space. -/
theorem local_path_exists (p : M) :
    ∃ U : Set M, IsOpen U ∧ p ∈ U ∧ ∀ q ∈ U, HasPiecewiseC1Path S p q := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨r, hr, hrT⟩ := Metric.isOpen_iff.mp e.open_target (e p) (e.map_source hp)
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e p) r,
    e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hp, by simpa using hr⟩, ?_⟩
  intro q hq
  let x : Euclidean n := (e p).val
  let y : Euclidean n := (e q).val
  let σ : Icc (0 : ℝ) 1 → ModelSpace n kind := fun t =>
    ⟨AffineMap.lineMap x y t.val,
      (SmoothManifolds.convex_modelSet n kind).lineMap_mem
        (e p).property (e q).property t.property⟩
  have hσ : Continuous σ := by
    apply Continuous.subtype_mk
    exact (AffineMap.contDiff_lineMap (n := 1) x y).continuous.comp continuous_subtype_val
  have hσT (t : Icc (0 : ℝ) 1) : σ t ∈ e.target := by
    apply hrT
    change AffineMap.lineMap x y t.val ∈ Metric.ball x r
    exact (convex_ball x r).lineMap_mem (by simpa using hr) hq.2 t.property
  let c : Icc (0 : ℝ) 1 → M := e.symm ∘ σ
  have hc : Continuous c := e.symm.continuousOn.comp_continuous hσ hσT
  have hsource (t : Icc (0 : ℝ) 1) : c t ∈ e.source := e.map_target (hσT t)
  have hcoord (t : Icc (0 : ℝ) 1) :
      (e (c t)).val = AffineMap.lineMap x y t.val := by
    exact congrArg Subtype.val (e.right_inv (hσT t))
  let f : ℝ → M := IccExtend (by norm_num : (0 : ℝ) ≤ 1) c
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t = c ⟨t, ht⟩ :=
    IccExtend_of_mem _ _ ht
  have hfcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (e (f t)).val = AffineMap.lineMap x y t := by rw [hf t ht]; exact hcoord _
  have hregular : CoordinateC1On S f (Icc 0 1) := by
    intro t ht
    refine ⟨e, he, ?_, AffineMap.lineMap x y,
      (AffineMap.contDiff_lineMap x y).contDiffAt, (hfcoord t ht).symm, ?_⟩
    · rw [hf t ht]; exact hsource _
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hfcoord s hs
  let d : PiecewiseC1Curve S 0 1 := {
    ordered := by norm_num
    toFun := f
    continuousOn := (continuous_IccExtend_iff.mpr hc).continuousOn
    pieces := 1
    node := ![0, 1]
    monotone_node := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> norm_num at *
    first_node := rfl
    last_node := rfl
    regular := by intro i; fin_cases i; exact hregular }
  refine ⟨0, 1, d, ?_, ?_⟩
  · change f 0 = p
    rw [hf 0 (by norm_num)]
    change e.symm (σ ⟨0, by norm_num⟩) = p
    have hσ0 : σ ⟨0, by norm_num⟩ = e p := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_zero x y
    rw [hσ0, e.left_inv hp]
  · change f 1 = q
    rw [hf 1 (by norm_num)]
    change e.symm (σ ⟨1, by norm_num⟩) = q
    have hσ1 : σ ⟨1, by norm_num⟩ = e q := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_one x y
    rw [hσ1, e.left_inv hq.1]

theorem path_exists (S : SmoothManifold n kind M) (p q : M) :
    HasPiecewiseC1Path S p q ↔ q ∈ connectedComponent p :=
  path_exists_of_local local_path_exists p q

theorem component_finite (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) :
    (pathLengths g p.val q.val).Nonempty ∧ BddBelow (pathLengths g p.val q.val) := by
  refine ⟨(pathLengths_nonempty_iff g p q).mpr ((path_exists S p q).mpr ?_),
    pathLengths_bddBelow g p q⟩
  rw [← connectedComponent_eq p.property]
  exact q.property

theorem componentDistance_nonneg (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) : 0 ≤ componentDistance g o p q := by
  apply Real.sInf_nonneg
  rintro L ⟨a, b, c, _, _, rfl⟩
  exact length_nonneg g c

theorem componentDistance_self (g : RiemannianMetric S) (o : M)
    (p : connectedComponent o) : componentDistance g o p p = 0 := by
  apply le_antisymm
  · exact csInf_le (pathLengths_bddBelow g p p) (pathLengths_refl g p)
  · exact componentDistance_nonneg g o p p

theorem componentDistance_comm (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) :
    componentDistance g o p q = componentDistance g o q p := by
  exact congrArg sInf (pathLengths_symm g p q)

theorem componentDistance_le_length (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (hp : c a = p.val) (hq : c b = q.val) :
    componentDistance g o p q ≤ length g c :=
  csInf_le (pathLengths_bddBelow g p q) ⟨a, b, c, hp, hq, rfl⟩

/-- Triangle inequality for reachable triples, using infimum lower bounds
twice. Path finiteness is an explicit helper hypothesis, not an assumption in
the independent full theorem specification. -/
theorem componentDistance_triangle_of_paths (g : RiemannianMetric S) (o : M)
    (p q r : connectedComponent o) (hpq : HasPiecewiseC1Path S p.val q.val)
    (hqr : HasPiecewiseC1Path S q.val r.val) :
    componentDistance g o p r ≤ componentDistance g o p q + componentDistance g o q r := by
  have hA := (pathLengths_nonempty_iff g p.val q.val).mpr hpq
  have hB := (pathLengths_nonempty_iff g q.val r.val).mpr hqr
  have h : componentDistance g o p r - componentDistance g o q r ≤
      componentDistance g o p q := by
    apply le_csInf hA
    intro x hx
    have hy : componentDistance g o p r - x ≤ componentDistance g o q r := by
      apply le_csInf hB
      intro y hy
      have hz : componentDistance g o p r ≤ x + y :=
        csInf_le (pathLengths_bddBelow g p r) (pathLengths_add g hx hy)
      linarith
    linarith
  linarith

theorem componentDistance_triangle (g : RiemannianMetric S) (o : M)
    (p q r : connectedComponent o) :
    componentDistance g o p r ≤ componentDistance g o p q + componentDistance g o q r :=
  componentDistance_triangle_of_paths g o p q r
    ((pathLengths_nonempty_iff g p q).mp (component_finite g o p q).1)
    ((pathLengths_nonempty_iff g q r).mp (component_finite g o q r).1)

theorem zero_dimension {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold 0 kind M) (o : M) : connectedComponent o = {o} := by
  letI := SmoothManifolds.TopologicalManifold.toChartedSpace S.topologicalManifold
  letI : DiscreteTopology M := ChartedSpace.discreteTopology (ModelSpace 0 kind) M
  exact connectedComponent_eq_singleton o

theorem componentDistance_lt_iff (g : RiemannianMetric S) (o : M)
    (p q : connectedComponent o) (ε : ℝ) :
    componentDistance g o p q < ε ↔
      ∃ a b : ℝ, ∃ c : PiecewiseC1Curve S a b,
        c a = p.val ∧ c b = q.val ∧ length g c < ε := by
  rw [componentDistance, P202.DistanceData.componentDistance,
    csInf_lt_iff (component_finite g o p q).2 (component_finite g o p q).1]
  constructor
  · rintro ⟨L, ⟨a, b, c, hp, hq, rfl⟩, hL⟩
    exact ⟨a, b, c, hp, hq, hL⟩
  · rintro ⟨a, b, c, hp, hq, hL⟩
    exact ⟨length g c, ⟨a, b, c, hp, hq, rfl⟩, hL⟩

theorem componentDistance_lt_mem_of_trapping (g : RiemannianMetric S)
    (htrap : LocalCurveTrapping g) (o : M) (p : connectedComponent o)
    (U : Set M) (hU : IsOpen U) (hp : p.val ∈ U) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ q : connectedComponent o,
      componentDistance g o p q < ε → q.val ∈ U := by
  obtain ⟨ε, hε, hcurves⟩ := htrap p.val U hU hp
  refine ⟨ε, hε, ?_⟩
  intro q hq
  obtain ⟨a, b, c, hp, hq, hL⟩ := (componentDistance_lt_iff g o p q ε).mp hq
  exact hq ▸ hcurves c hp hL

theorem componentDistance_eq_zero_iff_of_trapping (g : RiemannianMetric S)
    (htrap : LocalCurveTrapping g) (o : M) (p q : connectedComponent o) :
    componentDistance g o p q = 0 ↔ p = q := by
  constructor
  · intro hzero
    apply Subtype.ext
    by_contra hne
    letI := S.topologicalManifold.hausdorff
    obtain ⟨ε, hε, hU⟩ := componentDistance_lt_mem_of_trapping g htrap o p
      ({q.val}ᶜ) isClosed_singleton.isOpen_compl (by simpa using hne)
    have h := hU q (by simpa only [hzero] using hε)
    exact h (Set.mem_singleton q.val)
  · rintro rfl
    exact componentDistance_self g o p

theorem componentDistance_isOpen_iff_of_local (g : RiemannianMetric S)
    (hshort : LocalShortCurves g) (htrap : LocalCurveTrapping g)
    (o : M) (s : Set (connectedComponent o)) :
    IsOpen s ↔ ∀ p ∈ s, ∃ ε > 0, ∀ q,
      componentDistance g o p q < ε → q ∈ s := by
  constructor
  · intro hs p hp
    obtain ⟨U, hU, hsU⟩ := isOpen_induced_iff.mp hs
    have hpU : p.val ∈ U := by rwa [← hsU] at hp
    obtain ⟨ε, hε, hball⟩ := componentDistance_lt_mem_of_trapping g htrap o p U hU hpU
    refine ⟨ε, hε, ?_⟩
    intro q hq
    rw [← hsU]
    exact hball q hq
  · intro hs
    apply isOpen_iff_forall_mem_open.mpr
    intro p hp
    obtain ⟨ε, hε, hball⟩ := hs p hp
    obtain ⟨U, hU, hpU, hcurves⟩ := hshort p.val ε hε
    refine ⟨Subtype.val ⁻¹' U, ?_, hU.preimage continuous_subtype_val, hpU⟩
    intro q hq
    obtain ⟨a, b, c, hc0, hc1, hL⟩ := hcurves q.val hq
    exact hball q ((componentDistance_le_length g o p q c hc0 hc1).trans_lt hL)

/-- Global assembly from the two local geometric estimates. -/
theorem component_metric_of_local (g : RiemannianMetric S)
    (hshort : LocalShortCurves g) (htrap : LocalCurveTrapping g) (o : M) :
    ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q := by
  let d := MetricSpace.ofDistTopology (componentDistance g o)
    (componentDistance_self g o) (componentDistance_comm g o)
    (componentDistance_triangle g o) (componentDistance_isOpen_iff_of_local g hshort htrap o)
    (fun p q => (componentDistance_eq_zero_iff_of_trapping g htrap o p q).mp)
  exact ⟨d, rfl, fun _ _ => rfl⟩

theorem zero_dimension_local_short {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 kind M} (g : RiemannianMetric S) : LocalShortCurves g := by
  letI := SmoothManifolds.TopologicalManifold.toChartedSpace S.topologicalManifold
  letI : DiscreteTopology M := ChartedSpace.discreteTopology (ModelSpace 0 kind) M
  intro p ε hε
  refine ⟨{p}, isOpen_discrete _, by simp, ?_⟩
  intro q hq
  have hqp : q = p := Set.mem_singleton_iff.mp hq
  obtain ⟨c, hc, hL⟩ := P202.Geometry.MetricFoundation.stationary_exists S 0 0 le_rfl p
  exact ⟨0, 0, c, hc 0, (hc 0).trans hqp.symm, by simpa only [(hL g).1] using hε⟩

theorem zero_dimension_local_trapping {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 kind M} (g : RiemannianMetric S) : LocalCurveTrapping g := by
  intro p U hU hp
  refine ⟨1, zero_lt_one, ?_⟩
  intro a b c hc hL
  have hcomp : c b ∈ connectedComponent p := path_mem_component ⟨a, b, c, hc, rfl⟩
  rw [zero_dimension S p] at hcomp
  rwa [Set.mem_singleton_iff.mp hcomp]

theorem zero_dimension_metric {kind : ModelKind} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold 0 kind M} (g : RiemannianMetric S) (o : M) :
    ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q :=
  component_metric_of_local g (zero_dimension_local_short g) (zero_dimension_local_trapping g) o

/-- Assembly of the entire source theorem from the local geometric estimates. -/
theorem metric_distance_of_local :
    P202Specs.Geometry.LengthDistance.metric_distance_of_localType.{u} := by
  intro hshort htrap
  refine ⟨P202.Geometry.MetricFoundation.exists_metric,
    P202.Geometry.MetricFoundation.pullback_metric_original,
    P202.Geometry.MetricFoundation.localIsometry_length_exists,
    @path_exists, @component_finite, ?_, @zero_dimension⟩
  intro n kind M inst S g o
  exact component_metric_of_local g (hshort g) (htrap g) o

/-- The upstream short-curve estimate uses the same intrinsic metric and
compact-interval curve objects; only the manifold argument is explicit there. -/
theorem local_short_curves (g : RiemannianMetric S) : LocalShortCurves g :=
  P202.Geometry.LocalShortCurves.local_short_curves S g

/-- The upstream no-escape estimate quantifies explicitly over the interval
endpoints. Here they are inferred from the curve, with no change of scope. -/
theorem local_curve_trapping (g : RiemannianMetric S) : LocalCurveTrapping g := by
  intro p U hU hp
  obtain ⟨ε, hε, hcurves⟩ :=
    P202.Geometry.LocalCurveTrapping.local_curve_trapping g p U hU hp
  exact ⟨ε, hε, fun {a b} c hc hL => hcurves a b c hc hL⟩

/-- The length infimum is a metric on each connected component, and its
topology is the original subspace topology, for either model kind in every
dimension. No distance is assigned between distinct components. -/
theorem component_metric (g : RiemannianMetric S) (o : M) :
    ∃ d : MetricSpace (connectedComponent o),
      d.toUniformSpace.toTopologicalSpace =
        (inferInstance : TopologicalSpace (connectedComponent o)) ∧
      ∀ p q, @dist _ d.toDist p q = componentDistance g o p q :=
  component_metric_of_local g (local_short_curves g) (local_curve_trapping g) o

/-- Theorem 6.1, including its smooth-boundary extension and rank-zero case. -/
theorem metric_distance : P202Specs.Geometry.LengthDistance.metric_distanceType.{u} :=
  metric_distance_of_local (@local_short_curves) (@local_curve_trapping)

end P202.Geometry.LengthDistance
