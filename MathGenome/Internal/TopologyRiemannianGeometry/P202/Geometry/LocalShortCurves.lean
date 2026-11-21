import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalShortCurves
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricFoundation
import Mathlib.Analysis.Calculus.Deriv.AffineMap
import Mathlib.Analysis.Calculus.AddTorsor.AffineMap

set_option autoImplicit false
namespace P202.Geometry.LocalShortCurves
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  P202.MetricData P202.CurveData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- Evaluation of the genuine metric norm in a tangent frame, written as the
finite Gram polynomial so that it is defined even away from the chart source. -/
noncomputable def coordinateNorm (g : RiemannianMetric S)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (v : Euclidean n) : ℝ :=
  let B := (tangentRealization S).space.bundle
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  Real.sqrt (∑ j : Fin n, ∑ k : Fin n,
    v j * (v k * g.form p ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))))

@[simp] theorem coordinateNorm_zero (g : RiemannianMetric S)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val) (p : M) :
    coordinateNorm g e he p 0 = 0 := by
  simp [coordinateNorm]

theorem coordinateNorm_eq (g : RiemannianMetric S)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (v : TangentSpace S p) :
    coordinateNorm g e he p
      ((tangentStructure S).fiberCoordinates.equiv e he p hp v) =
      tangentNorm g p v := by
  let B := (tangentRealization S).space.bundle
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  have hpB : p ∈ B.baseSet i := by
    change p ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  have hcoord : B.fiberCoordinates i p hpB v =
      (tangentStructure S).fiberCoordinates.equiv e he p hp v := by
    rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply]
    exact (tangentRealization S).coordinates i p hp v
  have hbil := SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i p hpB)
    (g.form p) v v
  simp only [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
    hcoord] at hbil
  exact congrArg Real.sqrt hbil.symm

/-- Joint continuity in the base and vector follows directly from metric
smoothness; no norm bound or speed hypothesis is added. -/
theorem coordinateNorm_continuousAt (g : RiemannianMetric S)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (v : Euclidean n) :
    ContinuousAt (fun z : M × Euclidean n => coordinateNorm g e he z.1 z.2) (p, v) := by
  let B := (tangentRealization S).space.bundle
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e, he⟩
  have hpB : p ∈ B.baseSet i := by
    change p ∈ (tangentRealization S).space.bundle.baseSet i
    rw [(tangentRealization S).baseSet]
    exact hp
  have hgram (j k : Fin n) : ContinuousAt (fun r : M =>
      g.form r ((B.trivialization i).symm r (Pi.single j 1))
        ((B.trivialization i).symm r (Pi.single k 1))) p :=
    (g.smooth i j k p hpB).1
  change ContinuousAt (fun z : M × Euclidean n => Real.sqrt
    (∑ j : Fin n, ∑ k : Fin n, z.2 j * (z.2 k *
      g.form z.1 ((B.trivialization i).symm z.1 (Pi.single j 1))
        ((B.trivialization i).symm z.1 (Pi.single k 1))))) (p, v)
  apply Real.continuous_sqrt.continuousAt.comp
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  exact ((continuous_apply j).continuousAt.comp continuousAt_snd).mul
    (((continuous_apply k).continuousAt.comp continuousAt_snd).mul
      ((hgram j k).comp' (x := (p, v)) continuousAt_fst))

/-- A uniform small-vector estimate on a neighborhood of any base point. -/
theorem coordinateNorm_small (g : RiemannianMetric S)
    (e : ModelChart n kind M) (he : e ∈ S.smoothStructure.val)
    (p : M) (hp : p ∈ e.source) (η : ℝ) (hη : 0 < η) :
    ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ ∃ δ : ℝ, 0 < δ ∧
      ∀ r ∈ V, ∀ v : Euclidean n, ‖v‖ < δ → coordinateNorm g e he r v < η := by
  have hsmall : {z : M × Euclidean n | coordinateNorm g e he z.1 z.2 < η}
      ∈ 𝓝 (p, 0) :=
    (coordinateNorm_continuousAt g e he p hp 0).eventually
      (gt_mem_nhds (by simpa using hη))
  obtain ⟨A, hA, D, hD, hAD⟩ := mem_nhds_prod_iff.mp hsmall
  obtain ⟨V, hVA, hV, hpV⟩ := mem_nhds_iff.mp hA
  obtain ⟨δ, hδ, hδD⟩ := Metric.mem_nhds_iff.mp hD
  refine ⟨V, hV, hpV, δ, hδ, ?_⟩
  intro r hr v hv
  exact hAD (show (r, v) ∈ A ×ˢ D from
    ⟨hVA hr, hδD (by simpa [Metric.mem_ball, dist_zero_right] using hv)⟩)

/-- Straight segments stay in a sufficiently small convex coordinate ball
intersected with the model, so this also covers charts at the boundary. -/
theorem local_short_curves :
    P202Specs.Geometry.LocalShortCurves.local_short_curvesType.{u} := by
  intro n kind M _ S g p ε hε
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  obtain ⟨V, hV, hpV, δ, hδ, hsmall⟩ :=
    coordinateNorm_small g e he p hp (ε / 2) (half_pos hε)
  have hW : IsOpen (e.target ∩ e.symm ⁻¹' V) := e.symm.isOpen_inter_preimage hV
  have hpW : e p ∈ e.target ∩ e.symm ⁻¹' V := by
    exact ⟨e.map_source hp, by simpa only [mem_preimage, e.left_inv hp] using hpV⟩
  obtain ⟨r, hr, hrW⟩ := Metric.isOpen_iff.mp hW (e p) hpW
  let ρ := min r δ
  have hρ : 0 < ρ := lt_min hr hδ
  refine ⟨e.source ∩ e ⁻¹' Metric.ball (e p) ρ,
    e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hp, by simpa using hρ⟩, ?_⟩
  intro q hq
  let x : Euclidean n := (e p).val
  let y : Euclidean n := (e q).val
  have hy : y ∈ Metric.ball x r :=
    lt_of_lt_of_le hq.2 (min_le_left r δ)
  have hv : ‖y - x‖ < δ := by
    have h := lt_of_lt_of_le hq.2 (min_le_right r δ)
    simpa only [Metric.mem_ball, Subtype.dist_eq, dist_eq_norm] using h
  let σ : Icc (0 : ℝ) 1 → ModelSpace n kind := fun t =>
    ⟨AffineMap.lineMap x y t.val,
      (SmoothManifolds.convex_modelSet n kind).lineMap_mem
        (e p).property (e q).property t.property⟩
  have hσ : Continuous σ := by
    apply Continuous.subtype_mk
    exact (AffineMap.contDiff_lineMap (n := 1) x y).continuous.comp continuous_subtype_val
  have hσW (t : Icc (0 : ℝ) 1) : σ t ∈ e.target ∩ e.symm ⁻¹' V := by
    apply hrW
    change AffineMap.lineMap x y t.val ∈ Metric.ball x r
    exact (convex_ball x r).lineMap_mem (by simpa using hr) hy t.property
  let c : Icc (0 : ℝ) 1 → M := e.symm ∘ σ
  have hc : Continuous c := e.symm.continuousOn.comp_continuous hσ (fun t => (hσW t).1)
  have hsource (t : Icc (0 : ℝ) 1) : c t ∈ e.source := e.map_target (hσW t).1
  have hcoord (t : Icc (0 : ℝ) 1) :
      (e (c t)).val = AffineMap.lineMap x y t.val := by
    exact congrArg Subtype.val (e.right_inv (hσW t).1)
  let f : ℝ → M := IccExtend (by norm_num : (0 : ℝ) ≤ 1) c
  have hf (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t = c ⟨t, ht⟩ :=
    IccExtend_of_mem _ _ ht
  have hfcoord (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
      (e (f t)).val = AffineMap.lineMap x y t := by rw [hf t ht]; exact hcoord _
  have hfsource (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) : f t ∈ e.source := by
    rw [hf t ht]; exact hsource _
  have hregular : CoordinateC1On S f (Icc 0 1) := by
    intro t ht
    refine ⟨e, he, hfsource t ht, AffineMap.lineMap x y,
      (AffineMap.contDiff_lineMap x y).contDiffAt, (hfcoord t ht).symm, ?_⟩
    filter_upwards [self_mem_nhdsWithin] with s hs
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
  have hd0 : d 0 = p := by
    change f 0 = p
    rw [hf 0 (by norm_num)]
    change e.symm (σ ⟨0, by norm_num⟩) = p
    have hσ0 : σ ⟨0, by norm_num⟩ = e p := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_zero x y
    rw [hσ0, e.left_inv hp]
  have hd1 : d 1 = q := by
    change f 1 = q
    rw [hf 1 (by norm_num)]
    change e.symm (σ ⟨1, by norm_num⟩) = q
    have hσ1 : σ ⟨1, by norm_num⟩ = e q := by
      apply Subtype.ext
      exact AffineMap.lineMap_apply_one x y
    rw [hσ1, e.left_inv hq.1]
  refine ⟨0, 1, d, hd0, hd1, ?_⟩
  have hspeed (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : speed g d t ≤ ε / 2 := by
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioo_subset_Icc_self ht
    have hJ : Icc (0 : ℝ) 1 ∈ 𝓝 t := Icc_mem_nhds ht.1 ht.2
    have heq : (fun s => (e (f s)).val) =ᶠ[𝓝[Icc (0 : ℝ) 1] t]
        AffineMap.lineMap x y := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact hfcoord s hs
    have hvel := PiecewiseCurves.velocity_eq_coordinateExtension
      (continuous_IccExtend_iff.mpr hc |>.continuousAt) hJ e he (hfsource t ht')
      (AffineMap.contDiff_lineMap x y).contDiffAt heq
    have hcoords : (tangentStructure S).fiberCoordinates.equiv e he (f t)
        (hfsource t ht') (velocity S f t) = y - x := by
      rw [hvel, LinearEquiv.apply_symm_apply, AffineMap.hasDerivAt_lineMap.deriv]
    have hftV : f t ∈ V := by
      rw [hf t ht']; exact (hσW ⟨t, ht'⟩).2
    have hbound := hsmall (f t) hftV (y - x) hv
    rw [← hcoords, coordinateNorm_eq] at hbound
    exact hbound.le
  have hlen : length g d ≤ ε / 2 := by
    have H := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ) ≤ 1)
      (MetricFoundation.speed_integrable g d)
      (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ε / 2)
        MeasureTheory.volume 0 1) hspeed
    simpa only [length, intervalIntegral.integral_const, sub_zero, one_smul] using H
  exact hlen.trans_lt (half_lt_self hε)

end P202.Geometry.LocalShortCurves
