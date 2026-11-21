import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.LocalCurveTrapping
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricFoundation
import Mathlib.MeasureTheory.Integral.DivergenceTheorem
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
namespace P202.Geometry.LocalCurveTrapping
open SmoothManifolds (ModelKind)
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleOperationsData P202.MetricData P202.CurveData
open Set Filter MeasureTheory
open scoped Topology
universe u

variable {n : ℕ} {kind : ModelKind} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n kind M}

/-- The norm in an actual tangent chart, expressed by its Gram coefficients.
This expression is defined globally, but only used on the chart source. -/
noncomputable def chartNorm (g : RiemannianMetric S)
    (i : TangentIndex S) (q : M) (w : Euclidean n) : ℝ :=
  Real.sqrt (∑ j : Fin n, ∑ k : Fin n, w j * (w k *
    g.form q (((tangentRealization S).space.bundle.trivialization i).symm q
      (Pi.single j 1))
      (((tangentRealization S).space.bundle.trivialization i).symm q
        (Pi.single k 1))))

theorem chartNorm_coordinates (g : RiemannianMetric S) (i : TangentIndex S)
    (q : M) (hq : q ∈ i.val.source) (v : TangentSpace S q) :
    chartNorm g i q ((tangentStructure S).fiberCoordinates.equiv
      i.val i.property q hq v) = tangentNorm g q v := by
  let B := (tangentRealization S).space.bundle
  have hqB : q ∈ B.baseSet i := by
    rw [(tangentRealization S).baseSet]; exact hq
  have h := SmoothMetrics.bilinear_coordinates (B.fiberCoordinates i q hqB)
    (g.form q) v v
  dsimp only [B] at h
  simp only [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
    (tangentRealization S).coordinates i q hq] at h
  exact congrArg Real.sqrt h.symm

theorem chartNorm_continuousAt (g : RiemannianMetric S) (i : TangentIndex S)
    (q : M) (hq : q ∈ i.val.source) (w : Euclidean n) :
    ContinuousAt (fun z : M × Euclidean n => chartNorm g i z.1 z.2) (q, w) := by
  let B := (tangentRealization S).space.bundle
  have hqB : q ∈ B.baseSet i := by
    rw [(tangentRealization S).baseSet]; exact hq
  apply Real.continuous_sqrt.continuousAt.comp
  apply tendsto_finsetSum
  intro j _
  apply tendsto_finsetSum
  intro k _
  have hg : ContinuousAt (fun q =>
      g.form q ((B.trivialization i).symm q (Pi.single j 1))
        ((B.trivialization i).symm q (Pi.single k 1))) q :=
    (g.smooth i j k q hqB).1
  have hg' := hg.comp (continuousAt_fst :
    ContinuousAt (Prod.fst : M × Euclidean n → M) (q, w))
  exact ((continuous_apply j).continuousAt.comp continuousAt_snd).mul
    (((continuous_apply k).continuousAt.comp continuousAt_snd).mul hg')

theorem chartNorm_smul (g : RiemannianMetric S) (i : TangentIndex S)
    (q : M) (hq : q ∈ i.val.source) (r : ℝ) (w : Euclidean n) :
    chartNorm g i q (r • w) = |r| * chartNorm g i q w := by
  let E := (tangentStructure S).fiberCoordinates.equiv i.val i.property q hq
  have h (w : Euclidean n) : chartNorm g i q w = tangentNorm g q (E.symm w) := by
    have hh := chartNorm_coordinates g i q hq (E.symm w)
    change chartNorm g i q (E (E.symm w)) = _ at hh
    simpa only [LinearEquiv.apply_symm_apply] using hh
  rw [h, map_smul, SmoothMetrics.tangentNorm_smul, h]

theorem chartNorm_pos (g : RiemannianMetric S) (i : TangentIndex S)
    (q : M) (hq : q ∈ i.val.source) {w : Euclidean n} (hw : w ≠ 0) :
    0 < chartNorm g i q w := by
  let E := (tangentStructure S).fiberCoordinates.equiv i.val i.property q hq
  have hv : E.symm w ≠ 0 := fun h => hw (by simpa using congrArg E h)
  have h := chartNorm_coordinates g i q hq (E.symm w)
  change chartNorm g i q (E (E.symm w)) = _ at h
  simp only [LinearEquiv.apply_symm_apply] at h
  rw [h]
  exact lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g q _) fun he =>
    hv ((SmoothMetrics.tangentNorm_eq_zero_iff g q _).mp he.symm)

/-- Positive definiteness and continuity give a uniform lower norm comparison
on a neighborhood of a point. Compactness is used only on the coordinate unit
sphere, so no compactness of the manifold is required. -/
theorem local_coordinate_bound (g : RiemannianMetric S) (i : TangentIndex S)
    (p : M) (hp : p ∈ i.val.source) :
    ∃ C : ℝ, 0 < C ∧ ∃ V : Set M, IsOpen V ∧ p ∈ V ∧ V ⊆ i.val.source ∧
      ∀ (q : M) (hq : q ∈ i.val.source) (v : TangentSpace S q),
        q ∈ V → ‖(tangentStructure S).fiberCoordinates.equiv
          i.val i.property q hq v‖ ≤ C * tangentNorm g q v := by
  classical
  let K : Set (Euclidean n) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere _ _
  obtain ⟨δ, hδ, hlocal⟩ : ∃ δ : ℝ, 0 < δ ∧
      ∀ᶠ q in 𝓝 p, ∀ w ∈ K, δ < chartNorm g i q w := by
    by_cases hne : K.Nonempty
    · have hc : ContinuousOn (chartNorm g i p) K := by
        intro w hw
        exact ((chartNorm_continuousAt g i p hp w).comp
          (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
      obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne hc
      have hpos : 0 < chartNorm g i p w := by
        apply chartNorm_pos g i p hp
        have hn : ‖w‖ = 1 := by simpa [K, Metric.mem_sphere, dist_zero_right] using hw
        intro h; simp [h] at hn
      refine ⟨chartNorm g i p w / 2, half_pos hpos, ?_⟩
      apply hK.eventually_forall_of_forall_eventually
      intro z hz
      apply (chartNorm_continuousAt g i p hp z).eventually_const_lt
      exact lt_of_lt_of_le (half_lt_self hpos) (hmin hz)
    · exact ⟨1, zero_lt_one, .of_forall (fun _ w hw => (hne ⟨w, hw⟩).elim)⟩
  obtain ⟨V, hVsub, hVopen, hpV⟩ :=
    mem_nhds_iff.mp (hlocal.and (i.val.open_source.mem_nhds hp))
  have hVs : V ⊆ i.val.source := fun q hq => (hVsub hq).2
  refine ⟨δ⁻¹, inv_pos.mpr hδ, V, hVopen, hpV, hVs, ?_⟩
  intro q hqs v hq
  let E := (tangentStructure S).fiberCoordinates.equiv i.val i.property q (hVs hq)
  let w := E v
  change ‖w‖ ≤ δ⁻¹ * tangentNorm g q v
  by_cases hw : w = 0
  · rw [hw, norm_zero]
    exact mul_nonneg (inv_nonneg.mpr hδ.le) (SmoothMetrics.tangentNorm_nonneg g q v)
  have hnorm : 0 < ‖w‖ := norm_pos_iff.mpr hw
  have hunit : ‖w‖⁻¹ • w ∈ K := by
    simp [K, norm_smul, ne_of_gt hnorm]
  have hb := (hVsub hq).1 (‖w‖⁻¹ • w) hunit
  rw [chartNorm_smul g i q (hVs hq), abs_of_pos (inv_pos.mpr hnorm),
    chartNorm_coordinates g i q (hVs hq) v] at hb
  have hb' : δ * ‖w‖ < tangentNorm g q v :=
    (lt_div_iff₀ hnorm).mp (by simpa [div_eq_mul_inv, mul_comm] using hb)
  rw [← div_eq_inv_mul]
  exact (le_div_iff₀ hδ).mpr (by linarith)

/-- Displacement of a prefix which stays in a controlled chart is bounded by
the length of the entire curve. The finite corners are removed only in the
derivative assertions, using the countable-exception FTC. -/
theorem coordinate_displacement_le_length (g : RiemannianMetric S)
    (i : TangentIndex S) {C : ℝ} (hC : 0 ≤ C) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {r : ℝ} (har : a ≤ r) (hrb : r ≤ b)
    (hsource : ∀ t ∈ Icc a r, c t ∈ i.val.source)
    (hbound : ∀ (t : ℝ) (ht : t ∈ Icc a r) (v : TangentSpace S (c t)),
      ‖(tangentStructure S).fiberCoordinates.equiv i.val i.property
        (c t) (hsource t ht) v‖ ≤ C * tangentNorm g (c t) v) :
    ‖(i.val (c r)).val - (i.val (c a)).val‖ ≤ C * length g c := by
  classical
  let f : ℝ → Euclidean n := fun t => (i.val (c t)).val
  have hsub : Icc a r ⊆ Icc a b := Icc_subset_Icc_right hrb
  have hfc : ContinuousOn f (Icc a r) :=
    (continuous_subtype_val.comp_continuousOn i.val.continuousOn).comp
      (c.continuousOn.mono hsub) hsource
  have hd (t : ℝ) (ht : t ∈ Icc a r) (hcorner : t ∉ breakpoints c) :
      HasDerivAt f ((tangentStructure S).fiberCoordinates.equiv
        i.val i.property (c t) (hsource t ht) (velocity S c t)) t :=
    PiecewiseCurves.hasVelocityAt_coordinates
      (PiecewiseCurves.hasVelocityAt_off_breakpoints c (hsub ht) hcorner)
      i.val i.property (hsource t ht)
  have hB : IntervalIntegrable (fun t => C * speed g c t) volume a r :=
    ((PiecewiseCurves.speed_integrable g c).const_mul C).mono_set (by
      rw [uIcc_of_le har, uIcc_of_le c.ordered]; exact hsub)
  have hder : ∀ᵐ t ∂volume, t ∈ Ioc a r → ‖deriv f t‖ ≤ C * speed g c t := by
    filter_upwards [(breakpoints c).finite_toSet.countable.ae_notMem volume] with t ht hI
    rw [(hd t (Ioc_subset_Icc_self hI) ht).deriv]
    exact hbound t (Ioc_subset_Icc_self hI) (velocity S c t)
  have hfi : IntervalIntegrable (deriv f) volume a r := by
    apply hB.mono_fun' (aestronglyMeasurable_deriv f _)
    rw [uIoc_of_le har, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
    exact hder
  have hFTC : (∫ t in a..r, deriv f t) = f r - f a := by
    apply integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) har
      (breakpoints c).finite_toSet.countable hfc
    · intro t ht
      exact (hd t (Ioo_subset_Icc_self ht.1) ht.2).differentiableAt.hasDerivAt
    · exact hfi
  calc
    ‖(i.val (c r)).val - (i.val (c a)).val‖ = ‖∫ t in a..r, deriv f t‖ :=
      congrArg norm hFTC.symm
    _ ≤ ∫ t in a..r, C * speed g c t :=
      intervalIntegral.norm_integral_le_of_norm_le har hder hB
    _ = C * ∫ t in a..r, speed g c t := intervalIntegral.integral_const_mul _ _
    _ ≤ C * length g c := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact intervalIntegral.integral_mono_interval le_rfl har hrb
        (.of_forall (fun t => SmoothMetrics.tangentNorm_nonneg g (c t) _))
        (PiecewiseCurves.speed_integrable g c)

/-- Short curves cannot leave any prescribed open neighborhood. The argument
uses continuous induction on a closed neighborhood: a controlled prefix ends
strictly inside it and therefore extends a little farther. -/
theorem local_curve_trapping :
    P202Specs.Geometry.LocalCurveTrapping.local_curve_trappingType.{u} := by
  intro n kind M _ S g p U hU hpU
  let := SmoothManifolds.TopologicalManifold.regularSpace S.topologicalManifold
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let i : TangentIndex S := ⟨e, he⟩
  obtain ⟨C, hC, V, hVopen, hpV, hVs, hbound⟩ := local_coordinate_bound g i p hp
  obtain ⟨K, hKmem, hKclosed, hKsub⟩ :=
    exists_mem_nhds_isClosed_subset (Filter.inter_mem (hU.mem_nhds hpU) (hVopen.mem_nhds hpV))
  have hKU : K ⊆ U := fun q hq => (hKsub hq).1
  have hKV : K ⊆ V := fun q hq => (hKsub hq).2
  obtain ⟨W, hWK, hWopen, hpW⟩ := mem_nhds_iff.mp hKmem
  have hpre : e.symm ⁻¹' W ∈ 𝓝 (e p) :=
    (e.tendsto_symm hp) (hWopen.mem_nhds hpW)
  obtain ⟨r, hr, hrW⟩ := Metric.mem_nhds_iff.mp hpre
  refine ⟨r / C, div_pos hr hC, ?_⟩
  intro a b c hc hL
  let A : Set ℝ := c ⁻¹' K
  have hAclosed : IsClosed (A ∩ Icc a b) := by
    simpa [A, inter_comm] using c.continuousOn.preimage_isClosed_of_isClosed
      isClosed_Icc hKclosed
  have haA : a ∈ A := by
    change c a ∈ K
    rw [hc]
    exact mem_of_mem_nhds hKmem
  have hstay : Icc a b ⊆ A := by
    apply hAclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset haA
    intro t ht hprefix
    have hsource : ∀ s ∈ Icc a t, c s ∈ e.source :=
      fun s hs => hVs (hKV (hprefix hs))
    have hdisp := coordinate_displacement_le_length g i hC.le c ht.1 ht.2.le
      hsource (fun s hs v => hbound (c s) (hsource s hs) v (hKV (hprefix hs)))
    have hCr : C * length g c < r := by
      simpa only [mul_comm] using (lt_div_iff₀ hC).mp hL
    have hball : e (c t) ∈ Metric.ball (e p) r := by
      change ‖(e (c t)).val - (e p).val‖ < r
      simpa only [hc] using hdisp.trans_lt hCr
    have hctW : c t ∈ W := by
      have h := hrW hball
      rwa [mem_preimage, e.left_inv (hsource t ⟨ht.1, le_rfl⟩)] at h
    have hct : ContinuousWithinAt c (Ioi t) t :=
      (c.continuousOn t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT_of_mem ht)
    exact mem_of_superset (hct.preimage_mem_nhdsWithin (hWopen.mem_nhds hctW))
      (fun s hs => hWK hs)
  exact hKU (hstay ⟨c.ordered, le_rfl⟩)

end P202.Geometry.LocalCurveTrapping
