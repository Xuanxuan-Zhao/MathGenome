import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MinimizingIndexForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SecondVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialNormalCoordinates
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! Energy minimality and nonnegativity of the index of a minimizing affine
geodesic, paper.tex 4153–4162 and 4710–4726. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.MinimizingIndexForm
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.BundleData
  SmoothManifolds.TangentBundleData SmoothManifolds.MapData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.SecondVariationData
  P202.CurvatureData P202.MinimizingIndexData P202.GeodesicData P202.ExponentialData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The full quantitative estimate for every compact-interval competitor. -/
theorem length_sq_le_energy :
    P202Specs.Geometry.MinimizingIndexForm.length_sq_le_energyType.{u} := by
  intro n M _ S g a b σ
  exact FirstVariation.length_sq_le_energy g σ

/-- Constancy on the closed segment uses one-sided covariant derivatives at
both endpoints. No extension of the geodesic beyond its interval is assumed. -/
theorem segment_speed_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsAffineGeodesicSegment C γ a b) :
    ∀ t ∈ Icc a b,
      tangentNorm g (γ t) (segmentTangent S γ a b t) =
        tangentNorm g (γ a) (segmentTangent S γ a b a) := by
  let f (t : ℝ) := pairing g (γ t) (segmentTangent S γ a b t)
    (segmentTangent S γ a b t)
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt f 0 (Icc a b) t := by
    have h := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2
      ht (uniqueDiffOn_Icc hab t ht) (hγ.2 t ht) (hγ.2 t ht)
    simpa only [f, pairing, map_zero, LinearMap.zero_apply, add_zero] using h
  have hf : DifferentiableOn ℝ f (Icc a b) := fun t ht => (hd t ht).differentiableWithinAt
  have heq := constant_of_derivWithin_zero hf
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).derivWithin (uniqueDiffOn_Icc hab t ⟨ht.1, ht.2.le⟩))
  intro t ht
  exact congrArg Real.sqrt (heq t ht)

/-- At almost every parameter, the canonical speed used by energy agrees
with the constant one-sided speed. Endpoint values have measure zero. -/
theorem geodesic_speed_ae_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsAffineGeodesicSegment C γ a b) :
    ∀ᵐ t ∂volume.restrict (Ioc a b), speed g γ t =
      tangentNorm g (γ a) (segmentTangent S γ a b a) := by
  rw [← MeasureTheory.restrict_Ioo_eq_restrict_Ioc]
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
  have heq := segment_speed_constant g C hC hab hγ t (Ioo_subset_Icc_self ht)
  have hv := FirstVariation.segmentVelocity_eq_velocity hγ.1 (by norm_num) ht
  change segmentTangent S γ a b t = velocity S γ t at hv
  simpa only [speed, hv] using heq

theorem geodesic_energy_equality :
    P202Specs.Geometry.MinimizingIndexForm.geodesic_energy_equalityType.{u} := by
  intro n M _ S g C hC a b γ hab hγ
  exact FirstVariation.constant_speed_equality g γ _
    (geodesic_speed_ae_constant g C hC hab hγ)

theorem minimizes_energy :
    P202Specs.Geometry.MinimizingIndexForm.minimizes_energyType.{u} := by
  intro n M _ S g C hC a b γ hab hγ hmin σ ha hb
  have hlength := hmin σ ha hb
  have hnonneg := LengthDistance.length_nonneg g γ
  have hsq : length g γ ^ 2 ≤ length g σ ^ 2 :=
    pow_le_pow_left₀ hnonneg hlength 2
  have heq := geodesic_energy_equality g C hC γ hab hγ
  have hine := length_sq_le_energy g σ
  nlinarith [show 0 < 2 * (b - a) by linarith]

/-- A second derivative at a local minimum is nonnegative. Continuity of f
at zero is essential here: the default value of `deriv` at a discontinuity
must not be mistaken for a genuine first derivative. -/
theorem second_derivative_nonneg {f : ℝ → ℝ} {d : ℝ}
    (hmin : IsLocalMin f 0) (hc : ContinuousAt f 0)
    (hd : HasDerivAt (deriv f) d 0) : 0 ≤ d := by
  by_contra hn
  have hdneg : d < 0 := lt_of_not_ge hn
  have hzero : deriv f 0 = 0 := hmin.deriv_eq_zero
  have hslope := hd.tendsto_slope_zero_right.eventually (eventually_lt_nhds hdneg)
  have hnegative : ∀ᶠ x in 𝓝[>] (0 : ℝ), deriv f x < 0 := by
    filter_upwards [hslope, self_mem_nhdsWithin] with x hx (hxp : 0 < x)
    have hprod : x⁻¹ * deriv f x < 0 := by
      simpa only [zero_add, hzero, sub_zero, smul_eq_mul] using hx
    have hpos : 0 < x⁻¹ := inv_pos.mpr hxp
    nlinarith
  have hm : ∀ᶠ x in 𝓝 (0 : ℝ), f 0 ≤ f x := hmin
  obtain ⟨r, hr, hall⟩ := (nhdsGT_basis (0 : ℝ)).eventually_iff.mp
    (hnegative.and (hm.filter_mono nhdsWithin_le_nhds))
  have hx : 0 < r / 2 := by linarith
  have hxr : r / 2 < r := by linarith
  have hcont : ContinuousOn f (Icc 0 (r/2)) := by
    intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact hc.continuousWithinAt
    · exact (differentiableAt_of_deriv_ne_zero
        (hall ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2.trans_lt hxr⟩).1.ne).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ f (Ioo 0 (r/2)) := by
    intro t ht
    exact (differentiableAt_of_deriv_ne_zero
      (hall ⟨ht.1, ht.2.trans hxr⟩).1.ne).differentiableWithinAt
  obtain ⟨c, hcmem, hcderiv⟩ := exists_deriv_eq_slope f hx hcont hdiff
  have hcneg := (hall ⟨hcmem.1, hcmem.2.trans hxr⟩).1
  have hfmin := (hall ⟨hx, hxr⟩).2
  have hnonneg : 0 ≤ (f (r/2) - f 0) / (r/2 - 0) :=
    div_nonneg (sub_nonneg.mpr hfmin) (by linarith)
  linarith


/-- Each slice of a continuous variation smooth on finitely many strips is
one of the original compact-interval piecewise C¹ competitors. -/
def piecewiseVariationSlice {F : ℝ × ℝ → M} {ε : ℝ}
    {k : ℕ} {node : Fin (k+2) → ℝ}
    (hF : PiecewiseSmoothVariationOn S F ε node) (hnode : Monotone node)
    {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    PiecewiseC1Curve S (node 0) (node (Fin.last (k+1))) where
  ordered := hnode (Fin.zero_le _)
  toFun := fun t => F (s,t)
  continuousOn := hF.1.comp (continuousOn_const.prodMk continuousOn_id)
    (fun _ ht => ⟨hs, ht⟩)
  pieces := k+1
  node := node
  monotone_node := hnode
  first_node := rfl
  last_node := rfl
  regular := fun i => FirstVariation.variation_coordinateC1On_slice (hF.2 i) hs

/-- Length minimality gives an actual local minimum of the scalar varied
energy for every fixed-endpoint finite-piece variation. -/
theorem variedEnergy_isLocalMin (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hF : PiecewiseSmoothVariationOn S F ε node)
    (γ : PiecewiseC1Curve S (node 0) (node (Fin.last (k+1))))
    (hγ : IsAffineGeodesicSegment C γ (node 0) (node (Fin.last (k+1))))
    (hmin : IsLengthMinimizing g γ)
    (hcenter : (fun t => F (0,t)) = γ)
    (hfixed : FixedEndpoints F ε (node 0) (node (Fin.last (k+1)))) :
    IsLocalMin (variedEnergy g F (node 0) (node (Fin.last (k+1)))) 0 := by
  have hab : node 0 < node (Fin.last (k+1)) := hnode (by change (0 : ℕ) < k+1; omega)
  have henergy : variedEnergy g F (node 0) (node (Fin.last (k+1))) 0 =
      energy g γ := by
    change (1/2 : ℝ) * (∫ t in node 0..node (Fin.last (k+1)),
      speed g (fun r => F (0,r)) t ^ 2) = _
    rw [hcenter]
    rfl
  have hnhds : Ioo (-ε) ε ∈ 𝓝 (0 : ℝ) := Ioo_mem_nhds (by linarith) hε
  filter_upwards [hnhds] with s hs
  change variedEnergy g F (node 0) (node (Fin.last (k+1))) 0 ≤ _
  rw [henergy]
  exact minimizes_energy g C hC γ hab hγ hmin
    (piecewiseVariationSlice hF hnode.monotone hs)
    ((hfixed s hs).1.trans (congrFun hcenter _))
    ((hfixed s hs).2.trans (congrFun hcenter _))

/-- Nonnegativity for the field of every fixed-endpoint variation. This
already includes all finite break parameters, without a conjugacy condition. -/
theorem variation_indexForm_nonneg (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hF : PiecewiseSmoothVariationOn S F ε node)
    (γ : PiecewiseC1Curve S (node 0) (node (Fin.last (k+1))))
    (hγ : IsAffineGeodesicSegment C γ (node 0) (node (Fin.last (k+1))))
    (hmin : IsLengthMinimizing g γ)
    (hcenter : (fun t => F (0,t)) = γ)
    (hfixed : FixedEndpoints F ε (node 0) (node (Fin.last (k+1)))) :
    0 ≤ indexForm g C R (fun t => F (0,t)) (node 0) (node (Fin.last (k+1)))
      (variationField S F) (variationField S F) := by
  have hgeo : IsAffineGeodesicSegment C (fun t => F (0,t))
      (node 0) (node (Fin.last (k+1))) := by
    rw [hcenter]
    exact hγ
  have hsecond := SecondVariation.piecewise_second_variation_energy
    g C hC R hR F ε hε node hnode hF hgeo
  have hboundary := SecondVariation.fixed_endpoint_boundary g C F ε
    (node 0) (node (Fin.last (k+1))) hε hfixed
  rw [hboundary, add_zero] at hsecond
  have hcontinuous := (FirstVariation.piecewise_energy
    g C hC F ε hε node hnode hF.2).continuousAt
  exact second_derivative_nonneg
    (variedEnergy_isLocalMin g C hC hε node hnode hF γ hγ hmin hcenter hfixed)
    hcontinuous hsecond

/-- Changing a field only outside the parameter set cannot change its
chosen covariant derivative on a set with unique differentiation. -/
theorem covariantDerivativeWithin_congr_field
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (heq : ∀ r ∈ J, W r = V r) :
    covariantDerivativeWithin C γ W J t = covariantDerivativeWithin C γ V J t := by
  classical
  by_cases hex : ∃ D, HasCovariantDerivativeWithinAt C γ V J t D
  · exact CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ
      (SecondVariation.hasCovariantDerivativeWithinAt_congr_field C ht
        (CurveCovariantDerivative.covariantDerivativeWithin_spec C hex) heq)
  · have hnW : ¬ ∃ D, HasCovariantDerivativeWithinAt C γ W J t D := by
      rintro ⟨D,hD⟩
      exact hex ⟨D, SecondVariation.hasCovariantDerivativeWithinAt_congr_field C ht hD
        (fun r hr => (heq r hr).symm)⟩
    simp only [covariantDerivativeWithin, dite_eq_right hex, dite_eq_right hnW]

/-- Index values depend only on the fields on the compact segment, even
though all fields are represented by total functions. -/
theorem indexForm_congr_field (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (heq : ∀ t ∈ Icc a b, W t = V t) :
    indexForm g C R γ a b W W = indexForm g C R γ a b V V := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab.le]
  intro t ht
  have hd := covariantDerivativeWithin_congr_field C ht (uniqueDiffOn_Icc hab t ht) heq
  simp only [indexIntegrand, hd, heq t ht]

/-- Transport along equality of the central curves preserves the index. -/
theorem indexForm_transport (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ η : ℝ → M} (h : γ = η) (a b : ℝ)
    (V : (t : ℝ) → TangentSpace S (η t)) :
    indexForm g C R γ a b (h.symm ▸ V) (h.symm ▸ V) =
      indexForm g C R η a b V V := by
  subst η
  rfl

/-- Assemble the index theorem from the realization principle and the
proved nonnegativity for fixed-endpoint variations. -/
theorem indexForm_nonneg_of_realizes_field
    (hrealize : P202Specs.Geometry.MinimizingIndexForm.realizes_fieldType.{u}) :
    P202Specs.Geometry.MinimizingIndexForm.indexForm_nonnegType.{u} := by
  intro n M _ S g C hC R hR a b γ hab hγ hmin k node hnode ha hb V hV hVa hVb
  obtain ⟨ε,F,hcenter,hε,hF,hfixed,hfield⟩ :=
    hrealize g C hC γ hab hγ node hnode ha hb V hV hVa hVb
  subst a
  subst b
  have hnonneg := variation_indexForm_nonneg g C hC R hR hε node hnode hF
    γ hγ hmin hcenter hfixed
  rw [indexForm_congr_field g C R (hnode (by change (0 : ℕ) < k+1; omega)) hfield] at hnonneg
  rwa [indexForm_transport g C R hcenter] at hnonneg

def tangentScale (z : ℝ × Phase S) : Phase S := ⟨z.2.1, z.1 • z.2.2⟩

theorem tangentScale_continuous : Continuous (tangentScale (S := S)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  let B := tangentStructure S
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 z.2.1
  let c := B.chart e he
  have hw : z.2 ∈ c.source := by
    simpa only [c, B.chart_source, projection, mem_preimage] using hp
  have hsw : tangentScale z ∈ c.source := by
    simpa only [c, B.chart_source, projection, mem_preimage, tangentScale] using hp
  let L := B.productCoordinates.linearEquiv
  let f : ℝ × Phase S → Euclidean (n+n) := fun w =>
    L ((L.symm (c w.2).val).1, w.1 • (L.symm (c w.2).val).2)
  have hcoord : ContinuousAt (fun w : ℝ × Phase S => (c w.2).val) z :=
    continuous_subtype_val.continuousAt.comp
      ((c.continuousAt hw).comp continuous_snd.continuousAt)
  have hf : ContinuousAt f z := by
    exact L.continuous.continuousAt.comp
      (((L.symm.continuous.continuousAt.comp hcoord).fst).prodMk
        (continuous_fst.continuousAt.smul (L.symm.continuous.continuousAt.comp hcoord).snd))
  have hnear : ∀ᶠ w : ℝ × Phase S in 𝓝 z, w.2 ∈ c.source :=
    continuous_snd.continuousAt.eventually (c.open_source.mem_nhds hw)
  have heq : (fun w => (c (tangentScale w)).val) =ᶠ[𝓝 z] f := by
    filter_upwards [hnear] with w hw
    have hpw : w.2.1 ∈ e.source := by
      simpa only [c, B.chart_source, projection, mem_preimage] using hw
    change (B.chart e he (tangentScale w)).val =
      B.productCoordinates.linearEquiv
        ((B.productCoordinates.linearEquiv.symm ((B.chart e he) w.2).val).1,
          w.1 • (B.productCoordinates.linearEquiv.symm ((B.chart e he) w.2).val).2)
    rw [B.chart_apply e he (tangentScale w) hpw, B.chart_apply e he w.2 hpw]
    simp only [tangentScale, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  have hactual : ContinuousAt (fun w => (c (tangentScale w)).val) z :=
    hf.congr heq.symm
  have hmodel : ContinuousAt (fun w => c (tangentScale w)) z :=
    tendsto_subtype_rng.mpr hactual
  have hback := (c.continuousAt_symm (c.map_source hsw)).comp (f := fun w : ℝ × Phase S => c (tangentScale w)) hmodel
  apply hback.congr_of_eventuallyEq
  filter_upwards [hnear] with w hw
  exact (c.left_inv (by
    simpa only [c, B.chart_source, projection, mem_preimage, tangentScale] using hw)).symm



/-- The chart law for scalar multiplication in the original tangent fibers. -/
theorem tangentScale_chart (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (w : Phase S) (hw : w.1 ∈ e.source) (s : ℝ) :
    let B := tangentStructure S
    ((B.chart e he) (tangentScale (s,w))).val = B.productCoordinates.linearEquiv
      ((B.productCoordinates.linearEquiv.symm ((B.chart e he) w).val).1,
        s • (B.productCoordinates.linearEquiv.symm ((B.chart e he) w).val).2) := by
  dsimp only
  rw [(tangentStructure S).chart_apply e he (tangentScale (s,w)) hw,
    (tangentStructure S).chart_apply e he w hw]
  simp only [tangentScale, map_smul, ContinuousLinearEquiv.symm_apply_apply]

def scaledField (γ : ℝ → M) (V : (t : ℝ) → TangentSpace S (γ t))
    (z : ℝ × ℝ) : Phase S := tangentScale (z.1, ⟨γ z.2, V z.2⟩)

theorem scaledField_continuousOn {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ}
    (hV : ContinuousOn (fun t => (⟨γ t,V t⟩ : Phase S)) J) :
    ContinuousOn (scaledField γ V) (univ ×ˢ J) :=
  tangentScale_continuous.comp_continuousOn
    (continuousOn_fst.prodMk (hV.comp continuousOn_snd (fun _ hw => hw.2)))

theorem scaledField_smoothVariationOn {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b ε : ℝ}
    (hVc : ContinuousOn (fun t => (⟨γ t,V t⟩ : Phase S)) (Icc a b))
    (hV : SmoothFieldOn γ V (Icc a b)) :
    SmoothVariationOn (phaseManifold S) (scaledField γ V) ε a b := by
  let B := tangentStructure S
  let D := Ioo (-ε) ε ×ˢ Icc a b
  have hL : ContinuousOn (fun w : ℝ × ℝ => (⟨γ w.2,V w.2⟩ : Phase S)) D :=
    hVc.comp continuousOn_snd (fun _ hw => hw.2)
  refine ⟨(scaledField_continuousOn hVc).mono (prod_mono (subset_univ _) Subset.rfl), ?_⟩
  intro z hz
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hV z.2 hz.2
  let c := B.chart e he
  have hsource : (⟨γ z.2,V z.2⟩ : Phase S) ∈ c.source := by
    simpa only [c, B.chart_source, projection, mem_preimage] using hp
  have hscaled : scaledField γ V z ∈ c.source := by
    simpa only [c, B.chart_source, projection, mem_preimage, scaledField, tangentScale] using hp
  let y : ℝ × ℝ → Euclidean (n+n) := fun w => B.productCoordinates.linearEquiv
    ((B.productCoordinates.linearEquiv.symm (x w.2)).1,
      w.1 • (B.productCoordinates.linearEquiv.symm (x w.2)).2)
  have hx' : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun w : ℝ × ℝ => B.productCoordinates.linearEquiv.symm (x w.2)) z :=
    B.productCoordinates.linearEquiv.symm.contDiff.contDiffAt.comp z
      (hx.comp z contDiffAt_snd)
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y z :=
    B.productCoordinates.linearEquiv.contDiff.contDiffAt.comp z
      (hx'.fst.prodMk (contDiffAt_fst.smul hx'.snd))
  refine ⟨c, SmoothManifolds.TangentBundle.chart_mem S B e he, hscaled, y, hy, ?_, ?_⟩
  · dsimp only [y]
    rw [← hxt]
    exact (tangentScale_chart e he ⟨γ z.2,V z.2⟩ hp z.1).symm
  · have htend : Tendsto (fun w : ℝ × ℝ => w.2) (𝓝[D] z) (𝓝[Icc a b] z.2) :=
      continuous_snd.continuousAt.continuousWithinAt.tendsto_nhdsWithin (fun _ hw => hw.2)
    have hnear := (hL z hz).eventually (c.open_source.mem_nhds hsource)
    filter_upwards [heqx.comp_tendsto htend, hnear] with w hw hws
    have hpw : γ w.2 ∈ e.source := by
      change (⟨γ w.2,V w.2⟩ : Phase S) ∈ (B.chart e he).source at hws
      rw [B.chart_source] at hws
      exact hws
    change ((B.chart e he) (tangentScale (w.1,⟨γ w.2,V w.2⟩))).val = _
    dsimp only [Function.comp_def] at hw
    rw [tangentScale_chart e he _ hpw, hw]

/-- Smooth maps on an open domain preserve the coordinate-extension
regularity used for variations on closed strips. -/
theorem smoothVariationOn_comp {m : ℕ} {N : Type u} [TopologicalSpace N]
    {T : SmoothManifold m .euclidean N} {H : M → N} {U : Set M}
    {G : ℝ × ℝ → M} {ε a b : ℝ}
    (hH : ManifoldSmoothOn S.smoothStructure.val T.smoothStructure.val H U)
    (hG : SmoothVariationOn S G ε a b)
    (hGU : ∀ z ∈ Ioo (-ε) ε ×ˢ Icc a b, G z ∈ U) :
    SmoothVariationOn T (fun z => H (G z)) ε a b := by
  constructor
  · intro z hz
    exact (hH _ (hGU z hz)).1.comp_continuousWithinAt (hG.1 z hz)
  · intro z hz
    obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hG.2 z hz
    obtain ⟨d,hd,hq⟩ := T.smoothStructure.property.1.1 (H (G z))
    obtain ⟨W,hW,hzW,K,hK,heqK⟩ := (hH _ (hGU z hz)).2 e he d hd hp hq
    have hxW : x z ∈ W := hxt ▸ hzW
    refine ⟨d,hd,hq,K ∘ x,
      (hK.contDiffAt (hW.mem_nhds hxW)).comp z hx, ?_, ?_⟩
    · change K (x z) = _
      rw [hxt]
      exact heqK.eq_of_nhds
    · filter_upwards [heqK.comp_tendsto (hG.1 z hz),heqx] with w hKw hxw
      exact hKw.symm.trans (congrArg K hxw)

/-- Compactness supplies one open s-interval on which every scaled field
value lies in the actual (possibly proper) exponential domain. -/
theorem exists_common_exponential_interval
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ}
    (hV : ContinuousOn (fun t => (⟨γ t,V t⟩ : Phase S)) (Icc a b)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ z ∈ Ioo (-ε) ε ×ˢ Icc a b,
      scaledField γ V z ∈ exponentialDomain F := by
  let G : ℝ × Icc a b → Phase S := fun z => scaledField γ V (z.1,z.2.val)
  have hG : Continuous G := by
    rw [← continuousOn_univ]
    exact (scaledField_continuousOn hV).comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)).continuousOn
      (fun z _ => ⟨mem_univ _, z.2.property⟩)
  let O := G ⁻¹' exponentialDomain F
  have hO : IsOpen O := (ExponentialNormalCoordinates.domain_open S C F hF).preimage hG
  have hKO : ({(0 : ℝ)} : Set ℝ) ×ˢ (univ : Set (Icc a b)) ⊆ O := by
    rintro ⟨s,t⟩ ⟨hs,_⟩
    have hs0 : s = 0 := hs
    subst s
    simpa only [O, mem_preimage, G, scaledField, tangentScale, zero_smul] using
      (ExponentialNormalCoordinates.zero_section S C F hF (γ t.val)).1
  obtain ⟨U,W,hU,_,h0U,hW,hUW⟩ :=
    generalized_tube_lemma isCompact_singleton isCompact_univ hO hKO
  obtain ⟨ε,hε,hball⟩ := Metric.mem_nhds_iff.mp (hU.mem_nhds (h0U (mem_singleton 0)))
  refine ⟨ε,hε,?_⟩
  intro z hz
  have hzU : z.1 ∈ U := by
    apply hball
    change dist z.1 0 < ε
    simpa only [Real.dist_eq, sub_zero] using (abs_lt.mpr hz.1)
  exact hUW (show (z.1, (⟨z.2,hz.2⟩ : Icc a b)) ∈ U ×ˢ W from
    ⟨hzU,hW (mem_univ _)⟩)



/-- Equality of central curves transports a field into exactly the same
intrinsic tangent coordinates. -/
theorem fiberCoordinates_field_transport {γ η : ℝ → M} (h : γ = η)
    (V : (t : ℝ) → TangentSpace S (η t)) (t : ℝ)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : γ t ∈ e.source) (hq : η t ∈ e.source) :
    (tangentStructure S).fiberCoordinates.equiv e he (γ t) hp ((h.symm ▸ V) t) =
      (tangentStructure S).fiberCoordinates.equiv e he (η t) hq (V t) := by
  subst η
  rfl

/-- The exponential variation has the prescribed intrinsic s-velocity.
This is proved on the actual local exponential domain at the zero section. -/
theorem exponential_variation_velocity
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (γ : ℝ → M)
    (V : (t : ℝ) → TangentSpace S (γ t))
    (hcenter : (fun t => exponential F (scaledField γ V (0,t))) = γ) (t : ℝ) :
    HasVelocityAt S (fun s => exponential F (scaledField γ V (s,t))) 0
      ((hcenter.symm ▸ V) t) := by
  obtain ⟨e,he,hp⟩ := S.smoothStructure.property.1.1 (γ t)
  have hp' : exponential F (scaledField γ V (0,t)) ∈ e.source :=
    (congrFun hcenter t).symm ▸ hp
  refine ⟨?_,e,he,hp',?_⟩
  · have hc : ContinuousAt (fun s => scaledField γ V (s,t)) 0 :=
      tangentScale_continuous.continuousAt.comp
        (f := fun s : ℝ => (s, (⟨γ t,V t⟩ : Phase S)))
        (continuous_id.prodMk continuous_const).continuousAt
    have hdom : scaledField γ V (0,t) ∈ exponentialDomain F := by
      simpa only [scaledField,tangentScale,zero_smul] using
        (ExponentialNormalCoordinates.zero_section S C F hF (γ t)).1
    exact (ExponentialNormalCoordinates.smooth S C F hF _ hdom).1.comp
      (f := fun s => scaledField γ V (s,t)) hc
  · rw [fiberCoordinates_field_transport hcenter V t e he hp' hp]
    exact ExponentialNormalCoordinates.radial_derivative C F hF (γ t) e he hp (V t)

/-- Realization by F(s,t)=exp_{γ(t)}(s V(t)), with one common positive
s-interval and exactly the original finite break parameters. -/
theorem realizes_field : P202Specs.Geometry.MinimizingIndexForm.realizes_fieldType.{u} := by
  intro n M _ S g C hC γ a b hab hγ k node hnode ha hb V hV hVa hVb
  subst a
  subst b
  obtain ⟨G,hG⟩ := ExponentialNormalCoordinates.family_exists S C
  obtain ⟨ε,hε,hdom⟩ := exists_common_exponential_interval C G hG hV.1
  let F : ℝ × ℝ → M := fun z => exponential G (scaledField γ V z)
  have hzero (p : M) : exponential G (⟨p,0⟩ : Phase S) = p :=
    (ExponentialNormalCoordinates.zero_section S C G hG p).2
  have hcenter : (fun t => F (0,t)) = γ := by
    funext t
    simpa only [F,scaledField,tangentScale,zero_smul] using hzero (γ t)
  have hvariation : PiecewiseSmoothVariationOn S F ε node := by
    constructor
    · intro z hz
      apply (ExponentialNormalCoordinates.smooth S C G hG _ (hdom z hz)).1.comp_continuousWithinAt
      exact ((scaledField_continuousOn hV.1).mono
        (prod_mono (subset_univ _) Subset.rfl)) z hz
    · intro i
      have hleft : node 0 ≤ node i.castSucc := hnode.monotone (Fin.zero_le _)
      have hright : node i.succ ≤ node (Fin.last (k+1)) := hnode.monotone (Fin.le_last _)
      have hcont := hV.1.mono (Icc_subset_Icc hleft hright)
      exact smoothVariationOn_comp (ExponentialNormalCoordinates.smooth S C G hG)
        (scaledField_smoothVariationOn hcont (hV.2 i))
        (fun z hz => hdom z ⟨hz.1,⟨hleft.trans hz.2.1,hz.2.2.trans hright⟩⟩)
  have hfixed : FixedEndpoints F ε (node 0) (node (Fin.last (k+1))) := by
    intro s hs
    constructor
    · calc
        F (s,node 0) = γ (node 0) := by
          simpa only [F,scaledField,tangentScale,hVa,smul_zero] using hzero (γ (node 0))
        _ = F (0,node 0) := (congrFun hcenter _).symm
    · calc
        F (s,node (Fin.last (k+1))) = γ (node (Fin.last (k+1))) := by
          simpa only [F,scaledField,tangentScale,hVb,smul_zero] using hzero (γ (node (Fin.last (k+1))))
        _ = F (0,node (Fin.last (k+1))) := (congrFun hcenter _).symm
  refine ⟨ε,F,hcenter,hε,hvariation,hfixed,?_⟩
  intro t ht
  exact PiecewiseCurves.velocity_eq (exponential_variation_velocity C G hG γ V hcenter t)


/-- A minimizing affine geodesic has nonnegative index on every continuous
piecewise smooth zero-endpoint field, without any conjugacy assumption. -/
theorem indexForm_nonneg : P202Specs.Geometry.MinimizingIndexForm.indexForm_nonnegType.{u} :=
  indexForm_nonneg_of_realizes_field realizes_field

end P202.Geometry.MinimizingIndexForm
