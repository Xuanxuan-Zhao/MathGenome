import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.SecondVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.FirstVariation
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import Batteries.Tactic.OpenPrivate

/-! Second variation of energy, paper.tex 4065–4101. The canonical intrinsic
energy, tangent fibers, covariant derivatives and curvature are retained.
The proof differentiates actual smooth scalar germs, derives the pullback
curvature identity without rank assumptions, and cancels internal boundary
terms over fixed finite partitions. Moving endpoint acceleration remains. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

noncomputable abbrev indexForm := @P202.SecondVariationData.indexForm
noncomputable abbrev variationAcceleration := @P202.SecondVariationData.variationAcceleration
noncomputable abbrev accelerationBoundary := @P202.SecondVariationData.accelerationBoundary

/-- The final analytic assembly after the geometric density and product rules
have been established. This lemma does not assume the second-variation formula. -/
theorem secondVariation_of_density {a b : ℝ} (hab : a ≤ b)
    {E B H J : ℝ → ℝ}
    (hE : HasDerivAt (deriv E) (∫ t in a..b, H t) 0)
    (hB : ContinuousOn B (Icc a b))
    (hB' : ∀ t ∈ Ioo a b, HasDerivAt B (H t - J t) t)
    (hH : IntervalIntegrable H volume a b)
    (hJ : IntervalIntegrable J volume a b) :
    HasDerivAt (deriv E) ((∫ t in a..b, J t) + (B b - B a)) 0 := by
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
    hab hB hB' (hH.sub hJ)
  rw [intervalIntegral.integral_sub hH hJ] at hFTC
  convert hE using 1 <;> linarith

/-- The acceleration boundary pairing has no jump at an internal node when
both one-sided central tangents agree. The acceleration uses only the common
s-trace, so it is literally the same tangent vector on both sides. -/
theorem acceleration_boundary_sum
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ)
    (T : (t : ℝ) → TangentSpace S (F (0,t))) :
    (∑ i : Fin (k+1),
      (pairing g (F (0,node i.succ)) (variationAcceleration C F (node i.succ)) (T (node i.succ)) -
       pairing g (F (0,node i.castSucc)) (variationAcceleration C F (node i.castSucc)) (T (node i.castSucc)))) =
      pairing g (F (0,node (Fin.last (k+1))))
        (variationAcceleration C F (node (Fin.last (k+1)))) (T (node (Fin.last (k+1)))) -
      pairing g (F (0,node 0)) (variationAcceleration C F (node 0)) (T (node 0)) := by
  simpa using FirstVariation.sum_segment_boundary node
    (fun _ t => pairing g (F (0,t)) (variationAcceleration C F t) (T t))

/-- The pointwise index pairing on value/derivative jets is bilinear.
No regularity is needed for this purely fiberwise assertion. -/
noncomputable def indexPairing
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (R : CurvatureTensor S) (p : M) (T : TangentSpace S p) :
    (TangentSpace S p × TangentSpace S p) →ₗ[ℝ]
      (TangentSpace S p × TangentSpace S p) →ₗ[ℝ] ℝ where
  toFun v := {
    toFun := fun w => pairing g p v.2 w.2 - pairing g p (R.val p v.1 T T) w.1
    map_add' := by intros; simp [map_add]; ring
    map_smul' := by intros; simp [map_smul, smul_eq_mul]; ring }
  map_add' := by
    intro v z
    apply LinearMap.ext
    intro w
    change pairing g p (v.2 + z.2) w.2 - pairing g p (R.val p (v.1 + z.1) T T) w.1 =
      (pairing g p v.2 w.2 - pairing g p (R.val p v.1 T T) w.1) +
      (pairing g p z.2 w.2 - pairing g p (R.val p z.1 T T) w.1)
    simp only [map_add, LinearMap.add_apply]
    ring
  map_smul' := by
    intro c v
    apply LinearMap.ext
    intro w
    change pairing g p (c • v.2) w.2 - pairing g p (R.val p (c • v.1) T T) w.1 =
      c * (pairing g p v.2 w.2 - pairing g p (R.val p v.1 T T) w.1)
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring

/-- This is precisely the prescribed index integrand, with actual within
covariant derivatives providing the derivative components of the jets. -/
theorem indexIntegrand_eq_indexPairing
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (γ : ℝ → M) (a b : ℝ) (V W : (t : ℝ) → TangentSpace S (γ t)) (t : ℝ) :
    indexIntegrand g C R γ a b V W t = indexPairing g R (γ t)
      (segmentTangent S γ a b t)
      (V t, covariantDerivativeWithin C γ V (Icc a b) t)
      (W t, covariantDerivativeWithin C γ W (Icc a b) t) := rfl

/-- Curvature skew-symmetry supplies the minus sign in the index integrand. -/
theorem curvature_term_sign
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (p : M) (V T : TangentSpace S p) :
    pairing g p (R.val p V T V) T = -pairing g p (R.val p V T T) V :=
  (CurvatureAlgebra.symmetries g C hC R hR p V T V T).2.1

/-- The Jacobi curvature operator is self-adjoint in the metric pairing. -/
theorem curvature_index_symmetric
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (p : M) (V W T : TangentSpace S p) :
    pairing g p (R.val p V T T) W = pairing g p (R.val p W T T) V := by
  have h1 := (CurvatureAlgebra.symmetries g C hC R hR p V T T W).2.2
  have h2 := (CurvatureAlgebra.symmetries g C hC R hR p T W V T).1
  have h3 := (CurvatureAlgebra.symmetries g C hC R hR p W T V T).2.1
  change pairing g p (R.val p V T T) W = pairing g p (R.val p T W V) T at h1
  change pairing g p (R.val p T W V) T = -pairing g p (R.val p W T V) T at h2
  change pairing g p (R.val p W T V) T = -pairing g p (R.val p W T T) V at h3
  linarith

theorem indexForm_symmetric
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (γ : ℝ → M) (a b : ℝ) (V W : (t : ℝ) → TangentSpace S (γ t)) :
    indexForm g C R γ a b V W = indexForm g C R γ a b W V := by
  unfold indexForm P202.SecondVariationData.indexForm
  congr 1
  funext t
  unfold indexIntegrand
  rw [curvature_index_symmetric g C hC R hR (γ t) (V t) (W t)]
  congr 1
  exact g.symmetric _ _ _

/-- Additivity of the prescribed integrand in a C¹ field. -/
theorem indexIntegrand_add_left
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CoordinateC1On S γ (Icc a b)) (hγc : ContinuousOn γ (Icc a b))
    {V U W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b))
    (hU : C1FieldOn (B := tangentBundle S) γ U (Icc a b))
    {t : ℝ} (ht : t ∈ Icc a b) :
    indexIntegrand g C R γ a b (fun t => V t + U t) W t =
      indexIntegrand g C R γ a b V W t + indexIntegrand g C R γ a b U W t := by
  have hDV := (CurveCovariantDerivative.segment_derivative C hab hγ hγc hV ht).1
  have hDU := (CurveCovariantDerivative.segment_derivative C hab hγ hγc hU ht).1
  have hadd := CurveCovariantDerivative.covariantDerivativeWithin_add C ht
    (uniqueDiffOn_Icc hab t ht) hDV hDU
  simp only [indexIntegrand, hadd, map_add, LinearMap.add_apply]
  ring

theorem indexIntegrand_smul_left
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CoordinateC1On S γ (Icc a b)) (hγc : ContinuousOn γ (Icc a b))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b))
    (c : ℝ) {t : ℝ} (ht : t ∈ Icc a b) :
    indexIntegrand g C R γ a b (fun t => c • V t) W t =
      c * indexIntegrand g C R γ a b V W t := by
  have hDV := (CurveCovariantDerivative.segment_derivative C hab hγ hγc hV ht).1
  have hsmul := CurveCovariantDerivative.covariantDerivativeWithin_smul C ht
    (uniqueDiffOn_Icc hab t ht) hDV (hasDerivWithinAt_const t (Icc a b) c)
  simp only [zero_smul, zero_add] at hsmul
  simp only [indexIntegrand, hsmul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

/-- Integration preserves the established pointwise additivity when the two
summands are integrable. The integrability needed by the unrestricted geometric theorem is
derived from regularity below. -/
theorem indexForm_add_left_of_integrable
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CoordinateC1On S γ (Icc a b)) (hγc : ContinuousOn γ (Icc a b))
    {V U W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b))
    (hU : C1FieldOn (B := tangentBundle S) γ U (Icc a b))
    (hVW : IntervalIntegrable (indexIntegrand g C R γ a b V W) volume a b)
    (hUW : IntervalIntegrable (indexIntegrand g C R γ a b U W) volume a b) :
    indexForm g C R γ a b (fun t => V t + U t) W =
      indexForm g C R γ a b V W + indexForm g C R γ a b U W := by
  change (∫ t in a..b, indexIntegrand g C R γ a b (fun t => V t + U t) W t) = _
  rw [show (∫ t in a..b, indexIntegrand g C R γ a b (fun t => V t + U t) W t) =
      ∫ t in a..b, (indexIntegrand g C R γ a b V W t + indexIntegrand g C R γ a b U W t) from
    intervalIntegral.integral_congr_Ioo_of_le hab.le (fun t ht =>
      indexIntegrand_add_left g C R hab hγ hγc hV hU (Ioo_subset_Icc_self ht))]
  exact intervalIntegral.integral_add hVW hUW

theorem indexForm_smul_left
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CoordinateC1On S γ (Icc a b)) (hγc : ContinuousOn γ (Icc a b))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b)) (c : ℝ) :
    indexForm g C R γ a b (fun t => c • V t) W = c * indexForm g C R γ a b V W := by
  change (∫ t in a..b, indexIntegrand g C R γ a b (fun t => c • V t) W t) = _
  rw [show (∫ t in a..b, indexIntegrand g C R γ a b (fun t => c • V t) W t) =
      ∫ t in a..b, c * indexIntegrand g C R γ a b V W t from
    intervalIntegral.integral_congr_Ioo_of_le hab.le (fun t ht =>
      indexIntegrand_smul_left g C R hab hγ hγc hV c (Ioo_subset_Icc_self ht))]
  exact intervalIntegral.integral_const_mul c _

/-- A constant parameter germ has zero actual intrinsic velocity. -/
theorem hasVelocityAt_zero_of_eventually_constant
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {c : ℝ → M} {t : ℝ}
    (hc : c =ᶠ[𝓝 t] fun _ => c t) : HasVelocityAt S c t 0 := by
  simpa using PiecewiseCurves.HasVelocityAt.congr
    (PiecewiseCurves.hasVelocityAt_const (S := S) (c t) t) hc.symm

/-- Along a constant parameter germ the covariant derivative of the actual
velocity is zero, for every connection. No geometric formula is assumed. -/
theorem acceleration_zero_of_eventually_constant
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (C : Connection (tangentBundle S))
    {c : ℝ → M} {t : ℝ} (hc : c =ᶠ[𝓝 t] fun _ => c t) :
    covariantDerivative C c (velocity S c) t = 0 := by
  have hv0 : velocity S c t = 0 :=
    PiecewiseCurves.velocity_eq (hasVelocityAt_zero_of_eventually_constant hc)
  have hv : ∀ᶠ s in 𝓝 t, velocity S c s = 0 := by
    filter_upwards [hc, eventually_eventually_nhds.mpr hc] with s hs hsc
    have hsc' : c =ᶠ[𝓝 s] fun _ => c t := hsc
    have hsc'' : c =ᶠ[𝓝 s] fun _ => c s := by
      filter_upwards [hsc'] with r hr
      exact hr.trans hs.symm
    exact PiecewiseCurves.velocity_eq (hasVelocityAt_zero_of_eventually_constant hsc'')
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 (c t)
  let i : TangentIndex S := ⟨e, he⟩
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B i
  have hi : c t ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hp
  have hU : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  have hcoef : coefficientsAlong b c (velocity S c) =ᶠ[𝓝 t] fun _ => 0 := by
    filter_upwards [hv] with s hs
    simp [coefficientsAlong, hs]
  have hd : HasDerivWithinAt (coefficientsAlong b c (velocity S c)) 0 univ t :=
    ((hasDerivAt_const t (0 : Euclidean n)).congr_of_eventuallyEq hcoef).hasDerivWithinAt
  apply CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ t)
    uniqueDiffWithinAt_univ
  refine ⟨0, CurveCovariantDerivative.ordinary_velocity_iff.mpr
    (hasVelocityAt_zero_of_eventually_constant hc), _, hU, b, hi, 0, hd, ?_⟩
  simp [frameDerivative, coefficientsAlong, hv0]

theorem fixed_endpoint_boundary :
    P202Specs.Geometry.SecondVariation.fixed_endpoint_boundaryType.{u} := by
  intro n M _ S g C F ε a b hε hfix
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have ha : (fun s => F (s,a)) =ᶠ[𝓝 0] fun _ => F (0,a) := by
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact (hfix s hs).1
  have hb : (fun s => F (s,b)) =ᶠ[𝓝 0] fun _ => F (0,b) := by
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact (hfix s hs).2
  have hA := acceleration_zero_of_eventually_constant C ha
  have hB := acceleration_zero_of_eventually_constant C hb
  change pairing g (F (0,b)) (variationAcceleration C F b) (segmentVelocity S F a b b) -
    pairing g (F (0,a)) (variationAcceleration C F a) (segmentVelocity S F a b a) = 0
  rw [show variationAcceleration C F b = 0 from hB,
    show variationAcceleration C F a = 0 from hA]
  simp

/-- Geometric integration by parts along the affine central geodesic. The
second-density identity is an explicit input of this assembly helper; the full theorem below derives it from the original smooth-variation
hypotheses. -/
theorem secondVariation_of_geodesic_density
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    (R : CurvatureTensor S) (F : ℝ × ℝ → M) {a b : ℝ} (hab : a < b)
    (hgeo : IsAffineGeodesicSegment C (fun t => F (0,t)) a b)
    (hA : C1FieldOn (B := tangentBundle S) (fun t => F (0,t))
      (variationAcceleration C F) (Icc a b))
    {H : ℝ → ℝ} (hH : ContinuousOn H (Icc a b))
    (hE : HasDerivAt (deriv (variedEnergy g F a b)) (∫ t in a..b, H t) 0)
    (hId : ∀ t ∈ Icc a b, H t =
      indexIntegrand g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) t +
      pairing g (F (0,t))
        (covariantDerivativeWithin C (fun t => F (0,t)) (variationAcceleration C F) (Icc a b) t)
        (segmentVelocity S F a b t)) :
    HasDerivAt (deriv (variedEnergy g F a b))
      (indexForm g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) +
        accelerationBoundary g C F a b) 0 := by
  let γ : ℝ → M := fun t => F (0,t)
  let T := segmentVelocity S F a b
  let A := variationAcceleration C F
  let B : ℝ → ℝ := fun t => pairing g (γ t) (A t) (T t)
  let P : ℝ → ℝ := fun t => pairing g (γ t)
    (covariantDerivativeWithin C γ A (Icc a b) t) (T t)
  let J := indexIntegrand g C R γ a b (variationField S F) (variationField S F)
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hγ : CoordinateC1On S γ (Icc a b) :=
    FirstVariation.variation_coordinateC1On_slice (F := fun z => γ z.2) hgeo.1 h0
  have hγc : ContinuousOn γ (Icc a b) :=
    FirstVariation.variation_continuousOn_slice (F := fun z => γ z.2) hgeo.1 h0
  have hT : C1FieldOn (B := tangentBundle S) γ T (Icc a b) :=
    FirstVariation.segmentVelocity_c1 (F := fun z => γ z.2) hgeo.1 (by norm_num) hab
  have hDT (t : ℝ) (ht : t ∈ Icc a b) :
      covariantDerivativeWithin C γ T (Icc a b) t = 0 :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
      (uniqueDiffOn_Icc hab t ht) (hgeo.2 t ht)
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt B (P t) (Icc a b) t := by
    have hd := TorsionAndMetric.metric_curve_product_c1 (tangentBundle S) g C hC
      ht (uniqueDiffOn_Icc hab t ht) hγ hγc hA hT
    simpa only [B, P, A, pairing, hDT t ht, map_zero, add_zero] using hd
  have hBc : ContinuousOn B (Icc a b) := fun t ht => (hd t ht).continuousWithinAt
  have hBd : ContinuousOn (derivWithin B (Icc a b)) (Icc a b) := by
    apply FirstVariation.derivWithin_continuousOn_of_local_c1 (uniqueDiffOn_Icc hab)
    intro t ht
    exact FirstVariation.metric_pairing_c1_extension (tangentBundle S) g hγ hγc ht hA hT
  have hPc : ContinuousOn P (Icc a b) := hBd.congr fun t ht =>
    ((hd t ht).derivWithin (uniqueDiffOn_Icc hab t ht)).symm
  have hJc : ContinuousOn J (Icc a b) := by
    apply (hH.sub hPc).congr
    intro t ht
    change J t = H t - P t
    have hid : H t = J t + P t := hId t ht
    linarith
  have hB' : ∀ t ∈ Ioo a b, HasDerivAt B (H t - J t) t := by
    intro t ht
    have hid : H t = J t + P t := hId t (Ioo_subset_Icc_self ht)
    convert (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2) using 1
    linarith
  exact secondVariation_of_density hab.le hE hBc hB'
    (hH.intervalIntegrable_of_Icc hab.le) (hJc.intervalIntegrable_of_Icc hab.le)

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
open private sum_integrals from MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthLaws
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem smoothVariationOn_mono_interval {F : ℝ × ℝ → M} {ε a b l r : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hal : a ≤ l) (hrb : r ≤ b) :
    SmoothVariationOn S F ε l r := by
  have hsub : Ioo (-ε) ε ×ˢ Icc l r ⊆ Ioo (-ε) ε ×ˢ Icc a b := by
    rintro z ⟨hs, ht⟩
    exact ⟨hs, hal.trans ht.1, ht.2.trans hrb⟩
  refine ⟨hF.1.mono hsub, ?_⟩
  intro z hz
  obtain ⟨e, he, hp, x, hx, hv, hxeq⟩ := hF.2 z (hsub hz)
  exact ⟨e, he, hp, x, hx, hv, hxeq.filter_mono (nhdsWithin_mono z hsub)⟩

theorem hasCovariantDerivativeWithinAt_mono
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J K : Set ℝ} {t : ℝ}
    {D : TangentSpace S (γ t)}
    (h : HasCovariantDerivativeWithinAt C γ V J t D) (hK : K ⊆ J) :
    HasCovariantDerivativeWithinAt C γ V K t D := by
  obtain ⟨T, ⟨hc, e, he, hp, hd⟩, U, hU, b, hpt, v, hv, hD⟩ := h
  exact ⟨T, ⟨hc.mono hK, e, he, hp, hd.mono hK⟩,
    U, hU, b, hpt, v, hv.mono hK, hD⟩

theorem hasCovariantDerivativeWithinAt_of_mem_nhds
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J K : Set ℝ} {t : ℝ}
    {D : TangentSpace S (γ t)}
    (h : HasCovariantDerivativeWithinAt C γ V K t D) (hK : K ∈ 𝓝 t) :
    HasCovariantDerivativeWithinAt C γ V J t D := by
  obtain ⟨T, ⟨hc, e, he, hp, hd⟩, U, hU, b, hpt, v, hv, hD⟩ := h
  exact ⟨T, ⟨(hc.continuousAt hK).continuousWithinAt, e, he, hp,
    (hd.hasDerivAt hK).hasDerivWithinAt⟩,
    U, hU, b, hpt, v, (hv.hasDerivAt hK).hasDerivWithinAt, hD⟩

theorem covariantDerivativeWithin_eq_of_mem_nhds
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {J K : Set ℝ} {t : ℝ}
    (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t) (hK : K ∈ 𝓝 t)
    (hex : ∃ D, HasCovariantDerivativeWithinAt C γ V K t D)
    :
    covariantDerivativeWithin C γ V J t = covariantDerivativeWithin C γ V K t := by
  exact CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ
    (hasCovariantDerivativeWithinAt_of_mem_nhds C
      (CurveCovariantDerivative.covariantDerivativeWithin_spec C hex) hK)

/-- Differentiating a finite subdivision twice is valid on a common germ.
The first derivatives of the summands must exist near the base parameter. -/
theorem secondDerivative_of_eventually_sum {ι : Type*} [Fintype ι]
    {E : ℝ → ℝ} {e : ι → ℝ → ℝ} {d : ι → ℝ} {s : ℝ}
    (heq : E =ᶠ[𝓝 s] fun r => ∑ i, e i r)
    (hfirst : ∀ᶠ r in 𝓝 s, ∀ i, DifferentiableAt ℝ (e i) r)
    (hsecond : ∀ i, HasDerivAt (deriv (e i)) (d i) s) :
    HasDerivAt (deriv E) (∑ i, d i) s := by
  have hsum : HasDerivAt (fun r => ∑ i, deriv (e i) r) (∑ i, d i) s :=
    HasDerivAt.fun_sum (fun i _ => hsecond i)
  apply hsum.congr_of_eventuallyEq
  filter_upwards [heq.deriv, hfirst] with r hr hdiff
  exact hr.trans (deriv_fun_sum (fun i _ => hdiff i))


theorem hasCovariantDerivativeWithinAt_congr_field
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V W : (t : ℝ) → TangentSpace S (γ t)} {J : Set ℝ} {t : ℝ}
    {D : TangentSpace S (γ t)} (ht : t ∈ J)
    (h : HasCovariantDerivativeWithinAt C γ V J t D)
    (heq : ∀ r ∈ J, W r = V r) :
    HasCovariantDerivativeWithinAt C γ W J t D := by
  obtain ⟨T, hT, U, hU, b, hpt, v, hv, hD⟩ := h
  have hcoeff : coefficientsAlong b γ W =ᶠ[𝓝[J] t] coefficientsAlong b γ V := by
    filter_upwards [self_mem_nhdsWithin] with r hr
    simp only [coefficientsAlong, heq r hr]
  have hval : coefficientsAlong b γ W t = coefficientsAlong b γ V t := by
    simp only [coefficientsAlong, heq t ht]
  refine ⟨T, hT, U, hU, b, hpt, v, hv.congr_of_eventuallyEq hcoeff hval, ?_⟩
  simpa only [frameDerivative, hval] using hD

theorem segmentTangent_restrict {γ : ℝ → M} {a b l r t : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l < r) (ht : t ∈ Icc l r) :
    segmentTangent S γ l r t = segmentTangent S γ a b t := by
  have hsmall := FirstVariation.segmentVelocity_spec
    (smoothVariationOn_mono_interval hγ hal hrb) (by norm_num) ht
  have hwhole := FirstVariation.segmentVelocity_spec hγ (by norm_num)
    (show t ∈ Icc a b from ⟨hal.trans ht.1, ht.2.trans hrb⟩)
  have hwhole' : HasVelocityWithinAt S γ (Icc l r) t (segmentTangent S γ a b t) := by
    obtain ⟨hc, e, he, hp, hd⟩ := hwhole
    have hsub : Icc l r ⊆ Icc a b := Icc_subset_Icc hal hrb
    exact ⟨hc.mono hsub, e, he, hp, hd.mono hsub⟩
  exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hlr t ht) hsmall hwhole'

theorem affineGeodesicSegment_restrict
    (C : Connection (tangentBundle S)) {γ : ℝ → M} {a b l r : ℝ}
    (hγ : IsAffineGeodesicSegment C γ a b)
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l < r) :
    IsAffineGeodesicSegment C γ l r := by
  refine ⟨smoothVariationOn_mono_interval hγ.1 hal hrb, ?_⟩
  intro t ht
  exact hasCovariantDerivativeWithinAt_congr_field C ht
    (hasCovariantDerivativeWithinAt_mono C
      (hγ.2 t ⟨hal.trans ht.1, ht.2.trans hrb⟩) (Icc_subset_Icc hal hrb))
    (fun r hr => segmentTangent_restrict hγ.1 hal hrb hlr hr)


theorem indexIntegrand_restrict
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b l r t : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    (hal : a ≤ l) (hrb : r ≤ b) (hlr : l < r)
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc l r))
    (hW : C1FieldOn (B := tangentBundle S) γ W (Icc l r))
    (ht : t ∈ Ioo l r) :
    indexIntegrand g C R γ a b V W t = indexIntegrand g C R γ l r V W t := by
  have htK := Ioo_subset_Icc_self ht
  have htJ : t ∈ Icc a b := ⟨hal.trans htK.1, htK.2.trans hrb⟩
  have hab : a < b := (hal.trans_lt hlr).trans_le hrb
  have hsmall := smoothVariationOn_mono_interval hγ hal hrb
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_coordinateC1On_slice hsmall h0
  have hcc := FirstVariation.variation_continuousOn_slice hsmall h0
  have hder (U : (t : ℝ) → TangentSpace S (γ t))
      (hU : C1FieldOn (B := tangentBundle S) γ U (Icc l r)) :
      covariantDerivativeWithin C γ U (Icc a b) t =
        covariantDerivativeWithin C γ U (Icc l r) t :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C htJ
      (uniqueDiffOn_Icc hab t htJ)
      (hasCovariantDerivativeWithinAt_of_mem_nhds C
        (CurveCovariantDerivative.segment_derivative C hlr hc hcc hU htK).1
        (Icc_mem_nhds ht.1 ht.2))
  simp only [indexIntegrand, hder V hV, hder W hW,
    segmentTangent_restrict hγ hal hrb hlr htK]

/-- The canonical index form splits over fixed finite breaks. Endpoint
values of the default total covariant derivative are discarded only through
finite-set invariance of the integral. -/
theorem indexForm_subdivision_of_integrable
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 (node 0) (node (Fin.last (k+1))))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ)))
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)))
    (hint : ∀ i : Fin (k+1), IntervalIntegrable
      (indexIntegrand g C R γ (node i.castSucc) (node i.succ) V W) volume
      (node i.castSucc) (node i.succ)) :
    indexForm g C R γ (node 0) (node (Fin.last (k+1))) V W =
      ∑ i : Fin (k+1), indexForm g C R γ (node i.castSucc) (node i.succ) V W := by
  classical
  let J := indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W
  have hlt (i : Fin (k+1)) : node i.castSucc < node i.succ :=
    hnode (Fin.castSucc_lt_succ (i := i))
  have hleft (i : Fin (k+1)) : node 0 ≤ node i.castSucc := hnode.monotone (Fin.zero_le _)
  have hright (i : Fin (k+1)) : node i.succ ≤ node (Fin.last (k+1)) :=
    hnode.monotone (Fin.le_last _)
  have heq (i : Fin (k+1)) (t : ℝ)
      (ht : t ∈ uIoc (node i.castSucc) (node i.succ))
      (hne : t ∉ ({node i.succ} : Finset ℝ)) :
      J t = indexIntegrand g C R γ (node i.castSucc) (node i.succ) V W t := by
    rw [uIoc_of_le (hlt i).le] at ht
    have hne' : t ≠ node i.succ := by simpa only [Finset.mem_singleton] using hne
    exact indexIntegrand_restrict g C R hγ (hleft i) (hright i) (hlt i)
      (hV i) (hW i) ⟨ht.1, lt_of_le_of_ne ht.2 hne'⟩
  have hglobal (i : Fin (k+1)) : IntervalIntegrable J volume
      (node i.castSucc) (node i.succ) :=
    (PiecewiseCurves.intervalIntegrable_iff_of_eqOn_off_finite {node i.succ} (heq i)).mpr (hint i)
  have hsum := sum_integrals node hglobal
  change (∫ t in node 0..node (Fin.last (k+1)), J t) = _
  rw [← hsum]
  apply Finset.sum_congr rfl
  intro i _
  exact PiecewiseCurves.integral_eq_of_eqOn_off_finite {node i.succ} (heq i)


/-- All intermediate acceleration terms cancel, including their intrinsic
one-sided central velocities, on a smooth central curve. -/
theorem accelerationBoundary_subdivision
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => F (0,z.2)) 1
      (node 0) (node (Fin.last (k+1)))) :
    (∑ i : Fin (k+1), accelerationBoundary g C F (node i.castSucc) (node i.succ)) =
      accelerationBoundary g C F (node 0) (node (Fin.last (k+1))) := by
  have hvel (i : Fin (k+1)) (t : ℝ) (ht : t ∈ Icc (node i.castSucc) (node i.succ)) :
      segmentVelocity S F (node i.castSucc) (node i.succ) t =
        segmentVelocity S F (node 0) (node (Fin.last (k+1))) t :=
    segmentTangent_restrict (S := S) (γ := fun t => F (0,t)) hγ (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _)) (hnode (Fin.castSucc_lt_succ (i := i))) ht
  calc
    _ = ∑ i : Fin (k+1),
        (pairing g (F (0,node i.succ)) (variationAcceleration C F (node i.succ))
          (segmentVelocity S F (node 0) (node (Fin.last (k+1))) (node i.succ)) -
        pairing g (F (0,node i.castSucc)) (variationAcceleration C F (node i.castSucc))
          (segmentVelocity S F (node 0) (node (Fin.last (k+1))) (node i.castSucc))) := by
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [accelerationBoundary, P202.SecondVariationData.accelerationBoundary]
      rw [hvel i _ ⟨(hnode (Fin.castSucc_lt_succ (i := i))).le, le_rfl⟩,
        hvel i _ ⟨le_rfl, (hnode (Fin.castSucc_lt_succ (i := i))).le⟩]
    _ = _ := acceleration_boundary_sum g C F node
      (segmentVelocity S F (node 0) (node (Fin.last (k+1))))

/-- Actual second derivatives of the energies on a fixed partition sum to
the actual second derivative of the canonical total energy. -/
theorem variedEnergy_second_subdivision
    (g : RiemannianMetric S) {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    (hF : ∀ i : Fin (k+1), SmoothVariationOn S F ε (node i.castSucc) (node i.succ))
    (hfirst : ∀ s ∈ Ioo (-ε) ε, ∀ i : Fin (k+1),
      DifferentiableAt ℝ (variedEnergy g F (node i.castSucc) (node i.succ)) s)
    {d : Fin (k+1) → ℝ}
    (hsecond : ∀ i : Fin (k+1), HasDerivAt
      (deriv (variedEnergy g F (node i.castSucc) (node i.succ))) (d i) 0) :
    HasDerivAt (deriv (variedEnergy g F (node 0) (node (Fin.last (k+1)))))
      (∑ i, d i) 0 := by
  apply secondDerivative_of_eventually_sum (e := fun i s =>
    variedEnergy g F (node i.castSucc) (node i.succ) s) ?_ ?_ hsecond
  · filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact (FirstVariation.varied_functionals_subdivision g node hnode hF hs).1
  · filter_upwards [Ioo_mem_nhds (show -ε < (0 : ℝ) by linarith) hε] with s hs
    exact hfirst s hs

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData P202.MetricData P202.CurveData
  P202.ConnectionData P202.CurveConnectionData P202.LeviCivitaData P202.FirstVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

/-- Differentiating actual scalar smooth germs in the open strip direction
preserves smooth germs, including at the two closed edges. -/
theorem scalar_partial_extension
    {I J : Set ℝ} (hI : IsOpen I) {H : ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hz : z ∈ I ×ˢ J) {y : ℝ × ℝ → ℝ}
    (hy : ContDiffAt ℝ (⊤ : ℕ∞) y z)
    (he : H =ᶠ[𝓝[I ×ˢ J] z] y) :
    ∃ Q : ℝ × ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) Q z ∧
      (fun w : ℝ × ℝ => deriv (fun s => H (s,w.2)) w.1)
        =ᶠ[𝓝[I ×ˢ J] z] Q := by
  refine ⟨fun w => fderiv ℝ y w (1,0), ?_, ?_⟩
  · exact (hy.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  · have hnear := eventually_eventually_nhdsWithin.mpr he
    have hy1 : ContDiffAt ℝ 1 y z := hy.of_le (by simp)
    have hynear : ∀ᶠ w in 𝓝[I ×ˢ J] z, ContDiffAt ℝ 1 y w :=
      (hy1.eventually (by simp)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hnear, hynear, self_mem_nhdsWithin] with w hw hyw hwD
    have hline : Tendsto (fun s : ℝ => (s,w.2)) (𝓝 w.1) (𝓝[I ×ˢ J] w) := by
      apply tendsto_nhdsWithin_iff.mpr
      refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
      filter_upwards [hI.mem_nhds hwD.1] with s hs
      exact ⟨hs, hwD.2⟩
    have hdy := (hyw.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))
    have hw' : H =ᶠ[𝓝[I ×ˢ J] w] y := hw
    exact (hdy.congr_of_eventuallyEq (hw'.comp_tendsto hline)).deriv

/-- The second strip partial of a function with actual smooth scalar germs
exists and is jointly continuous on the closed strip. -/
theorem scalar_second_partial_calculus
    {I J : Set ℝ} (hI : IsOpen I) {H : ℝ × ℝ → ℝ}
    (hH : ∀ z ∈ I ×ˢ J, ∃ y : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) y z ∧ H =ᶠ[𝓝[I ×ˢ J] z] y) :
    ContinuousOn (fun z : ℝ × ℝ => deriv (fun s => deriv
      (fun r => H (r,z.2)) s) z.1) (I ×ˢ J) ∧
      ∀ z ∈ I ×ˢ J, HasDerivAt (fun s => deriv (fun r => H (r,z.2)) s)
        (deriv (fun s => deriv (fun r => H (r,z.2)) s) z.1) z.1 := by
  have hg : ∀ z ∈ I ×ˢ J, ∃ Q : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) Q z ∧
        (fun w : ℝ × ℝ => deriv (fun s => H (s,w.2)) w.1)
          =ᶠ[𝓝[I ×ˢ J] z] Q := by
    intro z hz
    obtain ⟨y, hy, he⟩ := hH z hz
    exact scalar_partial_extension hI hz hy he
  exact (FirstVariation.scalar_germs_on_strip hI hg).2

/-- Parameter differentiation of a continuous density with a jointly
continuous derivative at any point in the open parameter interval. -/
theorem hasDerivAt_integral_on_open_strip
    {a b ε s₀ : ℝ} (hab : a ≤ b) (hs₀ : s₀ ∈ Ioo (-ε) ε)
    {H G : ℝ × ℝ → ℝ}
    (hH : ContinuousOn H (Ioo (-ε) ε ×ˢ Icc a b))
    (hG : ContinuousOn G (Ioo (-ε) ε ×ˢ Icc a b))
    (hder : ∀ z ∈ Ioo (-ε) ε ×ˢ Icc a b,
      HasDerivAt (fun r => H (r,z.2)) (G z) z.1) :
    HasDerivAt (fun s => ∫ t in a..b, H (s,t)) (∫ t in a..b, G (s₀,t)) s₀ := by
  let δ : ℝ := min (s₀ + ε) (ε - s₀) / 2
  have hδ : 0 < δ := by
    dsimp [δ]
    exact div_pos (lt_min (by linarith [hs₀.1]) (by linarith [hs₀.2])) (by norm_num)
  have hsub : ∀ z ∈ Icc (-δ) δ ×ˢ Icc a b,
      (s₀ + z.1, z.2) ∈ Ioo (-ε) ε ×ˢ Icc a b := by
    intro z hz
    have hdl : 2 * δ ≤ s₀ + ε := by
      dsimp [δ]
      linarith [min_le_left (s₀ + ε) (ε - s₀)]
    have hdr : 2 * δ ≤ ε - s₀ := by
      dsimp [δ]
      linarith [min_le_right (s₀ + ε) (ε - s₀)]
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have htrans : ContinuousOn (fun z : ℝ × ℝ => (s₀ + z.1,z.2))
      (Icc (-δ) δ ×ˢ Icc a b) :=
    (continuous_const.add continuous_fst).prodMk continuous_snd |>.continuousOn
  have hd := FirstVariation.hasDerivAt_integral_on_rectangle hab hδ
    (hH.comp htrans hsub) (hG.comp htrans hsub) (fun s hs t ht => by
      have h := (hder (s₀+s,t) (hsub (s,t) ⟨⟨hs.1.le,hs.2.le⟩,ht⟩)).comp s
        ((hasDerivAt_id s).const_add s₀)
      convert h using 1 <;> simp [Function.comp_def] <;> rfl)
  have hd' : HasDerivAt (fun s => ∫ t in a..b, H (s₀+s,t))
      (∫ t in a..b, G (s₀,t)) (s₀-s₀) := by
    simpa only [Function.comp_def, add_zero, sub_self] using hd
  have hd'' := hd'.comp (h := fun s => s-s₀) s₀ ((hasDerivAt_id s₀).sub_const s₀)
  simpa only [Function.comp_def, add_sub_cancel, mul_one] using hd''

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Restrict and recenter the open variation parameter. The two bounds are
precisely what is needed to map the new strip into the original one. -/
theorem smoothVariation_recenter
    (hF : SmoothVariationOn S F ε a b) {s₀ δ : ℝ}
    (hleft : δ ≤ s₀ + ε) (hright : δ ≤ ε - s₀) :
    SmoothVariationOn S (fun z => F (s₀ + z.1,z.2)) δ a b := by
  let φ : ℝ × ℝ → ℝ × ℝ := fun z => (s₀ + z.1,z.2)
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ :=
    (contDiff_const.add contDiff_fst).prodMk contDiff_snd
  have hmaps : MapsTo φ (Ioo (-δ) δ ×ˢ Icc a b) (Ioo (-ε) ε ×ˢ Icc a b) := by
    intro z hz
    exact ⟨⟨by dsimp [φ]; linarith [hz.1.1],
      by dsimp [φ]; linarith [hz.1.2]⟩,hz.2⟩
  refine ⟨hF.1.comp hφ.continuous.continuousOn hmaps, ?_⟩
  intro z hz
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hF.2 (φ z) (hmaps hz)
  refine ⟨e, he, hp, x ∘ φ, hx.comp z hφ.contDiffAt, hxt, ?_⟩
  exact heq.comp_tendsto (hφ.continuous.continuousAt.continuousWithinAt.tendsto_nhdsWithin
    (fun _ hw => hmaps hw))

/-- The first derivative density at every interior variation parameter is
its canonical covariant pairing, computed on a recentered variation. -/
theorem sliceSquaredSpeed_hasDerivAt_recentered
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (hF : SmoothVariationOn S F ε a b)
    (hab : a < b) {s₀ t : ℝ} (hs₀ : s₀ ∈ Ioo (-ε) ε) (ht : t ∈ Icc a b) :
    let Fc : ℝ × ℝ → M := fun z => F (s₀ + z.1,z.2)
    HasDerivAt (fun s => FirstVariation.squaredVariationSpeed g F a b (s,t))
      (2 * pairing g (Fc (0,t))
        (covariantDerivativeWithin C (fun r => Fc (0,r))
          (variationField S Fc) (Icc a b) t) (segmentVelocity S Fc a b t)) s₀ := by
  dsimp only
  let δ : ℝ := min (s₀ + ε) (ε - s₀)
  have hδ : 0 < δ := lt_min (by linarith [hs₀.1]) (by linarith [hs₀.2])
  have hFc := smoothVariation_recenter hF
    (min_le_left (s₀ + ε) (ε - s₀)) (min_le_right (s₀ + ε) (ε - s₀))
  have hm := FirstVariation.sliceVelocity_mixed_covariantDerivative g C hC hFc hδ hab ht
  have hd := FirstVariation.squaredVariationSpeed_derivative g C hC.2
    (F := fun z => F (s₀ + z.1,z.2)) hδ ht hm
  have hd' : HasDerivAt
      (fun r => FirstVariation.squaredVariationSpeed g F a b (s₀+r,t))
      (2 * pairing g (F (s₀+0,t))
        (covariantDerivativeWithin C (fun r => F (s₀+0,r))
          (variationField S (fun z => F (s₀ + z.1,z.2))) (Icc a b) t)
        (segmentVelocity S (fun z => F (s₀ + z.1,z.2)) a b t)) (s₀-s₀) := by
    simpa only [FirstVariation.squaredVariationSpeed, FirstVariation.sliceVelocity,
      sub_self] using hd
  have hd'' := hd'.comp (h := fun s => s-s₀) s₀ ((hasDerivAt_id s₀).sub_const s₀)
  simpa only [Function.comp_def, add_sub_cancel, mul_one] using hd''

/-- The actual second parameter derivative of the intrinsic slice energy
density. The within velocity makes this defined at the closed t-edges. -/
noncomputable def secondEnergyDensity (g : RiemannianMetric S)
    (F : ℝ × ℝ → M) (a b : ℝ) (s t : ℝ) : ℝ :=
  (1/2 : ℝ) * deriv (fun r => deriv
    (fun q => FirstVariation.squaredVariationSpeed g F a b (q,t)) r) s

/-- The variation energy is differentiable at every parameter in its open
strip; its derivative is the integral of the actual first partial density. -/
theorem variedEnergy_hasDerivAt_density
    (g : RiemannianMetric S) (hF : SmoothVariationOn S F ε a b)
    (hab : a < b) {s : ℝ} (hs : s ∈ Ioo (-ε) ε) :
    HasDerivAt (variedEnergy g F a b)
      ((1/2 : ℝ) * ∫ t in a..b, deriv
        (fun r => FirstVariation.squaredVariationSpeed g F a b (r,t)) s) s := by
  obtain ⟨hH, hG, hdH⟩ := FirstVariation.squaredVariationSpeed_calculus g hF hab
  have h := (hasDerivAt_integral_on_open_strip hab.le hs hH hG hdH).const_mul (1/2 : ℝ)
  apply h.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioo.mem_nhds hs] with r hr
  exact FirstVariation.variedEnergy_eq_within_integral g hF hab.le hr

/-- Actual twice differentiability of the variation energy and the integral
formula for its second scalar density, with no density certificate assumed. -/
theorem variedEnergy_second_density_calculus
    (g : RiemannianMetric S) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b) :
    ContinuousOn (fun t => secondEnergyDensity g F a b 0 t) (Icc a b) ∧
      HasDerivAt (deriv (variedEnergy g F a b))
        (∫ t in a..b, secondEnergyDensity g F a b 0 t) 0 := by
  let H := FirstVariation.squaredVariationSpeed g F a b
  let G : ℝ × ℝ → ℝ := fun z => deriv (fun r => H (r,z.2)) z.1
  let K : ℝ × ℝ → ℝ := fun z => deriv (fun r => G (r,z.2)) z.1
  obtain ⟨hH, hG, hdH⟩ := FirstVariation.squaredVariationSpeed_calculus g hF hab
  obtain ⟨hK, hdG⟩ := scalar_second_partial_calculus isOpen_Ioo
    (fun z hz => FirstVariation.sliceSquaredSpeed_extension g hF hab hz)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hKc : ContinuousOn (fun t => secondEnergyDensity g F a b 0 t) (Icc a b) :=
    ((hK.comp (continuousOn_const.prodMk continuousOn_id)
      (fun t ht => ⟨h0, ht⟩)).const_mul (1/2 : ℝ))
  refine ⟨hKc, ?_⟩
  have hEder (s : ℝ) (hs : s ∈ Ioo (-ε) ε) :
      HasDerivAt (variedEnergy g F a b)
        ((1/2 : ℝ) * ∫ t in a..b, G (s,t)) s := by
    exact variedEnergy_hasDerivAt_density g hF hab hs
  have hEeq : deriv (variedEnergy g F a b) =ᶠ[𝓝 0]
      (fun s => (1/2 : ℝ) * ∫ t in a..b, G (s,t)) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
    exact (hEder s hs).deriv
  have hd := (hasDerivAt_integral_on_open_strip hab.le h0 hG hK hdG).const_mul (1/2 : ℝ)
  have hd' := hd.congr_of_eventuallyEq hEeq
  convert hd' using 1
  exact intervalIntegral.integral_const_mul _ _

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.MapData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData P202.TorsionMetricData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Totalized chart coefficient of an actual global tangent field. -/
noncomputable def tangentFieldCoefficient (c : TangentIndex S) (Z : Field S)
    (k : Fin n) : M → ℝ :=
  totalize (fun p : (tangentBundle S).baseSet c =>
    (tangentBundle S).fiberCoordinates c p.val p.property (Z.val p.val) k)

/-- The original connection on global fields has the local matrix formula. -/
theorem tangentField_covariant_coordinates
    (C : Connection (tangentBundle S)) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (X Z : Field S) (k : Fin n) :
    (tangentBundle S).fiberCoordinates c p.val p.property ((C.cov X Z).val p.val) k =
      scalarDerivative S (tangentFieldCoefficient c Z k) p.val (X.val p.val) +
        ∑ j : Fin n,
          connectionForm C (SmoothManifolds.ConstantRankBundles.trivializationFrame
            (tangentBundle S) c) p k j (X.val p.val) *
              (tangentBundle S).fiberCoordinates c p.val p.property (Z.val p.val) j := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  let Z' := restrictGlobalSection Z (B.baseSet c) hU
  have hZ : ∀ᶠ q in 𝓝 p.val,
      SmoothManifolds.SectionExtension.totalSection Z'.val q = Z.val q := by
    filter_upwards [hU.mem_nhds p.property] with q hq
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq]
    rfl
  have hpD := ConnectionForms.pointDerivative_congr B C Z.val
    (SmoothManifolds.SectionExtension.totalSection Z'.val) p.val
      ⟨Z, Eventually.of_forall (fun _ => rfl)⟩ (hZ.mono fun _ h => h.symm)
  change pointDerivative C Z.val p.val =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection Z'.val) p.val at hpD
  have h := ConnectionForms.local_frame_formula B C b Z' p (X.val p.val) k
  change (b.basis p).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection Z'.val) p.val (X.val p.val)) k = _ at h
  rw [← hpD, ConnectionForms.pointDerivative_global B C Z p.val X] at h
  rw [LeviCivita.trivializationFrame_coordinates] at h
  convert h using 2
  apply congrArg (fun f => scalarDerivative S f p.val (X.val p.val))
  funext q
  apply congrArg (fun f => totalize f q)
  funext r
  exact (congrFun (LeviCivita.trivializationFrame_coordinates c r (Z.val r.val)) k).symm
  apply Finset.sum_congr rfl
  intro j _
  congr 1

/-- Coordinate-frame representatives identify all Christoffel functions as
actual coefficient germs of the connection on smooth global fields. -/
theorem christoffel_field_coefficient_germ
    (C : Connection (tangentBundle S)) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (X Y : Field S) (i j k : Fin n)
    (hX : ∀ᶠ q in 𝓝 p.val, X.val q = coordinateVector c i q)
    (hY : ∀ᶠ q in 𝓝 p.val, Y.val q = coordinateVector c j q) :
    tangentFieldCoefficient c (C.cov X Y) k =ᶠ[𝓝 p.val]
      totalize (fun q => christoffel C c q k i j) := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  filter_upwards [hU.mem_nhds p.property, hX, hY.eventually_nhds] with q hq hXq hYq
  have hYs : ∀ᶠ r in 𝓝 q,
      Y.val r = SmoothManifolds.SectionExtension.totalSection (b.section_ j) r := by
    filter_upwards [hYq, hU.mem_nhds hq] with r hr hrU
    rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ r hrU,
      LeviCivita.trivializationFrame_section]
    exact hr
  have hpD := ConnectionForms.pointDerivative_congr B C Y.val
    (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) q
      ⟨Y, Eventually.of_forall (fun _ => rfl)⟩ hYs
  change pointDerivative C Y.val q =
    pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) q at hpD
  simp only [tangentFieldCoefficient, totalize_of_mem _ q hq]
  change _ = (b.basis ⟨q,hq⟩).equivFun
    (pointDerivative C (SmoothManifolds.SectionExtension.totalSection (b.section_ j)) q
      (coordinateVector c i q)) k
  rw [← hpD, ← hXq, ConnectionForms.pointDerivative_global B C Y q X,
    LeviCivita.trivializationFrame_coordinates]


private theorem scalarDerivative_eq_of_smooth_germ
    (f g : M → ℝ) (p : M) (hf : VectorSmoothAt S.smoothStructure.val f p)
    (hfg : f =ᶠ[𝓝 p] g) (v : TangentSpace S p) :
    scalarDerivative S f p v = scalarDerivative S g p v := by
  obtain ⟨r, hr, heq⟩ := SmoothManifolds.exists_global_representative S p f
    ((SmoothManifolds.scalarContDiffAt_iff _ _ _ _).mpr hf)
  let r' : GlobalSmooth S := ⟨r, (SmoothManifolds.mem_globalSmoothAlgebra_iff S r).mpr hr⟩
  have hf' : r'.val =ᶠ[𝓝 p] f := heq
  rw [ConnectionForms.scalarDerivative_representative f r' p hf',
    ConnectionForms.scalarDerivative_representative g r' p (hf'.trans hfg)]

theorem tangentFieldCoefficient_smoothAt
    (c : TangentIndex S) (Z : Field S) (k : Fin n)
    (p : (tangentBundle S).baseSet c) :
    VectorSmoothAt S.smoothStructure.val (tangentFieldCoefficient c Z k) p.val := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  let Z' := restrictGlobalSection Z (B.baseSet c) hU
  have hc := (SmoothManifolds.Frames.smooth_section_iff_coefficients B _ hU b Z'.val).mp Z'.property k
  have h := (hc p).totalize hU
  convert h using 1
  funext q
  apply congrArg (fun f => totalize f q)
  funext r
  exact (congrFun (LeviCivita.trivializationFrame_coordinates c r (Z.val r.val)) k).symm

/-- Curvature of the intrinsic connection in any actual coordinate tangent
frame, with the sign fixed by RepresentsCurvature. -/
theorem curvature_coordinate_formula
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (k i j l : Fin n) :
    (tangentBundle S).fiberCoordinates c p.val p.property
      (R.val p.val (coordinateVector c i p.val) (coordinateVector c j p.val)
        (coordinateVector c l p.val)) k =
      scalarDerivative S (totalize (fun q => christoffel C c q k j l)) p.val
        (coordinateVector c i p.val) -
      scalarDerivative S (totalize (fun q => christoffel C c q k i l)) p.val
        (coordinateVector c j p.val) +
      ∑ m : Fin n, (christoffel C c p k i m * christoffel C c p m j l -
        christoffel C c p k j m * christoffel C c p m i l) := by
  classical
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative B b p
  have hec (r : Fin n) : ∀ᶠ q in 𝓝 p.val, (e r).val q = coordinateVector c r q := by
    filter_upwards [he r, hU.mem_nhds p.property] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact LeviCivita.trivializationFrame_section c r ⟨q,hq'⟩
  have heval (r : Fin n) : (e r).val p.val = coordinateVector c r p.val :=
    (hec r).self_of_nhds
  have hcoeff (r s d : Fin n) :=
    christoffel_field_coefficient_germ C c p (e r) (e s) r s d (hec r) (hec s)
  have hcoeffval (r s d : Fin n) :
      B.fiberCoordinates c p.val p.property ((C.cov (e r) (e s)).val p.val) d =
        christoffel C c p d r s := by
    have h := (hcoeff r s d).self_of_nhds
    simpa only [tangentFieldCoefficient, totalize_of_mem _ p.val p.property] using h
  have hdouble (r s d : Fin n) :
      B.fiberCoordinates c p.val p.property ((C.cov (e r) (C.cov (e s) (e l))).val p.val) d =
        scalarDerivative S (totalize (fun q => christoffel C c q d s l)) p.val
          (coordinateVector c r p.val) +
        ∑ m : Fin n, christoffel C c p d r m * christoffel C c p m s l := by
    rw [tangentField_covariant_coordinates C c p (e r) (C.cov (e s) (e l)) d]
    rw [scalarDerivative_eq_of_smooth_germ _ _ p.val
      (tangentFieldCoefficient_smoothAt c (C.cov (e s) (e l)) d p) (hcoeff s l d)]
    rw [heval]
    congr 1
    apply Finset.sum_congr rfl
    intro m _
    rw [hcoeffval]
    rfl
  have hb : (bracket (e i) (e j)).val p.val = 0 :=
    LeviCivita.coordinate_bracket_zero c p.val p.property i j (e i) (e j) (hec i) (hec j)
  have hbr : (C.cov (bracket (e i) (e j)) (e l)).val p.val = 0 := by
    rw [← ConnectionForms.pointDerivative_global B C (e l) p.val (bracket (e i) (e j)), hb, map_zero]
  have hrep := hR (e i) (e j) (e l) p.val
  rw [heval, heval, heval] at hrep
  rw [hrep, CurvatureAlgebra.curvature_apply, hbr]
  simp only [LeviCivita.tangent_sub_as_add, map_add, map_smul, map_zero,
    smul_zero, add_zero, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [hdouble, hdouble, Finset.sum_sub_distrib]
  ring

end P202.Geometry.SecondVariation

namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Joint tangent coordinates of the actual s velocity on the parameter strip. -/
theorem sVelocity_coordinate_germ
    (hF : SmoothVariationOn S F ε a b)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F z ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ 1 x z)
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] x) :
    ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
      ∃ hw : F w ∈ e.source,
        (tangentStructure S).fiberCoordinates.equiv e he (F w) hw
          (velocity S (fun r => F (r,w.2)) w.1) = fderiv ℝ x w (1,0) := by
  have hxc : ContDiffAt ℝ 1 x z := hx
  have hxNear := (hxc.eventually (by simp)).filter_mono
    (nhdsWithin_le_nhds (s := Ioo (-ε) ε ×ˢ Icc a b))
  have heqNear : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
      (fun u => (e (F u)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] w] x :=
    eventually_eventually_nhdsWithin.mpr heq
  filter_upwards [hxNear, heqNear, self_mem_nhdsWithin,
    (hF.1 z hz).eventually (e.open_source.mem_nhds hp)] with w hxs hweq hwD hw
  refine ⟨hw, ?_⟩
  have hi : Tendsto (fun r : ℝ => (r,w.2)) (𝓝 w.1)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] w) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [Ioo_mem_nhds hwD.1.1 hwD.1.2] with r hr
    exact ⟨hr, hwD.2⟩
  have hd : HasDerivAt (fun r => (e (F (r,w.2))).val)
      (fderiv ℝ x w (1,0)) w.1 := by
    apply ((hxs.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).congr_of_eventuallyEq
    exact hweq.comp_tendsto hi
  have hc : ContinuousAt (fun r => F (r,w.2)) w.1 := Filter.Tendsto.comp (hF.1 w hwD) hi
  let L := (tangentStructure S).fiberCoordinates.equiv e he (F w) hw
  have hv : HasVelocityAt S (fun r => F (r,w.2)) w.1 (L.symm (fderiv ℝ x w (1,0))) := by
    refine ⟨hc, e, he, hw, ?_⟩
    change HasDerivAt _ (L (L.symm _)) w.1
    rw [LinearEquiv.apply_symm_apply]
    exact hd
  rw [PiecewiseCurves.velocity_eq hv]
  exact LinearEquiv.apply_symm_apply L _

theorem christoffel_total_smoothAt (C : Connection (tangentBundle S))
    (c : TangentIndex S) (k i j : Fin n) (p : (tangentBundle S).baseSet c) :
    VectorSmoothAt S.smoothStructure.val
      (totalize (fun q => christoffel C c q k i j)) p.val := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  obtain ⟨e,he⟩ := ConnectionForms.local_frame_representative B b p
  have hec (r : Fin n) : ∀ᶠ q in 𝓝 p.val, (e r).val q = coordinateVector c r q := by
    filter_upwards [he r, hU.mem_nhds p.property] with q hq hq'
    rw [hq, SmoothManifolds.SectionExtension.totalSection_of_mem _ q hq']
    exact LeviCivita.trivializationFrame_section c r ⟨q,hq'⟩
  exact (tangentFieldCoefficient_smoothAt c (C.cov (e i) (e j)) k p).congr
    (christoffel_field_coefficient_germ C c p (e i) (e j) i j k (hec i) (hec j))

/-- The canonical endpoint acceleration has the ordinary coordinate expression.
This holds without any condition on the rank of the variation. -/
theorem variationAcceleration_coordinates
    (C : Connection (tangentBundle S)) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) {t : ℝ} (ht : t ∈ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ 2 x (0,t))
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x) :
    let c : TangentIndex S := ⟨e, he⟩
    let hpc : F (0,t) ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (variationAcceleration C F t) =
        fderiv ℝ (fun z => fderiv ℝ x z (1,0)) (0,t) (1,0) +
          (fun k => ∑ j : Fin n, (∑ i : Fin n,
            fderiv ℝ x (0,t) (1,0) i * christoffel C c ⟨F (0,t), hpc⟩ k i j) *
              fderiv ℝ x (0,t) (1,0) j) := by
  dsimp only
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  let c : TangentIndex S := ⟨e, he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hpc : F (0,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  let v : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (1,0)
  let d : Euclidean n := fderiv ℝ v (0,t) (1,0)
  have hvc : ContDiffAt ℝ 1 v (0,t) :=
    (hx.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const
  have hline : Tendsto (fun s : ℝ => (s,t)) (𝓝 0)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact ⟨hs, ht⟩
  have hg := sVelocity_coordinate_germ hF ⟨h0,ht⟩ e he hp x (hx.of_le (by norm_num)) heq
  have hcoeff : coefficientsAlong b' (fun s => F (s,t))
      (fun s => velocity S (fun r => F (r,t)) s) =ᶠ[𝓝 0] (fun s => v (s,t)) := by
    filter_upwards [hline.eventually hg] with s hs
    obtain ⟨hps, hvs⟩ := hs
    have hpcs : F (s,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hps
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcs,
      FirstVariation.tangentFrame_coordinates e he (F (s,t)) hps]
    exact hvs
  have hder : HasDerivAt (coefficientsAlong b' (fun s => F (s,t))
      (fun s => velocity S (fun r => F (r,t)) s)) d 0 := by
    apply ((hvc.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
      ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t))).congr_of_eventuallyEq
    exact hcoeff
  have hV := FirstVariation.variationField_spec hF hε ht
  have hVw : HasVelocityWithinAt S (fun s => F (s,t)) univ 0 (variationField S F t) := by
    obtain ⟨hc, e', he', hp', hd⟩ := hV
    exact ⟨hc.continuousWithinAt, e', he', hp', hd.hasDerivWithinAt⟩
  have hacc : variationAcceleration C F t = frameDerivative C b' (fun s => F (s,t))
      (fun s => velocity S (fun r => F (r,t)) s) 0 hpc (variationField S F t) d :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ 0)
      uniqueDiffWithinAt_univ ⟨_, hVw, _, hU, b', hpc, _, hder.hasDerivWithinAt, rfl⟩
  have hv0 : (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (variationField S F t) = v (0,t) := by
    obtain ⟨hp', hv'⟩ := hg.self_of_nhdsWithin ⟨h0,ht⟩
    exact hv'
  rw [hacc, ← FirstVariation.tangentFrame_coordinates e he (F (0,t)) hp]
  change (b'.basis ⟨F (0,t),hpc⟩).equivFun
      ((b'.basis ⟨F (0,t),hpc⟩).equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rw [hcoeff.self_of_nhds]
  apply congrArg (fun w => d + w)
  funext k
  simp only [Matrix.mulVec, dotProduct, connectionMatrix]
  rw [← FirstVariation.tangentFrame_coordinates e he (F (0,t)) hp,
    LeviCivita.trivializationFrame_coordinates] at hv0
  apply Finset.sum_congr rfl
  intro j _
  have hform := FirstVariation.connectionForm_expansion C c
    ⟨F (0,t),hpc⟩ (variationField S F t) k j
  change connectionForm C b' ⟨F (0,t),hpc⟩ k j (variationField S F t) = _ at hform
  rw [hform]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [hv0]


/-- The moving-endpoint acceleration is C¹ along the whole closed base
segment, including the two endpoints. -/
theorem variationAcceleration_c1
    (C : Connection (tangentBundle S))
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) :
    C1FieldOn (B := tangentBundle S) (fun r => F (0,r))
      (variationAcceleration C F) (Icc a b) := by
  intro t ht
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (0,t) ⟨h0,ht⟩
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hpc : F (0,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  have hgram : ∀ k i j : Fin n, ∃ G : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) G (0,t) ∧
        (fun w => totalize (fun q => christoffel C c q k i j) (F w))
          =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G := by
    intro k i j
    exact FirstVariation.variation_scalar_extension hF ⟨h0,ht⟩ _
      (christoffel_total_smoothAt C c k i j ⟨F (0,t),hpc⟩)
  choose G hGc hGe using hgram
  let v : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (1,0)
  let w : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ v z (1,0)
  have hv : ContDiffAt ℝ (⊤ : ℕ∞) v (0,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hw : ContDiffAt ℝ (⊤ : ℕ∞) w (0,t) :=
    (hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  let A : ℝ × ℝ → Euclidean n := fun z => w z +
    (fun k => ∑ j : Fin n, (∑ i : Fin n, v z i * G k i j z) * v z j)
  have hA : ContDiffAt ℝ 1 A (0,t) := by
    apply (hw.of_le (by simp)).add
    apply contDiffAt_pi.mpr
    intro k
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro i _
      exact ((contDiffAt_pi.mp hv) i).of_le (by simp) |>.mul
        ((hGc k i j).of_le (by simp))
    · exact ((contDiffAt_pi.mp hv) j).of_le (by simp)
  have hline : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have heqNear : ∀ᶠ r in 𝓝[Icc a b] t,
      (fun u => (e (F u)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)] x :=
    hline.eventually (eventually_eventually_nhdsWithin.mpr heq)
  have hx2 : ContDiffAt ℝ 2 x (0,t) := hx.of_le (by simp)
  have hxNear : ∀ᶠ r in 𝓝[Icc a b] t, ContDiffAt ℝ 2 x (0,r) :=
    hline.eventually ((hx2.eventually (by norm_num)).filter_mono nhdsWithin_le_nhds)
  have hGall : ∀ᶠ r in 𝓝[Icc a b] t, ∀ k i j : Fin n,
      totalize (fun q => christoffel C c q k i j) (F (0,r)) = G k i j (0,r) :=
    hline.eventually (Filter.eventually_all.mpr fun k =>
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hGe k i))
  have hcoeff : coefficientsAlong b' (fun r => F (0,r)) (variationAcceleration C F)
      =ᶠ[𝓝[Icc a b] t] (fun r => A (0,r)) := by
    filter_upwards [heqNear, hxNear, hGall,
      (FirstVariation.variation_continuousOn_slice hF h0 t ht).eventually (e.open_source.mem_nhds hp),
      self_mem_nhdsWithin] with r hr hxr hGr hpr hrJ
    have hpcs : F (0,r) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcs,
      FirstVariation.tangentFrame_coordinates e he (F (0,r)) hpr,
      variationAcceleration_coordinates C hF hε hrJ e he hpr x hxr hr]
    change w (0,r) + _ = w (0,r) + _
    congr 1
    funext k
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    exact (totalize_of_mem (fun q => christoffel C c q k i j) (F (0,r)) hpcs).symm.trans (hGr k i j)
  refine ⟨_, hU, b', hpc, (fun r => A (0,r)), ?_, hcoeff.self_of_nhdsWithin ht, hcoeff⟩
  exact hA.comp t (contDiffAt_const.prodMk contDiffAt_id)

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Continuous scalar combinations of finitely many globally smooth fields,
locally along a parameter set. This is an auxiliary description of a field germ. -/
def ContinuousFieldGerm {γ : ℝ → M} (f : (t : ℝ) → TangentSpace S (γ t))
    (J : Set ℝ) (t : ℝ) : Prop :=
  ∃ (ι : Type) (_ : Fintype ι) (e : ι → Field S) (v : ι → ℝ → ℝ),
    (∀ i, ContinuousAt (v i) t) ∧
    ∀ᶠ s in 𝓝[J] t, f s = ∑ i, v i s • (e i).val (γ s)

theorem c1Field_local_expansion {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hγc : ContinuousOn γ J) (ht : t ∈ J)
    {f : (t : ℝ) → TangentSpace S (γ t)}
    (hf : C1FieldOn (B := tangentBundle S) γ f J) :
    ∃ (e : Fin n → Field S) (v : ℝ → Euclidean n), ContDiffAt ℝ 1 v t ∧
      ∀ᶠ s in 𝓝[J] t, f s = ∑ i, v s i • (e i).val (γ s) := by
  classical
  obtain ⟨U, hU, b, hp, v, hv, _, heq⟩ := hf t ht
  obtain ⟨e, he⟩ := ConnectionForms.local_frame_representative (tangentBundle S) b ⟨γ t, hp⟩
  refine ⟨e, v, hv, ?_⟩
  have heNear : ∀ᶠ s in 𝓝[J] t, ∀ i : Fin n,
      (e i).val (γ s) = SmoothManifolds.SectionExtension.totalSection (b.section_ i) (γ s) :=
    (hγc t ht).eventually (Filter.eventually_all.mpr he)
  filter_upwards [heq, heNear, (hγc t ht).eventually (hU.mem_nhds hp)] with s hs heS hsU
  have hb := (b.basis ⟨γ s, hsU⟩).sum_equivFun (f s)
  rw [← hs, CurveCovariantDerivative.coefficientsAlong_of_mem b γ f s hsU]
  convert hb.symm using 1
  apply Finset.sum_congr rfl
  intro i _
  rw [heS i, SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hsU, ← b.basis_eq]

theorem c1Field_continuousFieldGerm {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (hγc : ContinuousOn γ J) (ht : t ∈ J)
    {f : (t : ℝ) → TangentSpace S (γ t)}
    (hf : C1FieldOn (B := tangentBundle S) γ f J) : ContinuousFieldGerm f J t := by
  obtain ⟨e,v,hv,heq⟩ := c1Field_local_expansion hγc ht hf
  exact ⟨Fin n, inferInstance, e, (fun i s => v s i),
    fun i => (contDiffAt_pi.mp hv i).continuousAt, heq⟩

theorem continuousFieldGerm_metric_pairing {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (g : RiemannianMetric S) (hγ : CoordinateC1On S γ J)
    (hγc : ContinuousOn γ J) (ht : t ∈ J)
    {f h : (t : ℝ) → TangentSpace S (γ t)}
    (hf : ContinuousFieldGerm f J t) (hh : ContinuousFieldGerm h J t) :
    ContinuousWithinAt (fun s => pairing g (γ s) (f s) (h s)) J t := by
  classical
  obtain ⟨ι, hι, e, v, hv, hef⟩ := hf
  obtain ⟨κ, hκ, d, w, hw, heh⟩ := hh
  letI := hι
  letI := hκ
  have hgram (i : ι) (j : κ) : ContinuousWithinAt
      (fun s => pairing g (γ s) ((e i).val (γ s)) ((d j).val (γ s))) J t := by
    obtain ⟨y,hy,heq⟩ := FirstVariation.scalar_c1_extension hγ hγc ht
      (TorsionAndMetric.metricPairing_smooth (tangentBundle S) g (e i) (d j) (γ t))
    exact hy.continuousAt.continuousWithinAt.congr_of_eventuallyEq_of_mem heq ht
  have hc : ContinuousWithinAt (fun s => ∑ i, ∑ j,
      v i s * (w j s * pairing g (γ s) ((e i).val (γ s)) ((d j).val (γ s)))) J t := by
    apply tendsto_finsetSum
    intro i _
    apply tendsto_finsetSum
    intro j _
    exact (hv i).continuousWithinAt.mul ((hw j).continuousWithinAt.mul (hgram i j))
  apply hc.congr_of_eventuallyEq_of_mem _ ht
  filter_upwards [hef,heh] with s hfs hhs
  rw [hfs,hhs]
  simp only [pairing, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring


theorem ContinuousFieldGerm.smoothSection {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (e : Field S) : ContinuousFieldGerm (fun s => e.val (γ s)) J t := by
  classical
  refine ⟨Unit, inferInstance, fun _ => e, fun _ _ => 1,
    fun _ => continuousAt_const, ?_⟩
  exact Filter.Eventually.of_forall (fun _ => by simp)

theorem ContinuousFieldGerm.smul {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    {f : (s : ℝ) → TangentSpace S (γ s)} {a : ℝ → ℝ}
    (ha : ContinuousAt a t) (hf : ContinuousFieldGerm f J t) :
    ContinuousFieldGerm (fun s => a s • f s) J t := by
  classical
  obtain ⟨ι,hι,e,v,hv,heq⟩ := hf
  letI := hι
  refine ⟨ι,hι,e,fun i s => a s * v i s,fun i => ha.mul (hv i),?_⟩
  filter_upwards [heq] with s hs
  simp only [hs, Finset.smul_sum, mul_smul]

theorem ContinuousFieldGerm.add {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    {f h : (s : ℝ) → TangentSpace S (γ s)}
    (hf : ContinuousFieldGerm f J t) (hh : ContinuousFieldGerm h J t) :
    ContinuousFieldGerm (fun s => f s + h s) J t := by
  classical
  obtain ⟨ι,hι,e,v,hv,hef⟩ := hf
  obtain ⟨κ,hκ,d,w,hw,heh⟩ := hh
  letI := hι
  letI := hκ
  refine ⟨ι ⊕ κ, inferInstance, Sum.elim e d,
    Sum.elim v w, (by intro i; cases i <;> simp_all), ?_⟩
  filter_upwards [hef,heh] with s hs ht
  simp only [hs,ht,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr]

theorem ContinuousFieldGerm.zero {γ : ℝ → M} {J : Set ℝ} {t : ℝ} :
    ContinuousFieldGerm (fun s => (0 : TangentSpace S (γ s))) J t := by
  simpa only [zero_smul] using
    (ContinuousFieldGerm.smoothSection (γ := γ) (J := J) (t := t) (0 : Field S)).smul
      (a := fun _ => (0 : ℝ)) continuousAt_const

theorem ContinuousFieldGerm.sum {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    {ι : Type} (I : Finset ι) {f : ι → (s : ℝ) → TangentSpace S (γ s)}
    (hf : ∀ i ∈ I, ContinuousFieldGerm (f i) J t) :
    ContinuousFieldGerm (fun s => ∑ i ∈ I, f i s) J t := by
  classical
  induction I using Finset.induction_on with
  | empty => simpa using (ContinuousFieldGerm.zero (γ := γ) (J := J) (t := t))
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      (hf i (Finset.mem_insert_self i I)).add
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem derivative_congr_field {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (C : Connection (tangentBundle S)) (ht : t ∈ J)
    {f h : (s : ℝ) → TangentSpace S (γ s)} {D : TangentSpace S (γ t)}
    (hD : HasCovariantDerivativeWithinAt C γ f J t D)
    (heq : ∀ᶠ s in 𝓝[J] t, h s = f s) : HasCovariantDerivativeWithinAt C γ h J t D := by
  classical
  obtain ⟨T,hT,U,hU,b,hp,v,hv,hDeq⟩ := hD
  have hcoef : coefficientsAlong b γ h =ᶠ[𝓝[J] t] coefficientsAlong b γ f := by
    filter_upwards [heq] with s hs
    simp only [coefficientsAlong,hs]
  refine ⟨T,hT,U,hU,b,hp,v,hv.congr_of_eventuallyEq_of_mem hcoef ht,?_⟩
  simpa only [frameDerivative, hcoef.self_of_nhdsWithin ht] using hDeq

theorem derivative_finset_sum {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (C : Connection (tangentBundle S)) (ht : t ∈ J)
    (hJ : UniqueDiffWithinAt ℝ J t)
    {T : TangentSpace S (γ t)} (hT : HasVelocityWithinAt S γ J t T)
    {ι : Type} (I : Finset ι) {f : ι → (s : ℝ) → TangentSpace S (γ s)}
    {D : ι → TangentSpace S (γ t)}
    (hf : ∀ i ∈ I, HasCovariantDerivativeWithinAt C γ (f i) J t (D i)) :
    HasCovariantDerivativeWithinAt C γ (fun s => ∑ i ∈ I, f i s) J t
      (∑ i ∈ I, D i) := by
  classical
  induction I using Finset.induction_on with
  | empty =>
    obtain ⟨X,hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (γ t) T
    have hz := CurveCovariantDerivative.derivative_section_field (c := γ) C (0 : Field S) X ht
      (by simpa only [hX] using hT)
    simpa only [Finset.sum_empty, map_zero, ConnectionForms.section_zero_apply] using hz
  | @insert i I hi ih =>
    simpa only [Finset.sum_insert hi] using
      CurveCovariantDerivative.derivative_add C ht hJ
        (hf i (Finset.mem_insert_self i I))
        (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

theorem covariantDerivativeWithin_continuousFieldGerm
    {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (C : Connection (tangentBundle S)) (hJ : UniqueDiffOn ℝ J)
    (hγc : ContinuousOn γ J) (ht : t ∈ J)
    {T f : (s : ℝ) → TangentSpace S (γ s)}
    (hT : ∀ s ∈ J, HasVelocityWithinAt S γ J s (T s))
    (hTC : C1FieldOn (B := tangentBundle S) γ T J)
    (hf : C1FieldOn (B := tangentBundle S) γ f J) :
    ContinuousFieldGerm (covariantDerivativeWithin C γ f J) J t := by
  classical
  obtain ⟨e,v,hv,hev⟩ := c1Field_local_expansion hγc ht hf
  obtain ⟨X,w,hw,hew⟩ := c1Field_local_expansion hγc ht hTC
  let G : (s : ℝ) → TangentSpace S (γ s) := fun s => ∑ i : Fin n,
    (deriv (fun r => v r i) s • (e i).val (γ s) +
      v s i • (∑ j : Fin n, w s j • (C.cov (X j) (e i)).val (γ s)))
  have hG : ContinuousFieldGerm G J t := by
    unfold G
    apply ContinuousFieldGerm.sum
    intro i _
    apply ContinuousFieldGerm.add
    · exact (ContinuousFieldGerm.smoothSection (e i)).smul
        ((contDiffAt_pi.mp hv i).derivWithin (m := 0) (by norm_num)).continuousAt
    · apply ContinuousFieldGerm.smul (contDiffAt_pi.mp hv i).continuousAt
      apply ContinuousFieldGerm.sum
      intro j _
      exact (ContinuousFieldGerm.smoothSection (C.cov (X j) (e i))).smul
        (contDiffAt_pi.mp hw j).continuousAt
  obtain ⟨ι,hι,d,c,hc,heG⟩ := hG
  refine ⟨ι,hι,d,c,hc,?_⟩
  have hcongr : ∀ᶠ s in 𝓝[J] t, covariantDerivativeWithin C γ f J s = G s := by
    have hvNear : ∀ᶠ s in 𝓝[J] t, ContDiffAt ℝ 1 v s :=
      (hv.eventually (by simp)).filter_mono nhdsWithin_le_nhds
    have hevNear := eventually_eventually_nhdsWithin.mpr hev
    filter_upwards [hvNear,hevNear,hew,self_mem_nhdsWithin] with s hvs hevs hews hsJ
    apply CurveCovariantDerivative.covariantDerivativeWithin_eq C hsJ (hJ s hsJ)
    apply derivative_congr_field C hsJ (f := fun r => ∑ i : Fin n, v r i • (e i).val (γ r))
        (heq := hevs)
    change HasCovariantDerivativeWithinAt C γ _ J s (∑ i : Fin n,
      (deriv (fun r => v r i) s • (e i).val (γ s) +
        v s i • (∑ j : Fin n, w s j • (C.cov (X j) (e i)).val (γ s))))
    apply derivative_finset_sum C hsJ (hJ s hsJ) (hT s hsJ)
    intro i _
    have hd := CurveCovariantDerivative.derivative_smul C
      (CurveCovariantDerivative.derivative_section C (e i) hsJ (hT s hsJ))
      ((contDiffAt_pi.mp hvs i).differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt
    have hp : pointDerivative C (e i).val (γ s) (T s) =
        ∑ j : Fin n, w s j • (C.cov (X j) (e i)).val (γ s) := by
      rw [hews, map_sum]
      simp only [map_smul, ConnectionForms.pointDerivative_global]
    simpa only [G,hp] using hd


  filter_upwards [hcongr,heG] with s hs hgs
  exact hs.trans hgs

theorem ContinuousFieldGerm.curvature {γ : ℝ → M} {J : Set ℝ} {t : ℝ}
    (R : CurvatureTensor S)
    {f h k : (s : ℝ) → TangentSpace S (γ s)}
    (hf : ContinuousFieldGerm f J t) (hh : ContinuousFieldGerm h J t)
    (hk : ContinuousFieldGerm k J t) :
    ContinuousFieldGerm (fun s => R.val (γ s) (f s) (h s) (k s)) J t := by
  classical
  obtain ⟨ι,hι,e,v,hv,hef⟩ := hf
  obtain ⟨κ,hκ,d,w,hw,heh⟩ := hh
  obtain ⟨μ,hμ,c,z,hz,hek⟩ := hk
  letI := hι
  letI := hκ
  letI := hμ
  refine ⟨μ × κ × ι,inferInstance,
    (fun i => ⟨fun p => R.val p ((e i.2.2).val p) ((d i.2.1).val p)
        ((c i.1).val p), R.smooth (e i.2.2) (d i.2.1) (c i.1)⟩),
    (fun i s => z i.1 s * (w i.2.1 s * v i.2.2 s)),
    (fun i => (hz i.1).mul ((hw i.2.1).mul (hv i.2.2))), ?_⟩
  filter_upwards [hef,heh,hek] with s hfs hhs hks
  rw [hfs,hhs,hks]
  simp only [map_sum,LinearMap.sum_apply,map_smul,LinearMap.smul_apply,
    Fintype.sum_prod_type,Finset.smul_sum,smul_smul]

theorem indexIntegrand_continuousOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : CoordinateC1On S γ (Icc a b)) (hγc : ContinuousOn γ (Icc a b))
    (hT : ∀ t ∈ Icc a b, HasVelocityWithinAt S γ (Icc a b) t (segmentTangent S γ a b t))
    (hTC : C1FieldOn (B := tangentBundle S) γ (segmentTangent S γ a b) (Icc a b))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b))
    (hW : C1FieldOn (B := tangentBundle S) γ W (Icc a b)) :
    ContinuousOn (indexIntegrand g C R γ a b V W) (Icc a b) := by
  intro t ht
  have hdV := covariantDerivativeWithin_continuousFieldGerm C (uniqueDiffOn_Icc hab)
    hγc ht hT hTC hV
  have hdW := covariantDerivativeWithin_continuousFieldGerm C (uniqueDiffOn_Icc hab)
    hγc ht hT hTC hW
  have hVC := c1Field_continuousFieldGerm hγc ht hV
  have hWC := c1Field_continuousFieldGerm hγc ht hW
  have hTC' := c1Field_continuousFieldGerm hγc ht hTC
  exact (continuousFieldGerm_metric_pairing g hγ hγc ht hdV hdW).sub
    (continuousFieldGerm_metric_pairing g hγ hγc ht
      (hVC.curvature R hTC' hTC') hWC)

theorem indexIntegrand_intervalIntegrable
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hF : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : C1FieldOn (B := tangentBundle S) γ V (Icc a b))
    (hW : C1FieldOn (B := tangentBundle S) γ W (Icc a b)) :
    IntervalIntegrable (indexIntegrand g C R γ a b V W) volume a b := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  apply ContinuousOn.intervalIntegrable_of_Icc hab.le
  apply indexIntegrand_continuousOn g C R hab
    (FirstVariation.variation_coordinateC1On_slice hF h0)
    (FirstVariation.variation_continuousOn_slice hF h0) _ _ hV hW
  · intro t ht
    exact FirstVariation.segmentVelocity_spec hF (by norm_num) ht
  · exact FirstVariation.segmentVelocity_c1 hF (by norm_num) hab

end P202.Geometry.SecondVariation

namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

/-- Once the smooth second-variation formula is proved, fixed finite
partitions require no additional geometric identity. -/
theorem piecewise_second_variation_from_smooth_formula
    (h : P202Specs.Geometry.SecondVariation.second_variation_energyType.{u}) :
    P202Specs.Geometry.SecondVariation.piecewise_second_variation_energyType.{u} := by
  intro n M _ S g C hC R hR F ε hε k node hnode hF hgeo
  have hlt (i : Fin (k+1)) : node i.castSucc < node i.succ :=
    hnode (Fin.castSucc_lt_succ (i := i))
  have hleft (i : Fin (k+1)) : node 0 ≤ node i.castSucc :=
    hnode.monotone (Fin.zero_le _)
  have hright (i : Fin (k+1)) : node i.succ ≤ node (Fin.last (k+1)) :=
    hnode.monotone (Fin.le_last _)
  have hV (i : Fin (k+1)) : C1FieldOn (B := tangentBundle S) (fun t => F (0,t))
      (variationField S F) (Icc (node i.castSucc) (node i.succ)) :=
    FirstVariation.variationField_c1 (hF.2 i) hε
  have hint (i : Fin (k+1)) : IntervalIntegrable
      (indexIntegrand g C R (fun t => F (0,t)) (node i.castSucc) (node i.succ)
        (variationField S F) (variationField S F)) volume
      (node i.castSucc) (node i.succ) :=
    indexIntegrand_intervalIntegrable g C R (hlt i)
      (smoothVariationOn_mono_interval hgeo.1 (hleft i) (hright i)) (hV i) (hV i)
  have hd := variedEnergy_second_subdivision g hε node hnode.monotone hF.2
    (fun s hs i => (variedEnergy_hasDerivAt_density g (hF.2 i) (hlt i) hs).differentiableAt)
    (fun i => h g C hC R hR F ε (node i.castSucc) (node i.succ) hε (hlt i) (hF.2 i)
      (affineGeodesicSegment_restrict C hgeo (hleft i) (hright i) (hlt i)))
  rw [Finset.sum_add_distrib,
    ← indexForm_subdivision_of_integrable g C R node hnode hgeo.1 hV hV hint,
    accelerationBoundary_subdivision g C F node hnode hgeo.1] at hd
  exact hd

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u

/-- Twice differentiability follows from the original strip smoothness.
No second-derivative existence assumption is required. -/
theorem variedEnergy_twice_differentiable
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) :
    DifferentiableAt ℝ (deriv (variedEnergy g F a b)) 0 :=
  (variedEnergy_second_density_calculus g hF hε hab).2.differentiableAt

/-- The same actual twice differentiability holds across fixed finite
breaks, without geodesicity of the central curve. -/
theorem piecewise_variedEnergy_twice_differentiable
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    {F : ℝ × ℝ → M} {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hF : PiecewiseSmoothVariationOn S F ε node) :
    DifferentiableAt ℝ
      (deriv (variedEnergy g F (node 0) (node (Fin.last (k+1))))) 0 := by
  have hlt (i : Fin (k+1)) : node i.castSucc < node i.succ :=
    hnode (Fin.castSucc_lt_succ (i := i))
  exact (variedEnergy_second_subdivision g hε node hnode.monotone hF.2
    (fun s hs i => (variedEnergy_hasDerivAt_density g (hF.2 i) (hlt i) hs).differentiableAt)
    (fun i => (variedEnergy_second_density_calculus g (hF.2 i) hε (hlt i)).2)).differentiableAt

/-- All analytic and acceleration regularity steps reduce the smooth theorem
to the pointwise geometric density identity. The final theorem below
establishes this identity by intrinsic curvature commutation. -/
theorem secondVariation_of_pointwise_density
    {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsMetricCompatible g C)
    (R : CurvatureTensor S) {F : ℝ × ℝ → M} {ε a b : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hgeo : IsAffineGeodesicSegment C (fun t => F (0,t)) a b)
    (hId : ∀ t ∈ Icc a b, secondEnergyDensity g F a b 0 t =
      indexIntegrand g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) t +
      pairing g (F (0,t))
        (covariantDerivativeWithin C (fun t => F (0,t)) (variationAcceleration C F) (Icc a b) t)
        (segmentVelocity S F a b t)) :
    HasDerivAt (deriv (variedEnergy g F a b))
      (indexForm g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) +
        accelerationBoundary g C F a b) 0 := by
  obtain ⟨hc,hd⟩ := variedEnergy_second_density_calculus g hF hε hab
  exact secondVariation_of_geodesic_density g C hC R F hab hgeo
    (variationAcceleration_c1 C hF hε) hc hd hId

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
open private sum_integrals from MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthLaws
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem indexIntegrand_add_left_of_derivatives
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hJ : UniqueDiffWithinAt ℝ (Icc a b) t)
    {V U W : (s : ℝ) → TangentSpace S (γ s)}
    {DV DU : TangentSpace S (γ t)}
    (hV : HasCovariantDerivativeWithinAt C γ V (Icc a b) t DV)
    (hU : HasCovariantDerivativeWithinAt C γ U (Icc a b) t DU) :
    indexIntegrand g C R γ a b (fun s => V s + U s) W t =
      indexIntegrand g C R γ a b V W t + indexIntegrand g C R γ a b U W t := by
  have hadd := CurveCovariantDerivative.covariantDerivativeWithin_add C ht hJ hV hU
  simp only [indexIntegrand, hadd, map_add, LinearMap.add_apply]
  ring

theorem indexIntegrand_add_right_of_derivatives
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hJ : UniqueDiffWithinAt ℝ (Icc a b) t)
    {V U W : (s : ℝ) → TangentSpace S (γ s)}
    {DU DW : TangentSpace S (γ t)}
    (hU : HasCovariantDerivativeWithinAt C γ U (Icc a b) t DU)
    (hW : HasCovariantDerivativeWithinAt C γ W (Icc a b) t DW) :
    indexIntegrand g C R γ a b V (fun s => U s + W s) t =
      indexIntegrand g C R γ a b V U t + indexIntegrand g C R γ a b V W t := by
  have hadd := CurveCovariantDerivative.covariantDerivativeWithin_add C ht hJ hU hW
  simp only [indexIntegrand, hadd, map_add, LinearMap.add_apply]
  ring

theorem indexIntegrand_smul_left_of_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hJ : UniqueDiffWithinAt ℝ (Icc a b) t)
    {V W : (s : ℝ) → TangentSpace S (γ s)} {DV : TangentSpace S (γ t)}
    (hV : HasCovariantDerivativeWithinAt C γ V (Icc a b) t DV) (c : ℝ) :
    indexIntegrand g C R γ a b (fun s => c • V s) W t =
      c * indexIntegrand g C R γ a b V W t := by
  have hsmul := CurveCovariantDerivative.covariantDerivativeWithin_smul C ht hJ hV
    (hasDerivWithinAt_const t (Icc a b) c)
  simp only [zero_smul, zero_add] at hsmul
  simp only [indexIntegrand, hsmul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring

theorem indexIntegrand_smul_right_of_derivative
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b t : ℝ} (ht : t ∈ Icc a b)
    (hJ : UniqueDiffWithinAt ℝ (Icc a b) t)
    {V W : (s : ℝ) → TangentSpace S (γ s)} {DW : TangentSpace S (γ t)}
    (hW : HasCovariantDerivativeWithinAt C γ W (Icc a b) t DW) (c : ℝ) :
    indexIntegrand g C R γ a b V (fun s => c • W s) t =
      c * indexIntegrand g C R γ a b V W t := by
  have hsmul := CurveCovariantDerivative.covariantDerivativeWithin_smul C ht hJ hW
    (hasDerivWithinAt_const t (Icc a b) c)
  simp only [zero_smul, zero_add] at hsmul
  simp only [indexIntegrand, hsmul, map_smul, LinearMap.smul_apply, smul_eq_mul]
  ring


theorem indexIntegrand_piecewise_intervalIntegrable
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 (node 0) (node (Fin.last (k+1))))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ)))
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ))) :
    IntervalIntegrable
      (indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W) volume
      (node 0) (node (Fin.last (k+1))) := by
  apply PiecewiseCurves.intervalIntegrable_of_partition node
  intro i
  have hlt : node i.castSucc < node i.succ := hnode (Fin.castSucc_lt_succ (i := i))
  have hleft : node 0 ≤ node i.castSucc := hnode.monotone (Fin.zero_le _)
  have hright : node i.succ ≤ node (Fin.last (k+1)) := hnode.monotone (Fin.le_last _)
  have hi := indexIntegrand_intervalIntegrable g C R hlt
    (smoothVariationOn_mono_interval hγ hleft hright) (hV i) (hW i)
  apply hi.congr_uIoo
  rw [uIoo_of_le hlt.le]
  intro t ht
  exact (indexIntegrand_restrict g C R hγ hleft hright hlt (hV i) (hW i) ht).symm

theorem piecewise_exists_covariantDerivative
    (C : Connection (tangentBundle S))
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 (node 0) (node (Fin.last (k+1))))
    {V : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ)))
    {t : ℝ} (ht : t ∈ Ioo (node 0) (node (Fin.last (k+1))))
    (hne : ∀ i, t ≠ node i) :
    ∃ D, HasCovariantDerivativeWithinAt C γ V
      (Icc (node 0) (node (Fin.last (k+1)))) t D := by
  obtain ⟨i,hi⟩ := PiecewiseCurves.exists_piece_between_nodes node ht.1 ht.2 hne
  have hlt : node i.castSucc < node i.succ := hnode (Fin.castSucc_lt_succ (i := i))
  have hsmall := smoothVariationOn_mono_interval hγ
    (hnode.monotone (Fin.zero_le i.castSucc)) (hnode.monotone (Fin.le_last i.succ))
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨D,hD⟩ := CurveCovariantDerivative.exists_covariantDerivative C
    (Ioo_subset_Icc_self hi) (FirstVariation.variation_coordinateC1On_slice hsmall h0)
    (FirstVariation.variation_continuousOn_slice hsmall h0) (hV i)
  exact ⟨D,hasCovariantDerivativeWithinAt_of_mem_nhds C hD (Icc_mem_nhds hi.1 hi.2)⟩

theorem indexForm_bilinear : P202Specs.Geometry.SecondVariation.indexForm_bilinearType.{u} := by
  intro n M _ S g C R γ a b hab hγ k node hnode ha hb V U W hV hU hW
  subst a
  subst b
  classical
  let N : Finset ℝ := Finset.univ.image node
  have hnodes {t : ℝ} (hne : t ∉ N) : ∀ i, t ≠ node i := by
    intro i heq
    apply hne
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ i,heq.symm⟩
  have hmem {t : ℝ} (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1))))
      (hne : t ∉ N) : t ∈ Ioo (node 0) (node (Fin.last (k+1))) := by
    rw [uIoc_of_le hab.le] at ht
    exact ⟨ht.1,lt_of_le_of_ne ht.2 (hnodes hne _)⟩
  have hintVW := indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hV hW
  have hintUW := indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hU hW
  have hintVU := indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hV hU
  have hleft (t : ℝ)
      (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1)))) (hne : t ∉ N) :
      indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) (fun t => V t + U t) W t =
        indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W t +
        indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) U W t := by
    obtain ⟨DV,hDV⟩ := piecewise_exists_covariantDerivative C node hnode hγ hV (hmem ht hne) (hnodes hne)
    obtain ⟨DU,hDU⟩ := piecewise_exists_covariantDerivative C node hnode hγ hU (hmem ht hne) (hnodes hne)
    exact indexIntegrand_add_left_of_derivatives g C R (Ioo_subset_Icc_self (hmem ht hne))
      (uniqueDiffOn_Icc hab t (Ioo_subset_Icc_self (hmem ht hne))) hDV hDU
  have hright (t : ℝ)
      (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1)))) (hne : t ∉ N) :
      indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V (fun t => U t + W t) t =
        indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V U t +
        indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W t := by
    obtain ⟨DU,hDU⟩ := piecewise_exists_covariantDerivative C node hnode hγ hU (hmem ht hne) (hnodes hne)
    obtain ⟨DW,hDW⟩ := piecewise_exists_covariantDerivative C node hnode hγ hW (hmem ht hne) (hnodes hne)
    exact indexIntegrand_add_right_of_derivatives g C R (Ioo_subset_Icc_self (hmem ht hne))
      (uniqueDiffOn_Icc hab t (Ioo_subset_Icc_self (hmem ht hne))) hDU hDW
  have hsmulLeft (c t : ℝ)
      (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1)))) (hne : t ∉ N) :
      indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) (fun t => c • V t) W t =
        c * indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W t := by
    obtain ⟨DV,hDV⟩ := piecewise_exists_covariantDerivative C node hnode hγ hV (hmem ht hne) (hnodes hne)
    exact indexIntegrand_smul_left_of_derivative g C R (Ioo_subset_Icc_self (hmem ht hne))
      (uniqueDiffOn_Icc hab t (Ioo_subset_Icc_self (hmem ht hne))) hDV c
  have hsmulRight (c t : ℝ)
      (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1)))) (hne : t ∉ N) :
      indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V (fun t => c • W t) t =
        c * indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W t := by
    obtain ⟨DW,hDW⟩ := piecewise_exists_covariantDerivative C node hnode hγ hW (hmem ht hne) (hnodes hne)
    exact indexIntegrand_smul_right_of_derivative g C R (Ioo_subset_Icc_self (hmem ht hne))
      (uniqueDiffOn_Icc hab t (Ioo_subset_Icc_self (hmem ht hne))) hDW c
  refine ⟨?_,?_,?_⟩
  · unfold P202.SecondVariationData.indexForm
    rw [PiecewiseCurves.integral_eq_of_eqOn_off_finite N hleft]
    exact intervalIntegral.integral_add hintVW hintUW
  · unfold P202.SecondVariationData.indexForm
    rw [PiecewiseCurves.integral_eq_of_eqOn_off_finite N hright]
    exact intervalIntegral.integral_add hintVU hintVW
  · intro c
    constructor
    · unfold P202.SecondVariationData.indexForm
      rw [PiecewiseCurves.integral_eq_of_eqOn_off_finite N (hsmulLeft c)]
      exact intervalIntegral.integral_const_mul c _
    · unfold P202.SecondVariationData.indexForm
      rw [PiecewiseCurves.integral_eq_of_eqOn_off_finite N (hsmulRight c)]
      exact intervalIntegral.integral_const_mul c _

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem curve_covariantDerivative_coordinates
    (C : Connection (tangentBundle S)) (c : TangentIndex S)
    {γ : ℝ → M} {V : (t : ℝ) → TangentSpace S (γ t)}
    {J : Set ℝ} {t : ℝ} (ht : t ∈ J) (hJ : UniqueDiffWithinAt ℝ J t)
    (hp : γ t ∈ c.val.source)
    {T : TangentSpace S (γ t)} (hT : HasVelocityWithinAt S γ J t T)
    {v' : Euclidean n}
    (hv : HasDerivWithinAt (coefficientsAlong
      (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c) γ V) v' J t) :
    (tangentStructure S).fiberCoordinates.equiv c.val c.property (γ t) hp
      (covariantDerivativeWithin C γ V J t) =
    v' + fun k => ∑ j : Fin n,
      (∑ i : Fin n, ((tangentStructure S).fiberCoordinates.equiv c.val c.property (γ t) hp T) i *
        christoffel C c ⟨γ t, (tangentRealization S).baseSet c ▸ hp⟩ k i j) *
      coefficientsAlong (SmoothManifolds.ConstantRankBundles.trivializationFrame
        (tangentBundle S) c) γ V t j := by
  let B := tangentBundle S
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hpc : γ t ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  have hD : covariantDerivativeWithin C γ V J t = frameDerivative C b γ V t hpc T v' :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C ht hJ
      ⟨T, hT, _, hU, b, hpc, v', hv, rfl⟩
  rw [hD, ← FirstVariation.tangentFrame_coordinates c.val c.property (γ t) hp]
  change (b.basis ⟨γ t,hpc⟩).equivFun ((b.basis ⟨γ t,hpc⟩).equivFun.symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  congr 1
  funext k
  simp only [Matrix.mulVec, dotProduct, connectionMatrix]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  have hform := FirstVariation.connectionForm_expansion C c ⟨γ t,hpc⟩ T k j
  change connectionForm C b ⟨γ t,hpc⟩ k j T = _ at hform
  rw [hform]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← FirstVariation.tangentFrame_coordinates c.val c.property (γ t) hp,
    LeviCivita.trivializationFrame_coordinates]

end P202.Geometry.SecondVariation





namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Each variation-parameter trace is C¹ on its full open parameter interval. -/
theorem variation_coordinateC1On_sTrace
    (hF : SmoothVariationOn S F ε a b) {t : ℝ} (ht : t ∈ Icc a b) :
    CoordinateC1On S (fun s => F (s,t)) (Ioo (-ε) ε) := by
  intro s hs
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hF.2 (s,t) ⟨hs,ht⟩
  refine ⟨e, he, hp, (fun r => x (r,t)), ?_, hxt, ?_⟩
  · exact (hx.comp s (contDiffAt_id.prodMk contDiffAt_const)).of_le (by simp)
  · exact heq.comp_tendsto
      (((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
        (fun _ hr => ⟨hr,ht⟩))

theorem variation_continuousOn_sTrace
    (hF : SmoothVariationOn S F ε a b) {t : ℝ} (ht : t ∈ Icc a b) :
    ContinuousOn (fun s => F (s,t)) (Ioo (-ε) ε) :=
  hF.1.comp (continuousOn_id.prodMk continuousOn_const) (fun _ hs => ⟨hs,ht⟩)

/-- The actual s-covariant derivative of the slice tangent, with the original
open parameter interval as its differentiation set. -/
noncomputable def sliceVelocitySDerivative
    (C : Connection (tangentBundle S)) (F : ℝ × ℝ → M)
    (ε a b s t : ℝ) : TangentSpace S (F (s,t)) :=
  covariantDerivativeWithin C (fun r => F (r,t))
    (fun r => FirstVariation.sliceVelocity S F a b r t) (Ioo (-ε) ε) s

/-- The slice tangent is C¹ as a field along each variation-parameter trace. -/
theorem sliceVelocity_s_c1
    (hF : SmoothVariationOn S F ε a b) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    C1FieldOn (B := tangentBundle S) (fun s => F (s,t))
      (fun s => FirstVariation.sliceVelocity S F a b s t) (Ioo (-ε) ε) := by
  intro s hs
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (s,t) ⟨hs,ht⟩
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hpc : F (s,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  let v : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (0,1)
  have hv : ContDiffAt ℝ (⊤ : ℕ∞) v (s,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hline : Tendsto (fun r : ℝ => (r,t)) (𝓝[Ioo (-ε) ε] s)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (s,t)) :=
    ((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨hr,ht⟩)
  have hcoeff : coefficientsAlong b' (fun s => F (s,t))
      (fun s => FirstVariation.sliceVelocity S F a b s t) =ᶠ[𝓝[Ioo (-ε) ε] s]
        (fun r => v (r,t)) := by
    filter_upwards [hline.eventually
      (FirstVariation.sliceVelocity_coordinate_germ hF hab ⟨hs,ht⟩ e he hp x hx heq)] with r hr
    obtain ⟨hpr, hcr⟩ := hr
    have hpcr : F (r,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcr,
      FirstVariation.tangentFrame_coordinates e he (F (r,t)) hpr]
    exact hcr
  refine ⟨_, hU, b', hpc, (fun r => v (r,t)), ?_, hcoeff.self_of_nhdsWithin hs, hcoeff⟩
  have hv1 : ContDiffAt ℝ 1 v (s,t) := hv.of_le (by simp)
  exact hv1.comp s (contDiffAt_id.prodMk contDiffAt_const)

/-- The mixed covariant derivative itself is C¹ on each s-trace. This is a
regularity conclusion from the actual smooth coordinate germs. -/
theorem sliceVelocitySDerivative_s_c1
    (C : Connection (tangentBundle S))
    (hF : SmoothVariationOn S F ε a b) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b) :
    C1FieldOn (B := tangentBundle S) (fun s => F (s,t))
      (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) := by
  intro s hs
  obtain ⟨e, he, hp, x, hx, _, heq⟩ := hF.2 (s,t) ⟨hs,ht⟩
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have hpc : F (s,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hU : IsOpen (B.baseSet c) := B.trivialization_baseSet c ▸ (B.trivialization c).open_baseSet
  have hgram : ∀ k i j : Fin n, ∃ G : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) G (s,t) ∧
        (fun w => totalize (fun q => christoffel C c q k i j) (F w))
          =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (s,t)] G := by
    intro k i j
    exact FirstVariation.variation_scalar_extension hF ⟨hs,ht⟩ _
      (christoffel_total_smoothAt C c k i j ⟨F (s,t),hpc⟩)
  choose G hGc hGe using hgram
  let v : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (1,0)
  let w : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (0,1)
  let d : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ w z (1,0)
  have hv : ContDiffAt ℝ (⊤ : ℕ∞) v (s,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hw : ContDiffAt ℝ (⊤ : ℕ∞) w (s,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) d (s,t) :=
    (hw.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  let A : ℝ × ℝ → Euclidean n := fun z => d z +
    (fun k => ∑ j : Fin n, (∑ i : Fin n, v z i * G k i j z) * w z j)
  have hA : ContDiffAt ℝ 1 A (s,t) := by
    apply (hd.of_le (by simp)).add
    apply contDiffAt_pi.mpr
    intro k
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro i _
      exact ((contDiffAt_pi.mp hv) i).of_le (by simp) |>.mul
        ((hGc k i j).of_le (by simp))
    · exact ((contDiffAt_pi.mp hw) j).of_le (by simp)
  have hline : Tendsto (fun r : ℝ => (r,t)) (𝓝[Ioo (-ε) ε] s)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (s,t)) :=
    ((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨hr,ht⟩)
  have heqLine : (fun r => (e (F (r,t))).val) =ᶠ[𝓝[Ioo (-ε) ε] s]
      (fun r => x (r,t)) := heq.comp_tendsto hline
  have hTcoeff : coefficientsAlong b' (fun r => F (r,t))
      (fun r => FirstVariation.sliceVelocity S F a b r t) =ᶠ[𝓝[Ioo (-ε) ε] s]
        (fun r => w (r,t)) := by
    filter_upwards [hline.eventually
      (FirstVariation.sliceVelocity_coordinate_germ hF hab ⟨hs,ht⟩ e he hp x hx heq)] with r hr
    obtain ⟨hpr, hcr⟩ := hr
    have hpcr : F (r,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpr
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcr,
      FirstVariation.tangentFrame_coordinates e he (F (r,t)) hpr]
    exact hcr
  have hnearEq := eventually_eventually_nhdsWithin.mpr heqLine
  have hnearT := eventually_eventually_nhdsWithin.mpr hTcoeff
  have hx1 : ContDiffAt ℝ 1 x (s,t) := hx.of_le (by simp)
  have hw1 : ContDiffAt ℝ 1 w (s,t) := hw.of_le (by simp)
  have hxNear : ∀ᶠ r in 𝓝[Ioo (-ε) ε] s, ContDiffAt ℝ 1 x (r,t) :=
    hline.eventually ((hx1.eventually (by simp)).filter_mono nhdsWithin_le_nhds)
  have hwNear : ∀ᶠ r in 𝓝[Ioo (-ε) ε] s, ContDiffAt ℝ 1 w (r,t) :=
    hline.eventually ((hw1.eventually (by simp)).filter_mono nhdsWithin_le_nhds)
  have hGall : ∀ᶠ r in 𝓝[Ioo (-ε) ε] s, ∀ k i j : Fin n,
      totalize (fun q => christoffel C c q k i j) (F (r,t)) = G k i j (r,t) :=
    hline.eventually (Filter.eventually_all.mpr fun k =>
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hGe k i))
  have hcoeff : coefficientsAlong b' (fun r => F (r,t))
      (fun r => sliceVelocitySDerivative C F ε a b r t)
      =ᶠ[𝓝[Ioo (-ε) ε] s] (fun r => A (r,t)) := by
    filter_upwards [hnearEq, hnearT, hxNear, hwNear, hGall,
      (variation_continuousOn_sTrace hF ht s hs).eventually (e.open_source.mem_nhds hp),
      self_mem_nhdsWithin] with r hrE hrT hxr hwr hGr hpr hrJ
    have hpcr : F (r,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpr
    have hrE' : (fun u => (e (F (u,t))).val) =ᶠ[𝓝[Ioo (-ε) ε] r] (fun u => x (u,t)) := hrE
    have hrT' : coefficientsAlong b' (fun u => F (u,t))
        (fun u => FirstVariation.sliceVelocity S F a b u t) =ᶠ[𝓝[Ioo (-ε) ε] r]
          (fun u => w (u,t)) := hrT
    let L := (tangentStructure S).fiberCoordinates.equiv e he (F (r,t)) hpr
    let V : TangentSpace S (F (r,t)) := L.symm (v (r,t))
    have hV : HasVelocityWithinAt S (fun u => F (u,t)) (Ioo (-ε) ε) r V := by
      refine ⟨variation_continuousOn_sTrace hF ht r hrJ, e, he, hpr, ?_⟩
      change HasDerivWithinAt _ (L (L.symm _)) _ _
      rw [LinearEquiv.apply_symm_apply]
      exact ((hxr.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt r
        ((hasDerivAt_id r).prodMk (hasDerivAt_const r t))).hasDerivWithinAt
          |>.congr_of_eventuallyEq_of_mem hrE' hrJ
    have hwrD : HasFDerivAt w (fderiv ℝ w (r,t)) (r,t) :=
      (hwr.differentiableAt (by simp)).hasFDerivAt
    have hDT0 : HasDerivAt (fun u => w (u,t)) (d (r,t)) r := by
      exact hwrD.comp_hasDerivAt r ((hasDerivAt_id r).prodMk (hasDerivAt_const r t))
    have hDT : HasDerivWithinAt (coefficientsAlong b' (fun u => F (u,t))
        (fun u => FirstVariation.sliceVelocity S F a b u t)) (d (r,t)) (Ioo (-ε) ε) r :=
      hDT0.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hrT' hrJ
    have hder : sliceVelocitySDerivative C F ε a b r t = frameDerivative C b'
        (fun u => F (u,t)) (fun u => FirstVariation.sliceVelocity S F a b u t)
        r hpcr V (d (r,t)) :=
      CurveCovariantDerivative.covariantDerivativeWithin_eq C hrJ (uniqueDiffWithinAt_Ioo hrJ)
        ⟨_,hV,_,hU,b',hpcr,_,hDT,rfl⟩
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcr, hder]
    change (b'.basis ⟨F (r,t),hpcr⟩).equivFun
      ((b'.basis ⟨F (r,t),hpcr⟩).equivFun.symm _) = _
    rw [LinearEquiv.apply_symm_apply, hrT'.self_of_nhdsWithin hrJ]
    apply congrArg (fun q => d (r,t) + q)
    funext k
    simp only [Matrix.mulVec, dotProduct, connectionMatrix]
    apply Finset.sum_congr rfl
    intro j _
    have hform := FirstVariation.connectionForm_expansion C c ⟨F (r,t),hpcr⟩ V k j
    change connectionForm C b' ⟨F (r,t),hpcr⟩ k j V = _ at hform
    rw [hform]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    have hVc : B.fiberCoordinates c (F (r,t)) hpcr V = v (r,t) := by
      rw [SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
        (tangentRealization S).coordinates c (F (r,t)) hpr]
      exact L.apply_symm_apply _
    rw [hVc]
    congr 1
    exact (totalize_of_mem (fun q => christoffel C c q k i j) (F (r,t)) hpcr).symm.trans (hGr k i j)
  refine ⟨_, hU, b', hpc, (fun r => A (r,t)), ?_, hcoeff.self_of_nhdsWithin hs, hcoeff⟩
  exact hA.comp s (contDiffAt_id.prodMk contDiffAt_const)

/-- Differentiating the actual metric energy density twice gives the square
of the first mixed covariant derivative and its second s derivative. -/
theorem secondEnergyDensity_eq_covariant
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    secondEnergyDensity g F a b 0 t =
      pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t)
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationField S F) (Icc a b) t) +
      pairing g (F (0,t))
        (covariantDerivativeWithin C (fun s => F (s,t))
          (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) 0)
        (segmentVelocity S F a b t) := by
  let c : ℝ → M := fun s => F (s,t)
  let T : (s : ℝ) → TangentSpace S (c s) :=
    fun s => FirstVariation.sliceVelocity S F a b s t
  let U : (s : ℝ) → TangentSpace S (c s) :=
    fun s => sliceVelocitySDerivative C F ε a b s t
  let J := Ioo (-ε) ε
  let W := covariantDerivativeWithin C c U J 0
  have h0 : (0 : ℝ) ∈ J := ⟨by linarith, hε⟩
  have hc : CoordinateC1On S c J := variation_coordinateC1On_sTrace hF ht
  have hcc : ContinuousOn c J := variation_continuousOn_sTrace hF ht
  have hT : C1FieldOn (B := tangentBundle S) c T J := sliceVelocity_s_c1 hF hab ht
  have hU : C1FieldOn (B := tangentBundle S) c U J := sliceVelocitySDerivative_s_c1 C hF hab ht
  have hTD (s : ℝ) (hs : s ∈ J) : HasCovariantDerivativeWithinAt C c T J s (U s) :=
    CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C hs hc hcc hT)
  have hUD : HasCovariantDerivativeWithinAt C c U J 0 W :=
    CurveCovariantDerivative.covariantDerivativeWithin_spec C
      (CurveCovariantDerivative.exists_covariantDerivative C h0 hc hcc hU)
  let Q : ℝ → ℝ := fun s => pairing g (c s) (U s) (T s)
  have hfirst (s : ℝ) (hs : s ∈ J) :
      deriv (fun r => FirstVariation.squaredVariationSpeed g F a b (r,t)) s = 2 * Q s := by
    have hd := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2 hs
      (uniqueDiffWithinAt_Ioo hs) (hTD s hs) (hTD s hs)
    have hd' := hd.hasDerivAt (isOpen_Ioo.mem_nhds hs)
    change HasDerivAt (fun r => FirstVariation.squaredVariationSpeed g F a b (r,t)) _ s at hd'
    rw [hd'.deriv]
    change pairing g (c s) (U s) (T s) + pairing g (c s) (T s) (U s) = 2 * Q s
    dsimp only [Q, pairing]
    rw [g.symmetric (c s) (T s) (U s)]
    ring
  have hsecond := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2 h0
    (uniqueDiffWithinAt_Ioo h0) hUD (hTD 0 h0)
  have hsecond' : HasDerivAt Q
      (pairing g (c 0) W (T 0) + pairing g (c 0) (U 0) (U 0)) 0 :=
    hsecond.hasDerivAt (isOpen_Ioo.mem_nhds h0)
  have heq : (fun s => deriv (fun r => FirstVariation.squaredVariationSpeed g F a b (r,t)) s)
      =ᶠ[𝓝 0] (fun s => 2 * Q s) := by
    filter_upwards [isOpen_Ioo.mem_nhds h0] with s hs
    exact hfirst s hs
  have hd := ((hsecond').const_mul 2).congr_of_eventuallyEq heq
  have hU0 : U 0 = covariantDerivativeWithin C (fun r => F (0,r))
      (variationField S F) (Icc a b) t :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C h0 (uniqueDiffWithinAt_Ioo h0)
      (FirstVariation.sliceVelocity_mixed_covariantDerivative g C hC hF hε hab ht)
  change (1/2 : ℝ) * deriv (fun s => deriv
    (fun r => FirstVariation.squaredVariationSpeed g F a b (r,t)) s) 0 = _
  rw [hd.deriv]
  change (1/2 : ℝ) * (2 * (pairing g (F (0,t)) _ (segmentVelocity S F a b t) +
    pairing g (F (0,t)) (U 0) (U 0))) = _
  rw [hU0]
  ring

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Acceleration in a common smooth coordinate representative. -/
noncomputable def variationAccelerationCoordinate (x : ℝ × ℝ → Euclidean n)
    (G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ) (z : ℝ × ℝ) : Euclidean n :=
  fderiv ℝ (fun w => fderiv ℝ x w (1,0)) z (1,0) +
    fun k => ∑ j : Fin n,
      (∑ i : Fin n, (fderiv ℝ x z (1,0)) i * G k i j z) * (fderiv ℝ x z (1,0)) j

theorem variationAccelerationCoordinate_smoothAt
    {x : ℝ × ℝ → Euclidean n}
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x z)
    (hG : ∀ k i j, ContDiffAt ℝ (⊤ : ℕ∞) (G k i j) z) :
    ContDiffAt ℝ (⊤ : ℕ∞) (variationAccelerationCoordinate x G) z := by
  have hv : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => fderiv ℝ x w (1,0)) z :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  apply ((hv.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const).add
  apply contDiffAt_pi.mpr
  intro k
  apply ContDiffAt.sum
  intro j _
  apply ContDiffAt.mul
  · apply ContDiffAt.sum
    intro i _
    exact ((contDiffAt_pi.mp hv) i).mul (hG k i j)
  · exact (contDiffAt_pi.mp hv) j

/-- The coefficient germ of the actual acceleration is the common smooth
coordinate acceleration; it is valid at the closed t-edges as well. -/
theorem variationAcceleration_coordinate_germ
    (C : Connection (tangentBundle S)) {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) {x : ℝ × ℝ → Euclidean n}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (0,t))
    (heq : (fun z => (e (F z)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x)
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ}
    (hGe : ∀ k i j,
      (fun z => totalize (fun p => christoffel C (⟨e,he⟩ : TangentIndex S) p k i j) (F z))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G k i j) :
    coefficientsAlong (SmoothManifolds.ConstantRankBundles.trivializationFrame
      (tangentBundle S) (⟨e,he⟩ : TangentIndex S))
      (fun r => F (0,r)) (variationAcceleration C F) =ᶠ[𝓝[Icc a b] t]
      (fun r => variationAccelerationCoordinate x G (0,r)) := by
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith, hε⟩
  have hline : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have heqNear : ∀ᶠ r in 𝓝[Icc a b] t,
      (fun z => (e (F z)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,r)] x :=
    hline.eventually (eventually_eventually_nhdsWithin.mpr heq)
  have hx2 : ContDiffAt ℝ 2 x (0,t) := hx.of_le (by simp)
  have hxNear : ∀ᶠ r in 𝓝[Icc a b] t, ContDiffAt ℝ 2 x (0,r) :=
    hline.eventually ((hx2.eventually (by norm_num)).filter_mono nhdsWithin_le_nhds)
  have hGall : ∀ᶠ r in 𝓝[Icc a b] t, ∀ k i j : Fin n,
      totalize (fun p => christoffel C c p k i j) (F (0,r)) = G k i j (0,r) :=
    hline.eventually (Filter.eventually_all.mpr fun k =>
      Filter.eventually_all.mpr fun i => Filter.eventually_all.mpr (hGe k i))
  filter_upwards [heqNear, hxNear, hGall,
    (FirstVariation.variation_continuousOn_slice hF h0 t ht).eventually (e.open_source.mem_nhds hp),
    self_mem_nhdsWithin] with r hr hxr hGr hpr hrJ
  have hpcs : F (0,r) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpr
  rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcs,
    FirstVariation.tangentFrame_coordinates e he (F (0,r)) hpr,
    variationAcceleration_coordinates C hF hε hrJ e he hpr x hxr hr]
  dsimp only [variationAccelerationCoordinate]
  congr 1
  funext k
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  rw [← hGr k i j, totalize_of_mem _ _ hpcs]

/-- Coordinates of D_t A in the same ambient germs as the second-density
calculation. All one-sided derivative certificates are constructed here. -/
theorem variationAcceleration_t_coordinates
    (C : Connection (tangentBundle S)) {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) (ht : t ∈ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) {x : ℝ × ℝ → Euclidean n}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (0,t))
    (heq : (fun z => (e (F z)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x)
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ}
    (hG : ∀ k i j, ContDiffAt ℝ (⊤ : ℕ∞) (G k i j) (0,t))
    (hGe : ∀ k i j,
      (fun z => totalize (fun p => christoffel C (⟨e,he⟩ : TangentIndex S) p k i j) (F z))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G k i j) :
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (covariantDerivativeWithin C (fun r => F (0,r)) (variationAcceleration C F) (Icc a b) t) =
    fderiv ℝ (variationAccelerationCoordinate x G) (0,t) (0,1) +
      fun k => ∑ j : Fin n,
        (∑ i : Fin n, (fderiv ℝ x (0,t) (0,1)) i * G k i j (0,t)) *
          variationAccelerationCoordinate x G (0,t) j := by
  let c : TangentIndex S := ⟨e,he⟩
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hcoeff := variationAcceleration_coordinate_germ C hF hε ht e he hp hx heq hGe
  have hA := variationAccelerationCoordinate_smoothAt hx hG
  have hd := ((hA.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
    ((hasDerivAt_const t (0 : ℝ)).prodMk (hasDerivAt_id t))).hasDerivWithinAt
      (s := Icc a b)
  have hd' := hd.congr_of_eventuallyEq_of_mem hcoeff ht
  have hT := FirstVariation.segmentVelocity_spec hF hε ht
  have hc := curve_covariantDerivative_coordinates C c ht (uniqueDiffOn_Icc hab t ht) hp hT hd'
  have hTv : (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (segmentVelocity S F a b t) = fderiv ℝ x (0,t) (0,1) := by
    have hg := FirstVariation.sliceVelocity_coordinate_germ hF hab ⟨⟨by linarith,hε⟩,ht⟩
      e he hp x hx heq
    exact (hg.self_of_nhdsWithin ⟨⟨by linarith,hε⟩,ht⟩).2
  rw [hTv, hcoeff.self_of_nhdsWithin ht] at hc
  convert hc using 1
  funext k
  simp only [Pi.add_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact ((hGe k i j).self_of_nhdsWithin ⟨⟨by linarith,hε⟩,ht⟩).symm.trans
    (by exact totalize_of_mem _ _ ((tangentRealization S).baseSet c ▸ hp))

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData
open scoped Matrix

private theorem differentiableAt_matrix_mulVec
    {n : ℕ} {A : ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ} {v : ℝ × ℝ → Euclidean n}
    {z : ℝ × ℝ} (hA : DifferentiableAt ℝ A z) (hv : DifferentiableAt ℝ v z) :
    DifferentiableAt ℝ (fun w => (A w).mulVec (v w)) z := by
  apply differentiableAt_pi.mpr
  intro i
  change DifferentiableAt ℝ (fun w => ∑ j : Fin n, A w i j * v w j) z
  apply DifferentiableAt.fun_sum
  intro j _
  exact (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j).mul
    (differentiableAt_pi.mp hv j)

theorem fderiv_matrix_mulVec
    {n : ℕ} {A : ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ} {v : ℝ × ℝ → Euclidean n}
    {z : ℝ × ℝ} (hA : DifferentiableAt ℝ A z) (hv : DifferentiableAt ℝ v z)
    (d : ℝ × ℝ) :
    fderiv ℝ (fun w => (A w).mulVec (v w)) z d =
      (fderiv ℝ A z d).mulVec (v z) + (A z).mulVec (fderiv ℝ v z d) := by
  have hg := differentiableAt_matrix_mulVec hA hv
  ext i
  have hi := congrArg (fun L => L d) (fderiv_apply hg i)
  change fderiv ℝ (fun w => (A w).mulVec (v w) i) z d =
    (fderiv ℝ (fun w => (A w).mulVec (v w)) z d) i at hi
  rw [← hi]
  simp only [Matrix.mulVec, dotProduct, Pi.add_apply]
  rw [fderiv_fun_sum (u := Finset.univ) (A := fun j w => A w i j * v w j) (fun j _ =>
    (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j).mul
      (differentiableAt_pi.mp hv j))]
  simp only [ContinuousLinearMap.sum_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [fderiv_fun_mul (differentiableAt_pi.mp (differentiableAt_pi.mp hA i) j)
    (differentiableAt_pi.mp hv j)]
  rw [fderiv_apply (differentiableAt_pi.mp hA i) j, fderiv_apply hA i,
    fderiv_apply hv j]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [mul_comm (v z j)]
  exact add_comm _ _

theorem coordinate_covariant_commutator
    {n : ℕ} {A B : ℝ × ℝ → Matrix (Fin n) (Fin n) ℝ}
    {v : ℝ × ℝ → Euclidean n} {z : ℝ × ℝ}
    (hv : ContDiffAt ℝ 2 v z) (hA : DifferentiableAt ℝ A z)
    (hB : DifferentiableAt ℝ B z) :
    fderiv ℝ (fun w => fderiv ℝ v w (0,1) + (B w).mulVec (v w)) z (1,0) +
        (A z).mulVec (fderiv ℝ v z (0,1) + (B z).mulVec (v z)) -
      (fderiv ℝ (fun w => fderiv ℝ v w (1,0) + (A w).mulVec (v w)) z (0,1) +
        (B z).mulVec (fderiv ℝ v z (1,0) + (A z).mulVec (v z))) =
      (fderiv ℝ B z (1,0) - fderiv ℝ A z (0,1) + A z * B z - B z * A z).mulVec (v z) := by
  have hvs : DifferentiableAt ℝ (fun w => fderiv ℝ v w (1,0)) z :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hvt : DifferentiableAt ℝ (fun w => fderiv ℝ v w (0,1)) z :=
    ((hv.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const).differentiableAt (by simp)
  have hvd := hv.differentiableAt (by norm_num)
  have hmixed : fderiv ℝ (fun w => fderiv ℝ v w (0,1)) z (1,0) =
      fderiv ℝ (fun w => fderiv ℝ v w (1,0)) z (0,1) := by
    have hfd := (hv.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
    have hs := (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) z)).fderiv
    have ht := (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) z)).fderiv
    rw [hs,ht]
    simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
    exact (hv.isSymmSndFDerivAt (by norm_num)).eq (1,0) (0,1)
  rw [fderiv_fun_add hvt (differentiableAt_matrix_mulVec hB hvd),
    fderiv_fun_add hvs (differentiableAt_matrix_mulVec hA hvd)]
  simp only [ContinuousLinearMap.add_apply]
  rw [fderiv_matrix_mulVec hB hvd, fderiv_matrix_mulVec hA hvd,hmixed]
  simp only [Matrix.mulVec_add,Matrix.mulVec_mulVec,Matrix.sub_mulVec,Matrix.add_mulVec]
  abel

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData
open scoped Matrix

/-- The connection matrix in a direction, written solely in coefficients. -/
def coordinateConnectionMatrix {n : ℕ}
    (G : Fin n → Fin n → Fin n → ℝ) (v : Euclidean n) : Matrix (Fin n) (Fin n) ℝ :=
  fun k j => ∑ i : Fin n, v i * G k i j

private theorem coordinateConnectionMatrix_mul_apply {n : ℕ}
    (G : Fin n → Fin n → Fin n → ℝ) (v w : Euclidean n) (k l : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, v i * w j * (∑ m : Fin n, G k i m * G m j l)) =
      (coordinateConnectionMatrix G v * coordinateConnectionMatrix G w) k l := by
  simp only [coordinateConnectionMatrix,Matrix.mul_apply,Finset.mul_sum,Finset.sum_mul]
  calc
    _ = ∑ i : Fin n, ∑ m : Fin n, ∑ j : Fin n, v i * w j * (G k i m * G m j l) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ m : Fin n, ∑ i : Fin n, ∑ j : Fin n, v i * w j * (G k i m * G m j l) :=
      Finset.sum_comm
    _ = ∑ m : Fin n, ∑ j : Fin n, ∑ i : Fin n, v i * w j * (G k i m * G m j l) := by
      apply Finset.sum_congr rfl
      intro m _
      exact Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro m _
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring

/-- Contracting the canonical coordinate curvature polynomial gives the
matrix curvature of the two directional connection matrices. -/
theorem curvature_coordinate_contraction {n : ℕ}
    (G : Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (v w : Euclidean n) (k l : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, v i * w j *
      (dG k j l i - dG k i l j + ∑ m : Fin n,
        (G k i m * G m j l - G k j m * G m i l))) =
      (∑ j : Fin n, (w j * (∑ i : Fin n, v i * dG k j l i) -
        v j * (∑ i : Fin n, w i * dG k j l i))) +
      (coordinateConnectionMatrix G v * coordinateConnectionMatrix G w -
        coordinateConnectionMatrix G w * coordinateConnectionMatrix G v) k l := by
  have hd1 : (∑ i : Fin n, ∑ j : Fin n, v i * w j * dG k j l i) =
      ∑ j : Fin n, w j * (∑ i : Fin n, v i * dG k j l i) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hd2 : (∑ i : Fin n, ∑ j : Fin n, v i * w j * dG k i l j) =
      ∑ j : Fin n, v j * (∑ i : Fin n, w i * dG k j l i) := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hq1 := coordinateConnectionMatrix_mul_apply G v w k l
  have hq2 : (∑ i : Fin n, ∑ j : Fin n, v i * w j *
      (∑ m : Fin n, G k j m * G m i l)) =
      (coordinateConnectionMatrix G w * coordinateConnectionMatrix G v) k l := by
    rw [← coordinateConnectionMatrix_mul_apply G w v k l,Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  simp only [Finset.sum_sub_distrib,mul_sub,mul_add,Finset.sum_add_distrib,Pi.sub_apply]
  rw [hd1,hd2,hq1,hq2]
  rfl


theorem curvature_coordinate_contraction_mulVec {n : ℕ}
    (G : Fin n → Fin n → Fin n → ℝ)
    (dG : Fin n → Fin n → Fin n → Fin n → ℝ)
    (v w z : Euclidean n) (k : Fin n) :
    (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n, v i * (w j * (z l *
      (dG k j l i - dG k i l j + ∑ m : Fin n,
        (G k i m * G m j l - G k j m * G m i l))))) =
      ((Matrix.of (fun k l => ∑ j : Fin n,
          (w j * (∑ i : Fin n, v i * dG k j l i) -
            v j * (∑ i : Fin n, w i * dG k j l i)))) +
        coordinateConnectionMatrix G v * coordinateConnectionMatrix G w -
        coordinateConnectionMatrix G w * coordinateConnectionMatrix G v).mulVec z k := by
  let K := fun (i j l : Fin n) => dG k j l i - dG k i l j + ∑ m : Fin n,
    (G k i m * G m j l - G k j m * G m i l)
  calc
    _ = ∑ i : Fin n, ∑ l : Fin n, ∑ j : Fin n, v i * (w j * (z l * K i j l)) := by
      apply Finset.sum_congr rfl
      intro i _
      exact Finset.sum_comm
    _ = ∑ l : Fin n, ∑ i : Fin n, ∑ j : Fin n, v i * (w j * (z l * K i j l)) :=
      Finset.sum_comm
    _ = ∑ l : Fin n, (∑ i : Fin n, ∑ j : Fin n, v i * w j * K i j l) * z l := by
      apply Finset.sum_congr rfl
      intro l _
      simp only [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by
      unfold K
      simp_rw [curvature_coordinate_contraction G dG v w k]
      simp only [Matrix.mulVec,dotProduct,Matrix.sub_apply,Matrix.add_apply,Matrix.of_apply]
      apply Finset.sum_congr rfl
      intro l _
      ring

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.MapData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.CurveData P202.CurveConnectionData P202.FirstVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Multilinearity expands the actual curvature tensor in a coordinate frame. -/
theorem curvature_coordinate_expansion
    (R : CurvatureTensor S) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v w z : TangentSpace S p.val) (k : Fin n) :
    (tangentBundle S).fiberCoordinates c p.val p.property (R.val p.val v w z) k =
      ∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
        (tangentBundle S).fiberCoordinates c p.val p.property v i *
          ((tangentBundle S).fiberCoordinates c p.val p.property w j *
            ((tangentBundle S).fiberCoordinates c p.val p.property z l *
              (tangentBundle S).fiberCoordinates c p.val p.property
                (R.val p.val (coordinateVector c i p.val) (coordinateVector c j p.val)
                  (coordinateVector c l p.val)) k)) := by
  classical
  let L := (tangentBundle S).fiberCoordinates c p.val p.property
  calc
    L (R.val p.val v w z) k =
        L (R.val p.val
          (∑ i : Fin n, L v i • coordinateVector c i p.val)
          (∑ j : Fin n, L w j • coordinateVector c j p.val)
          (∑ l : Fin n, L z l • coordinateVector c l p.val)) k := by
      rw [LeviCivita.coordinate_expansion, LeviCivita.coordinate_expansion,
        LeviCivita.coordinate_expansion]
    _ = _ := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
        Finset.sum_apply, Pi.smul_apply, Finset.smul_sum, smul_eq_mul]
      conv_lhs =>
        rw [Finset.sum_comm]
        arg 2
        ext j
        rw [Finset.sum_comm]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring

/-- Pullback differentiation of a local scalar in the s direction agrees
with the derivative of any smooth ambient extension of its strip germ. -/
theorem variation_scalar_s_derivative
    {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (ht : t ∈ Icc a b)
    (f : M → ℝ) (hf : VectorSmoothAt S.smoothStructure.val f (F (0,t)))
    (G : ℝ × ℝ → ℝ) (hG : ContDiffAt ℝ 1 G (0,t))
    (heq : (fun z => f (F z)) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G) :
    scalarDerivative S f (F (0,t)) (variationField S F t) = fderiv ℝ G (0,t) (1,0) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hVw : HasVelocityWithinAt S (fun s => F (s,t)) univ 0 (variationField S F t) := by
    obtain ⟨hc,e,he,hp,hd⟩ := FirstVariation.variationField_spec hF hε ht
    exact ⟨hc.continuousWithinAt,e,he,hp,hd.hasDerivWithinAt⟩
  have hd := CurveCovariantDerivative.scalar_chain hVw f hf
  rw [hasDerivWithinAt_univ] at hd
  have hline : Tendsto (fun s : ℝ => (s,t)) (𝓝 0)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨(continuous_id.prodMk continuous_const).continuousAt, ?_⟩
    filter_upwards [Ioo_mem_nhds h0.1 h0.2] with s hs
    exact ⟨hs,ht⟩
  have hdG := ((hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt 0
    ((hasDerivAt_id 0).prodMk (hasDerivAt_const 0 t))).congr_of_eventuallyEq
      (heq.comp_tendsto hline)
  exact hd.unique hdG

/-- The same pullback derivative comparison in the one-sided t direction. -/
theorem variation_scalar_t_derivative
    {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) (ht : t ∈ Icc a b)
    (f : M → ℝ) (hf : VectorSmoothAt S.smoothStructure.val f (F (0,t)))
    (G : ℝ × ℝ → ℝ) (hG : ContDiffAt ℝ 1 G (0,t))
    (heq : (fun z => f (F z)) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G) :
    scalarDerivative S f (F (0,t)) (segmentVelocity S F a b t) = fderiv ℝ G (0,t) (0,1) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hd := CurveCovariantDerivative.scalar_chain (FirstVariation.segmentVelocity_spec hF hε ht) f hf
  have hline : Tendsto (fun r : ℝ => (0,r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have hdG : HasDerivWithinAt (fun r => f (F (0,r))) (fderiv ℝ G (0,t) (0,1)) (Icc a b) t :=
    ((hG.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t 0).prodMk (hasDerivAt_id t))).hasDerivWithinAt
      |>.congr_of_eventuallyEq_of_mem (heq.comp_tendsto hline) ht
  exact (uniqueDiffOn_Icc hab t ht).eq_deriv _ hd hdG


/-- Intrinsic scalar differentiation is linear in the actual tangent direction. -/
theorem scalarDerivative_coordinate_expansion
    (f : M → ℝ) (c : TangentIndex S) (p : (tangentBundle S).baseSet c)
    (v : TangentSpace S p.val) :
    scalarDerivative S f p.val v = ∑ i : Fin n,
      (tangentBundle S).fiberCoordinates c p.val p.property v i *
        scalarDerivative S f p.val (coordinateVector c i p.val) := by
  have h := congrArg (scalarDerivative S f p.val)
    (LeviCivita.coordinate_expansion c p.val p.property v)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData SmoothManifolds.MapData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Joint coordinate germ of the actual first s derivative of the slice tangent. -/
theorem sliceVelocitySDerivative_coordinate_germ
    (C : Connection (tangentBundle S))
    (hF : SmoothVariationOn S F ε a b) (hab : a < b)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F z ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x z)
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] x)
    (G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ)
    (hΓ : ∀ k i j : Fin n,
      (fun w => totalize (fun q => christoffel C (⟨e,he⟩ : TangentIndex S) q k i j) (F w))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] G k i j) :
    ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z,
      ∃ hpw : F w ∈ e.source,
        (tangentStructure S).fiberCoordinates.equiv e he (F w) hpw
          (sliceVelocitySDerivative C F ε a b w.1 w.2) =
          fderiv ℝ (fun q => fderiv ℝ x q (0,1)) w (1,0) +
          (fun k => ∑ j : Fin n, (∑ i : Fin n,
            fderiv ℝ x w (1,0) i * G k i j w) * fderiv ℝ x w (0,1) j) := by
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  let xs : ℝ × ℝ → Euclidean n := fun w => fderiv ℝ x w (1,0)
  let xt : ℝ × ℝ → Euclidean n := fun w => fderiv ℝ x w (0,1)
  let d : ℝ × ℝ → Euclidean n := fun w => fderiv ℝ xt w (1,0)
  let TC : ℝ × ℝ → Euclidean n := fun w => coefficientsAlong b'
    (fun s => F (s,w.2)) (fun s => FirstVariation.sliceVelocity S F a b s w.2) w.1
  have hTC : TC =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] xt := by
    filter_upwards [FirstVariation.sliceVelocity_coordinate_germ hF hab hz e he hp x hx heq] with w hw
    obtain ⟨hpw, hcw⟩ := hw
    have hpcw : F w ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hpw
    dsimp only [TC]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcw,
      FirstVariation.tangentFrame_coordinates e he (F w) hpw]
    exact hcw
  have hxt : ContDiffAt ℝ (⊤ : ℕ∞) xt z :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hx1 : ContDiffAt ℝ 1 x z := hx.of_le (by simp)
  have hxt1 : ContDiffAt ℝ 1 xt z := hxt.of_le (by simp)
  have hxNear : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z, ContDiffAt ℝ 1 x w :=
    (hx1.eventually (by simp)).filter_mono nhdsWithin_le_nhds
  have hxtNear : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z, ContDiffAt ℝ 1 xt w :=
    (hxt1.eventually (by simp)).filter_mono nhdsWithin_le_nhds
  have hΓall : ∀ᶠ w in 𝓝[Ioo (-ε) ε ×ˢ Icc a b] z, ∀ k i j : Fin n,
      totalize (fun q => christoffel C c q k i j) (F w) = G k i j w :=
    Filter.eventually_all.mpr fun k => Filter.eventually_all.mpr fun i =>
      Filter.eventually_all.mpr (hΓ k i)
  filter_upwards [eventually_eventually_nhdsWithin.mpr heq,
    eventually_eventually_nhdsWithin.mpr hTC, hxNear, hxtNear, hΓall,
    (hF.1 z hz).eventually (e.open_source.mem_nhds hp), self_mem_nhdsWithin]
      with w hwE hwT hxw hxtw hGw hpw hwD
  refine ⟨hpw, ?_⟩
  have hline : Tendsto (fun r : ℝ => (r,w.2)) (𝓝[Ioo (-ε) ε] w.1)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] w) :=
    ((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hr => ⟨hr,hwD.2⟩)
  have hwE' : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] w] x := hwE
  have hwT' : TC =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] w] xt := hwT
  have hTcoeff : coefficientsAlong b' (fun r => F (r,w.2))
      (fun r => FirstVariation.sliceVelocity S F a b r w.2)
      =ᶠ[𝓝[Ioo (-ε) ε] w.1] (fun r => xt (r,w.2)) := hwT'.comp_tendsto hline
  let L := (tangentStructure S).fiberCoordinates.equiv e he (F w) hpw
  let V : TangentSpace S (F w) := L.symm (xs w)
  have hV : HasVelocityWithinAt S (fun r => F (r,w.2)) (Ioo (-ε) ε) w.1 V := by
    refine ⟨Filter.Tendsto.comp (hF.1 w hwD) hline, e, he, hpw, ?_⟩
    change HasDerivWithinAt _ (L (L.symm _)) _ _
    rw [LinearEquiv.apply_symm_apply]
    exact ((hxw.differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt w.1
      ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2))).hasDerivWithinAt
        |>.congr_of_eventuallyEq_of_mem (hwE'.comp_tendsto hline) hwD.1
  have hxtD : HasFDerivAt xt (fderiv ℝ xt w) w :=
    (hxtw.differentiableAt (by simp)).hasFDerivAt
  have hTD0 : HasDerivAt (fun r => xt (r,w.2)) (d w) w.1 := by
    convert hxtD.comp_hasDerivAt w.1 ((hasDerivAt_id w.1).prodMk (hasDerivAt_const w.1 w.2)) using 1 <;> rfl
  have hTD : HasDerivWithinAt (coefficientsAlong b' (fun r => F (r,w.2))
      (fun r => FirstVariation.sliceVelocity S F a b r w.2)) (d w) (Ioo (-ε) ε) w.1 :=
    hTD0.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hTcoeff hwD.1
  have hformula := curve_covariantDerivative_coordinates C c hwD.1
    (uniqueDiffWithinAt_Ioo hwD.1) hpw hV hTD
  change L (sliceVelocitySDerivative C F ε a b w.1 w.2) = _ at hformula
  rw [hformula]
  have hVs : L V = xs w := L.apply_symm_apply _
  rw [hVs, hTcoeff.self_of_nhdsWithin hwD.1]
  apply congrArg (fun q => d w + q)
  funext k
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (totalize_of_mem (fun q => christoffel C c q k i j) (F w)
    ((tangentRealization S).baseSet c ▸ hpw)).symm.trans (hGw k i j)

/-- Coordinates of the second actual s derivative of the slice tangent in
one common smooth chart and common ambient Christoffel representatives. -/
theorem sliceVelocity_second_s_coordinates
    (C : Connection (tangentBundle S))
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (0,t))
    (heq : (fun w => (e (F w)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x)
    (G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ)
    (hG : ∀ k i j : Fin n, ContDiffAt ℝ (⊤ : ℕ∞) (G k i j) (0,t))
    (hΓ : ∀ k i j : Fin n,
      (fun w => totalize (fun q => christoffel C (⟨e,he⟩ : TangentIndex S) q k i j) (F w))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] G k i j) :
    let xs : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (1,0)
    let xt : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (0,1)
    let A : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ xt z (1,0) +
      (fun k => ∑ j : Fin n, (∑ i : Fin n, xs z i * G k i j z) * xt z j)
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (covariantDerivativeWithin C (fun s => F (s,t))
        (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) 0) =
      fderiv ℝ A (0,t) (1,0) +
      (fun k => ∑ j : Fin n, (∑ i : Fin n, xs (0,t) i * G k i j (0,t)) * A (0,t) j) := by
  dsimp only
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  let b' := SmoothManifolds.ConstantRankBundles.trivializationFrame B c
  let xs : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (1,0)
  let xt : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ x z (0,1)
  let A : ℝ × ℝ → Euclidean n := fun z => fderiv ℝ xt z (1,0) +
    (fun k => ∑ j : Fin n, (∑ i : Fin n, xs z i * G k i j z) * xt z j)
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  have hpc : F (0,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hxs : ContDiffAt ℝ (⊤ : ℕ∞) xs (0,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hxt : ContDiffAt ℝ (⊤ : ℕ∞) xt (0,t) :=
    (hx.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A (0,t) := by
    apply ((hxt.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiffAt_const).add
    apply contDiffAt_pi.mpr
    intro k
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.mul
    · apply ContDiffAt.sum
      intro i _
      exact ((contDiffAt_pi.mp hxs) i).mul (hG k i j)
    · exact (contDiffAt_pi.mp hxt) j
  have hline : Tendsto (fun s : ℝ => (s,t)) (𝓝[Ioo (-ε) ε] 0)
      (𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)) :=
    ((continuous_id.prodMk continuous_const).continuousAt.continuousWithinAt).tendsto_nhdsWithin
      (fun _ hs => ⟨hs,ht⟩)
  have hUgerm := sliceVelocitySDerivative_coordinate_germ C hF hab ⟨h0,ht⟩
    e he hp x hx heq G hΓ
  have hcoeff : coefficientsAlong b' (fun s => F (s,t))
      (fun s => sliceVelocitySDerivative C F ε a b s t)
      =ᶠ[𝓝[Ioo (-ε) ε] 0] (fun s => A (s,t)) := by
    filter_upwards [hline.eventually hUgerm] with s hs
    obtain ⟨hps,hcs⟩ := hs
    have hpcs : F (s,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hps
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpcs,
      FirstVariation.tangentFrame_coordinates e he (F (s,t)) hps]
    exact hcs
  have hAD : HasFDerivAt A (fderiv ℝ A (0,t)) (0,t) :=
    (hA.differentiableAt (by simp)).hasFDerivAt
  have hD0 : HasDerivAt (fun s => A (s,t)) (fderiv ℝ A (0,t) (1,0)) 0 := by
    convert hAD.comp_hasDerivAt (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).prodMk (hasDerivAt_const (0 : ℝ) t)) using 1 <;> rfl
  have hD : HasDerivWithinAt (coefficientsAlong b' (fun s => F (s,t))
      (fun s => sliceVelocitySDerivative C F ε a b s t))
      (fderiv ℝ A (0,t) (1,0)) (Ioo (-ε) ε) 0 :=
    hD0.hasDerivWithinAt.congr_of_eventuallyEq_of_mem hcoeff h0
  have hV : HasVelocityWithinAt S (fun s => F (s,t)) (Ioo (-ε) ε) 0
      (variationField S F t) := by
    obtain ⟨hc, e',he',hp',hd⟩ := FirstVariation.variationField_spec hF hε ht
    exact ⟨hc.continuousWithinAt,e',he',hp',hd.hasDerivWithinAt⟩
  have hformula := curve_covariantDerivative_coordinates C c h0
    (uniqueDiffWithinAt_Ioo h0) hp hV hD
  rw [hformula, hcoeff.self_of_nhdsWithin h0]
  have hVs : (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (variationField S F t) = xs (0,t) := by
    obtain ⟨hp',hvs⟩ := (sVelocity_coordinate_germ hF ⟨h0,ht⟩ e he hp x
      (hx.of_le (by simp)) heq).self_of_nhdsWithin ⟨h0,ht⟩
    exact hvs
  rw [hVs]
  apply congrArg (fun q => fderiv ℝ A (0,t) (1,0) + q)
  funext k
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  exact (totalize_of_mem (fun q => christoffel C c q k i j) (F (0,t)) hpc).symm.trans
    ((hΓ k i j).self_of_nhdsWithin ⟨h0,ht⟩)

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.CurveData P202.CurveConnectionData P202.FirstVariationData P202.SecondVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Local smooth connection representatives can be chosen symmetric in their
two tangent slots. Averaging preserves the actual Levi-Civita coefficients
on the parameter strip and makes the symmetry hold on the ambient domain. -/
theorem symmetric_christoffel_extensions
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {F : ℝ × ℝ → M} {ε a b : ℝ} (hF : SmoothVariationOn S F ε a b)
    {z : ℝ × ℝ} (hz : z ∈ Ioo (-ε) ε ×ˢ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val) (hp : F z ∈ e.source) :
    ∃ G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ,
      (∀ k i j, ContDiffAt ℝ (⊤ : ℕ∞) (G k i j) z) ∧
      (∀ w k i j, G k i j w = G k j i w) ∧
      ∀ k i j, (fun w => totalize
        (fun p => christoffel C (⟨e,he⟩ : TangentIndex S) p k i j) (F w))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] G k i j := by
  let c : TangentIndex S := ⟨e,he⟩
  have hpc : F z ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hG : ∀ k i j : Fin n, ∃ H : ℝ × ℝ → ℝ,
      ContDiffAt ℝ (⊤ : ℕ∞) H z ∧
        (fun w => totalize (fun p => christoffel C c p k i j) (F w))
          =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] z] H := by
    intro k i j
    exact FirstVariation.variation_scalar_extension hF hz _
      (christoffel_total_smoothAt C c k i j ⟨F z,hpc⟩)
  choose H hH hHe using hG
  refine ⟨fun k i j w => (H k i j w + H k j i w) / 2, ?_, ?_, ?_⟩
  · intro k i j
    exact ((hH k i j).add (hH k j i)).div_const 2
  · intro w k i j
    dsimp only
    rw [add_comm]
  · intro k i j
    filter_upwards [hHe k i j, hHe k j i,
      (hF.1 z hz).eventually (e.open_source.mem_nhds hp)] with w hij hji hpw
    have hpcw : F w ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hpw
    change totalize (fun p => christoffel C c p k i j) (F w) =
      (H k i j w + H k j i w) / 2
    rw [← hij, ← hji, totalize_of_mem _ _ hpcw, totalize_of_mem _ _ hpcw,
      FirstVariation.christoffel_symm g C hC c ⟨F w,hpcw⟩ k j i]
    ring

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData
open scoped Matrix

private theorem differentiableAt_coordinateConnectionMatrix {n : ℕ}
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ}
    {v : ℝ × ℝ → Euclidean n} {z : ℝ × ℝ}
    (hG : ∀ k i j, DifferentiableAt ℝ (G k i j) z)
    (hv : DifferentiableAt ℝ v z) :
    DifferentiableAt ℝ (fun z => coordinateConnectionMatrix (fun k i j => G k i j z) (v z)) z := by
  apply differentiableAt_pi.mpr
  intro k
  apply differentiableAt_pi.mpr
  intro j
  change DifferentiableAt ℝ (fun w => ∑ i : Fin n, v w i * G k i j w) z
  apply DifferentiableAt.fun_sum
  intro i _
  exact (differentiableAt_pi.mp hv i).mul (hG k i j)

theorem fderiv_coordinateConnectionMatrix {n : ℕ}
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ}
    {v : ℝ × ℝ → Euclidean n} {z : ℝ × ℝ}
    (hG : ∀ k i j, DifferentiableAt ℝ (G k i j) z)
    (hv : DifferentiableAt ℝ v z) (d : ℝ × ℝ) :
    fderiv ℝ (fun z => coordinateConnectionMatrix (fun k i j => G k i j z) (v z)) z d =
      Matrix.of (fun k j => ∑ i : Fin n,
        ((fderiv ℝ v z d) i * G k i j z + v z i * fderiv ℝ (G k i j) z d)) := by
  let A := fun z => coordinateConnectionMatrix (fun k i j => G k i j z) (v z)
  have hA : DifferentiableAt ℝ A z := differentiableAt_coordinateConnectionMatrix hG hv
  ext k j
  have hcoord : fderiv ℝ (fun w => A w k j) z d = (fderiv ℝ A z d) k j := by
    rw [fderiv_apply (differentiableAt_pi.mp hA k) j, fderiv_apply hA k]
    rfl
  change (fderiv ℝ A z d) k j = _
  rw [← hcoord]
  change fderiv ℝ (fun w => ∑ i : Fin n, v w i * G k i j w) z d =
    ∑ i : Fin n, ((fderiv ℝ v z d) i * G k i j z + v z i * fderiv ℝ (G k i j) z d)
  rw [fderiv_fun_sum (A := fun i w => v w i * G k i j w)
    (fun i _ => (differentiableAt_pi.mp hv i).mul (hG k i j))]
  simp only [ContinuousLinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [fderiv_fun_mul (differentiableAt_pi.mp hv i) (hG k i j), fderiv_apply hv i]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.proj_apply,smul_eq_mul]
  rw [mul_comm (G k i j z)]
  exact add_comm _ _

/-- The terms differentiating the directional vectors cancel when their
cross partials agree. -/
theorem connectionMatrix_cross_derivative {n : ℕ}
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ}
    {v w : ℝ × ℝ → Euclidean n} {z : ℝ × ℝ}
    (hG : ∀ k i j, DifferentiableAt ℝ (G k i j) z)
    (hv : DifferentiableAt ℝ v z) (hw : DifferentiableAt ℝ w z)
    (hmix : fderiv ℝ w z (1,0) = fderiv ℝ v z (0,1)) :
    fderiv ℝ (fun z => coordinateConnectionMatrix (fun k i j => G k i j z) (w z)) z (1,0) -
      fderiv ℝ (fun z => coordinateConnectionMatrix (fun k i j => G k i j z) (v z)) z (0,1) =
      Matrix.of (fun k j => ∑ i : Fin n,
        (w z i * fderiv ℝ (G k i j) z (1,0) -
          v z i * fderiv ℝ (G k i j) z (0,1))) := by
  rw [fderiv_coordinateConnectionMatrix hG hw, fderiv_coordinateConnectionMatrix hG hv]
  ext k j
  simp only [Matrix.sub_apply,Matrix.of_apply]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [hmix]
  ring


open Filter
open scoped Topology

/-- Equality of the two ambient coordinate mixed partials. -/
theorem fderiv_partial_comm {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {x : ℝ × ℝ → E} {z : ℝ × ℝ} (hx : ContDiffAt ℝ 2 x z) :
    fderiv ℝ (fun w => fderiv ℝ x w (0,1)) z (1,0) =
      fderiv ℝ (fun w => fderiv ℝ x w (1,0)) z (0,1) := by
  have hfd := (hx.fderiv_right (m := 1) (by norm_num)).differentiableAt (by simp)
  have hs := (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const ((0,1) : ℝ × ℝ) z)).fderiv
  have ht := (hfd.hasFDerivAt.clm_apply (hasFDerivAt_const ((1,0) : ℝ × ℝ) z)).fderiv
  rw [hs,ht]
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.zero_apply,map_zero,zero_add,ContinuousLinearMap.flip_apply]
  exact (hx.isSymmSndFDerivAt (by norm_num)).eq (1,0) (0,1)

theorem coordinateConnectionMatrix_mulVec_symm {n : ℕ}
    {G : Fin n → Fin n → Fin n → ℝ}
    (hG : ∀ k i j, G k i j = G k j i) (v w : Euclidean n) :
    (coordinateConnectionMatrix G v).mulVec w =
      (coordinateConnectionMatrix G w).mulVec v := by
  ext k
  simp only [coordinateConnectionMatrix,Matrix.mulVec,dotProduct,Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hG k j i]
  ring

/-- Ambient coordinates of the first covariant s derivative of the t tangent. -/
noncomputable def mixedVelocityCoordinate {n : ℕ} (x : ℝ × ℝ → Euclidean n)
    (G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ) (z : ℝ × ℝ) : Euclidean n :=
  fderiv ℝ (fun w => fderiv ℝ x w (0,1)) z (1,0) +
    (coordinateConnectionMatrix (fun k i j => G k i j z) (fderiv ℝ x z (1,0))).mulVec
      (fderiv ℝ x z (0,1))

/-- The coordinate second-covariant-derivative difference is matrix curvature.
Ambient symmetric Christoffel extensions may be chosen by symmetrization. -/
theorem coordinate_second_variation_commutator {n : ℕ}
    {x : ℝ × ℝ → Euclidean n}
    {G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ} {z : ℝ × ℝ}
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x z)
    (hG : ∀ k i j, DifferentiableAt ℝ (G k i j) z)
    (hGsym : ∀ k i j y, G k i j y = G k j i y) :
    let xs := fun y => fderiv ℝ x y (1,0)
    let xt := fun y => fderiv ℝ x y (0,1)
    let A := coordinateConnectionMatrix (fun k i j => G k i j z) (xs z)
    let B := coordinateConnectionMatrix (fun k i j => G k i j z) (xt z)
    fderiv ℝ (mixedVelocityCoordinate x G) z (1,0) + A.mulVec (mixedVelocityCoordinate x G z) -
      (fderiv ℝ (variationAccelerationCoordinate x G) z (0,1) +
        B.mulVec (variationAccelerationCoordinate x G z)) =
      ((Matrix.of (fun k j => ∑ i : Fin n,
        (xt z i * fderiv ℝ (G k i j) z (1,0) -
          xs z i * fderiv ℝ (G k i j) z (0,1)))) + A * B - B * A).mulVec (xs z) := by
  dsimp only
  let v := fun y => fderiv ℝ x y (1,0)
  let w := fun y => fderiv ℝ x y (0,1)
  let A := fun y => coordinateConnectionMatrix (fun k i j => G k i j y) (v y)
  let B := fun y => coordinateConnectionMatrix (fun k i j => G k i j y) (w y)
  have hv : ContDiffAt ℝ 2 v z :=
    (hx.fderiv_right (m := 2) (by simp)).clm_apply contDiffAt_const
  have hw : ContDiffAt ℝ 1 w z :=
    (hx.fderiv_right (m := 1) (by simp)).clm_apply contDiffAt_const
  have hvd := hv.differentiableAt (by norm_num)
  have hwd := hw.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ A z := differentiableAt_coordinateConnectionMatrix hG hvd
  have hB : DifferentiableAt ℝ B z := differentiableAt_coordinateConnectionMatrix hG hwd
  have heq : mixedVelocityCoordinate x G =ᶠ[𝓝 z]
      (fun y => fderiv ℝ v y (0,1) + (B y).mulVec (v y)) := by
    have hx2 : ContDiffAt ℝ 2 x z := hx.of_le (by simp)
    filter_upwards [hx2.eventually (by norm_num)] with y hy
    unfold mixedVelocityCoordinate
    rw [fderiv_partial_comm hy]
    exact congrArg (fun q => fderiv ℝ v y (0,1) + q)
      (coordinateConnectionMatrix_mulVec_symm (fun k i j => hGsym k i j y) (v y) (w y))
  have hacc : variationAccelerationCoordinate x G =
      fun y => fderiv ℝ v y (1,0) + (A y).mulVec (v y) := by
    rfl
  have h := coordinate_covariant_commutator hv hA hB
  have hUval : mixedVelocityCoordinate x G z = fderiv ℝ v z (0,1) + (B z).mulVec (v z) :=
    heq.self_of_nhds
  have haccVal : variationAccelerationCoordinate x G z =
      fderiv ℝ v z (1,0) + (A z).mulVec (v z) := congrFun hacc z
  rw [← heq.fderiv_eq, ← hUval, ← hacc, ← haccVal] at h
  have hmixed : fderiv ℝ w z (1,0) = fderiv ℝ v z (0,1) :=
    fderiv_partial_comm (hx.of_le (by simp))
  rw [connectionMatrix_cross_derivative hG hvd hwd hmixed] at h
  exact h

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.MapData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.CurveData P202.CurveConnectionData P202.FirstVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The curvature matrix in arbitrary actual tangent directions, retaining
intrinsic directional derivatives of the connection coefficients. -/
theorem curvature_directional_matrix_formula
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (c : TangentIndex S)
    (p : (tangentBundle S).baseSet c) (v w z : TangentSpace S p.val) (k : Fin n) :
    let L := (tangentBundle S).fiberCoordinates c p.val p.property
    let G := fun k i j => christoffel C c p k i j
    L (R.val p.val v w z) k =
      ((Matrix.of (fun k l => ∑ j : Fin n,
        (L w j * scalarDerivative S (totalize (fun q => christoffel C c q k j l)) p.val v -
          L v j * scalarDerivative S (totalize (fun q => christoffel C c q k j l)) p.val w))) +
        coordinateConnectionMatrix G (L v) * coordinateConnectionMatrix G (L w) -
        coordinateConnectionMatrix G (L w) * coordinateConnectionMatrix G (L v)).mulVec (L z) k := by
  dsimp only
  let L := (tangentBundle S).fiberCoordinates c p.val p.property
  let G := fun k i j => christoffel C c p k i j
  let dG := fun k j l i => scalarDerivative S
    (totalize (fun q => christoffel C c q k j l)) p.val (coordinateVector c i p.val)
  have htensor := curvature_coordinate_expansion R c p v w z k
  simp_rw [curvature_coordinate_formula C R hR] at htensor
  have halg := curvature_coordinate_contraction_mulVec G dG (L v) (L w) (L z) k
  change L (R.val p.val v w z) k = (∑ i : Fin n, ∑ j : Fin n, ∑ l : Fin n,
    L v i * (L w j * (L z l *
      (dG k j l i - dG k i l j + ∑ m : Fin n,
        (G k i m * G m j l - G k j m * G m i l))))) at htensor
  rw [htensor,halg]
  congr 2
  funext r l
  simp only [Matrix.add_apply,Matrix.of_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  dsimp only [dG]
  rw [← scalarDerivative_coordinate_expansion,← scalarDerivative_coordinate_expansion]


/-- Along a smooth variation, the curvature matrix uses precisely the
ambient derivatives of any common smooth Christoffel extensions. -/
theorem variation_curvature_matrix_formula
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {F : ℝ × ℝ → M} {ε a b t : ℝ}
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b) (ht : t ∈ Icc a b)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : F (0,t) ∈ e.source) (x : ℝ × ℝ → Euclidean n)
    (hx : ContDiffAt ℝ (⊤ : ℕ∞) x (0,t))
    (heq : (fun u => (e (F u)).val) =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] x)
    (G : Fin n → Fin n → Fin n → ℝ × ℝ → ℝ)
    (hGc : ∀ k i j, ContDiffAt ℝ 1 (G k i j) (0,t))
    (hGe : ∀ k i j,
      (fun u => totalize (fun p => christoffel C (⟨e,he⟩ : TangentIndex S) p k i j) (F u))
        =ᶠ[𝓝[Ioo (-ε) ε ×ˢ Icc a b] (0,t)] (G k i j)) (k : Fin n) :
    let v := fderiv ℝ x (0,t) (1,0)
    let w := fderiv ℝ x (0,t) (0,1)
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
      (R.val (F (0,t)) (variationField S F t) (segmentVelocity S F a b t) (variationField S F t)) k =
        (Matrix.of (fun k l => ∑ j : Fin n,
          (w j * fderiv ℝ (G k j l) (0,t) (1,0) -
            v j * fderiv ℝ (G k j l) (0,t) (0,1))) +
          coordinateConnectionMatrix (fun k i j => G k i j (0,t)) v *
            coordinateConnectionMatrix (fun k i j => G k i j (0,t)) w -
          coordinateConnectionMatrix (fun k i j => G k i j (0,t)) w *
            coordinateConnectionMatrix (fun k i j => G k i j (0,t)) v).mulVec v k := by
  dsimp only
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  let c : TangentIndex S := ⟨e,he⟩
  let B := tangentBundle S
  have hpc : F (0,t) ∈ B.baseSet c := (tangentRealization S).baseSet c ▸ hp
  let p : B.baseSet c := ⟨F (0,t),hpc⟩
  let L := B.fiberCoordinates c p.val p.property
  have hL (u : TangentSpace S (F (0,t))) :
      L u = (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp u := by
    rw [SmoothVectorBundle.fiberCoordinates_apply]
    exact (tangentRealization S).coordinates c (F (0,t)) hp u
  have hvc : L (variationField S F t) = fderiv ℝ x (0,t) (1,0) := by
    rw [hL]
    obtain ⟨hp', hv'⟩ := (sVelocity_coordinate_germ hF ⟨h0,ht⟩ e he hp x
      (hx.of_le (by simp)) heq).self_of_nhdsWithin ⟨h0,ht⟩
    exact hv'
  have hwc : L (segmentVelocity S F a b t) = fderiv ℝ x (0,t) (0,1) := by
    rw [hL]
    obtain ⟨hp', hv'⟩ := (FirstVariation.sliceVelocity_coordinate_germ hF hab
      ⟨h0,ht⟩ e he hp x hx heq).self_of_nhdsWithin ⟨h0,ht⟩
    exact hv'
  have hGval : (fun k i j => christoffel C c p k i j) = (fun k i j => G k i j (0,t)) := by
    funext k i j
    have h := (hGe k i j).self_of_nhdsWithin ⟨h0,ht⟩
    simpa only [totalize_of_mem _ (F (0,t)) hpc] using h
  have hDs (k j l : Fin n) :
      scalarDerivative S (totalize (fun q => christoffel C c q k j l)) (F (0,t))
        (variationField S F t) = fderiv ℝ (G k j l) (0,t) (1,0) :=
    variation_scalar_s_derivative hF hε ht _
      (christoffel_total_smoothAt C c k j l p) _ (hGc k j l) (hGe k j l)
  have hDt (k j l : Fin n) :
      scalarDerivative S (totalize (fun q => christoffel C c q k j l)) (F (0,t))
        (segmentVelocity S F a b t) = fderiv ℝ (G k j l) (0,t) (0,1) :=
    variation_scalar_t_derivative hF hε hab ht _
      (christoffel_total_smoothAt C c k j l p) _ (hGc k j l) (hGe k j l)
  rw [← hL]
  have h := curvature_directional_matrix_formula C R hR c p
    (variationField S F t) (segmentVelocity S F a b t) (variationField S F t) k
  dsimp only at h
  change L (R.val (F (0,t)) (variationField S F t) (segmentVelocity S F a b t)
    (variationField S F t)) k = _ at h
  rw [hvc,hwc,hGval] at h
  simpa only [p,hDs,hDt] using h

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.CurveData P202.CurveConnectionData P202.FirstVariationData P202.SecondVariationData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The intrinsic pullback commutation identity needed for second variation.
It is valid for every smooth variation, including maps of nonconstant rank,
and at the closed edges with one-sided t differentiation. -/
theorem variation_covariant_commutation
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {F : ℝ × ℝ → M} {ε a b : ℝ} (hF : SmoothVariationOn S F ε a b)
    (hε : 0 < ε) (hab : a < b) {t : ℝ} (ht : t ∈ Icc a b) :
    covariantDerivativeWithin C (fun s => F (s,t))
        (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) 0 =
      covariantDerivativeWithin C (fun r => F (0,r)) (variationAcceleration C F) (Icc a b) t +
        R.val (F (0,t)) (variationField S F t) (segmentVelocity S F a b t) (variationField S F t) := by
  have h0 : (0 : ℝ) ∈ Ioo (-ε) ε := ⟨by linarith,hε⟩
  obtain ⟨e,he,hp,x,hx,_,heq⟩ := hF.2 (0,t) ⟨h0,ht⟩
  obtain ⟨G,hG,hGsym,hGe⟩ := symmetric_christoffel_extensions g C hC hF ⟨h0,ht⟩ e he hp
  let L := (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp
  let v := fderiv ℝ x (0,t) (1,0)
  let w := fderiv ℝ x (0,t) (0,1)
  let A := coordinateConnectionMatrix (fun k i j => G k i j (0,t)) v
  let B := coordinateConnectionMatrix (fun k i j => G k i j (0,t)) w
  let K : Euclidean n :=
    (Matrix.of (fun k l => ∑ j : Fin n,
      (w j * fderiv ℝ (G k j l) (0,t) (1,0) -
        v j * fderiv ℝ (G k j l) (0,t) (0,1))) + A * B - B * A).mulVec v
  have hRv : L (R.val (F (0,t)) (variationField S F t)
      (segmentVelocity S F a b t) (variationField S F t)) = K := by
    funext k
    exact variation_curvature_matrix_formula C R hR hF hε hab ht e he hp x hx heq G
      (fun k i j => (hG k i j).of_le (by simp)) hGe k
  have hU := sliceVelocity_second_s_coordinates C hF hε hab ht e he hp x hx heq G hG hGe
  have hAt := variationAcceleration_t_coordinates C hF hε hab ht e he hp hx heq hG hGe
  have halg := coordinate_second_variation_commutator hx
    (fun k i j => (hG k i j).differentiableAt (by simp))
    (fun k i j y => hGsym y k i j)
  apply L.injective
  change L _ = L _
  rw [map_add, hRv]
  change (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp _ =
    (tangentStructure S).fiberCoordinates.equiv e he (F (0,t)) hp _ + K
  rw [hU,hAt]
  have hsub :
      fderiv ℝ (mixedVelocityCoordinate x G) (0,t) (1,0) +
        A.mulVec (mixedVelocityCoordinate x G (0,t)) -
      (fderiv ℝ (variationAccelerationCoordinate x G) (0,t) (0,1) +
        B.mulVec (variationAccelerationCoordinate x G (0,t))) = K := halg
  have hh := (sub_eq_iff_eq_add).mp hsub
  calc
    _ = K + (fderiv ℝ (variationAccelerationCoordinate x G) (0,t) (0,1) +
        B.mulVec (variationAccelerationCoordinate x G (0,t))) := hh
    _ = _ := add_comm _ _

end P202.Geometry.SecondVariation


namespace P202.Geometry.SecondVariation
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.CurvatureData P202.SecondVariationData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M} {F : ℝ × ℝ → M} {ε a b : ℝ}

/-- Curvature commutation identifies the actual second scalar energy density
with the index integrand plus the derivative of the acceleration pairing. -/
theorem secondEnergyDensity_eq_indexIntegrand_of_commutation
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    {t : ℝ} (ht : t ∈ Icc a b)
    (hcomm : covariantDerivativeWithin C (fun s => F (s,t))
        (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) 0 =
      covariantDerivativeWithin C (fun r => F (0,r)) (variationAcceleration C F) (Icc a b) t +
        R.val (F (0,t)) (variationField S F t) (segmentVelocity S F a b t) (variationField S F t)) :
    secondEnergyDensity g F a b 0 t =
      indexIntegrand g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) t +
      pairing g (F (0,t))
        (covariantDerivativeWithin C (fun r => F (0,r)) (variationAcceleration C F) (Icc a b) t)
        (segmentVelocity S F a b t) := by
  rw [secondEnergyDensity_eq_covariant g C hC hF hε hab ht, hcomm]
  simp only [map_add, LinearMap.add_apply]
  rw [curvature_term_sign g C hC R hR (F (0,t))
    (variationField S F t) (segmentVelocity S F a b t)]
  unfold indexIntegrand
  have hT : segmentTangent S (fun t => F (0,t)) a b t = segmentVelocity S F a b t := rfl
  rw [hT]
  ring

/-- The smooth source conclusion follows from the intrinsic commutation
identity. The final theorem supplies that identity, rather than assuming it. -/
theorem second_variation_energy_of_commutation
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (hF : SmoothVariationOn S F ε a b) (hε : 0 < ε) (hab : a < b)
    (hgeo : IsAffineGeodesicSegment C (fun t => F (0,t)) a b)
    (hcomm : ∀ t ∈ Icc a b,
      covariantDerivativeWithin C (fun s => F (s,t))
        (fun s => sliceVelocitySDerivative C F ε a b s t) (Ioo (-ε) ε) 0 =
      covariantDerivativeWithin C (fun r => F (0,r)) (variationAcceleration C F) (Icc a b) t +
        R.val (F (0,t)) (variationField S F t) (segmentVelocity S F a b t) (variationField S F t)) :
    HasDerivAt (deriv (variedEnergy g F a b))
      (indexForm g C R (fun t => F (0,t)) a b (variationField S F) (variationField S F) +
        accelerationBoundary g C F a b) 0 := by
  apply secondVariation_of_pointwise_density g C hC.2 R hF hε hab hgeo
  intro t ht
  exact secondEnergyDensity_eq_indexIntegrand_of_commutation g C hC R hR hF hε hab ht (hcomm t ht)

end P202.Geometry.SecondVariation

namespace P202.Geometry.SecondVariation
universe u

/-- Second variation of the canonical energy, retaining moving endpoint
acceleration and requiring only the original smooth-variation hypotheses. -/
theorem second_variation_energy :
    P202Specs.Geometry.SecondVariation.second_variation_energyType.{u} := by
  intro n M _ S g C hC R hR F ε a b hε hab hF hgeo
  apply second_variation_energy_of_commutation g C hC R hR hF hε hab hgeo
  intro t ht
  exact variation_covariant_commutation g C hC R hR hF hε hab ht

/-- Fixed finite piecewise smooth variations satisfy the same complete
moving-endpoint formula; internal acceleration boundary terms cancel. -/
theorem piecewise_second_variation_energy :
    P202Specs.Geometry.SecondVariation.piecewise_second_variation_energyType.{u} :=
  piecewise_second_variation_from_smooth_formula second_variation_energy

end P202.Geometry.SecondVariation
