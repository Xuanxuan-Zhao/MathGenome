import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.RauchComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.IndexLemma
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Reflection

/-! Rauch comparison on the intrinsic tangent fibers.
The supporting lemmas use the accepted index lemma and the actual Jacobi IVP.
No comparison or nonconjugacy certificate is added to the geometric hypotheses. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.RauchComparison
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
  P202.ExponentialJacobiData P202.JacobiMatrixData P202.RauchComparisonData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem orthonormal_independent (g : RiemannianMetric S)
    (p : M) (T v : TangentSpace S p)
    (hT : pairing g p T T = 1) (hv : pairing g p v v = 1)
    (horth : pairing g p v T = 0) : LinearIndependent ℝ ![T, v] := by
  apply (linearIndependent_fin2 (K := ℝ) (f := ![T,v])).mpr
  constructor
  · change v ≠ 0
    intro hz
    rw [hz, LinearMap.BilinForm.zero_left] at hv
    norm_num at hv
  · change ∀ a : ℝ, a • v ≠ T
    intro a hab
    have h1 := congrArg (fun z => pairing g p z T) hab
    rw [LinearMap.BilinForm.smul_left, horth, hT, mul_zero] at h1
    norm_num at h1

/-- The metric-unit condition in the Specs is equivalent to norm one. -/
theorem tangentNorm_eq_one_iff (g : RiemannianMetric S) (p : M)
    (v : TangentSpace S p) : tangentNorm g p v = 1 ↔ pairing g p v v = 1 := by
  constructor
  · intro h
    simpa only [h, one_pow] using (SmoothMetrics.tangentNorm_sq g p v).symm
  · intro h
    simp only [tangentNorm, h, Real.sqrt_one]

theorem normalized_pairing (g : RiemannianMetric S) (p : M)
    (v : TangentSpace S p) (hv : v ≠ 0) :
    pairing g p ((tangentNorm g p v)⁻¹ • v) ((tangentNorm g p v)⁻¹ • v) = 1 := by
  have hn : 0 < tangentNorm g p v :=
    Real.sqrt_pos.mpr (g.positive p v hv)
  rw [← SmoothMetrics.tangentNorm_sq,
    SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr hn),
    inv_mul_cancel₀ (ne_of_gt hn), one_pow]


/-- On the unit orthogonal pairs used in the hypothesis, the curvature form
in the independent specification is exactly sectional curvature. -/
theorem sectionalCurvature_of_orthonormal (g : RiemannianMetric S)
    (R : CurvatureTensor S) (p : M) (T v : TangentSpace S p)
    (hT : pairing g p T T = 1) (hv : pairing g p v v = 1)
    (horth : pairing g p v T = 0) (hi : LinearIndependent ℝ ![T, v]) :
    sectionalCurvature g R p T v hi = curvatureForm g R p T v v T := by
  have ho : pairing g p T v = 0 := (g.symmetric p T v).trans horth
  simp only [sectionalCurvature, hT, hv, ho, one_mul, zero_pow (by decide : 2 ≠ 0),
    sub_zero, div_one]

/-- Uniqueness compares only values on the actual open domain. -/
theorem jacobi_initial_unique (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J K : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hK : IsJacobiField C R I.carrier q K)
    (hvalue : J 0 = K 0) (w : TangentSpace S (q 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w)
    (hdK : HasCovariantDerivativeAt C (fun s => (q s).1) K 0 w) :
    ∀ t ∈ I.carrier, J t = K t := by
  obtain ⟨L, _, _, _, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq
    0 h0 (K 0) w
  intro t ht
  exact (huniq J hJ hvalue hdJ t ht).trans (huniq K hK rfl hdK t ht).symm

/-- The zero initial jet gives the zero solution on the whole domain. -/
theorem jacobi_zero_of_zero_initial (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 0) :
    ∀ t ∈ I.carrier, J t = 0 := by
  have hd0 : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq 0 h0).2 (0 : ℝ)
  exact jacobi_initial_unique g C hC R hR I q hq h0 J (fun _ => 0) hJ
    (by simpa only [zero_smul] using JacobiIVP.jacobi_smul C R hJ (0 : ℝ)) hJ0 0 hdJ hd0

/-- An initially zero Jacobi field whose initial derivative is normal stays
normal. Neither unit speed nor nonconstancy is needed. -/
theorem normal_of_initial (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (w : TangentSpace S (q 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w)
    (hw : pairing g (q 0).1 w (q 0).2 = 0) :
    NormalFieldOn g q J I.carrier := by
  obtain ⟨a, c, hac⟩ := JacobiIVP.pairing_velocity_affine g C hC R hR I q hq J hJ
  have ha : a = 0 := by
    have h := hac 0 h0
    simpa only [hJ0, map_zero, LinearMap.zero_apply, mul_zero, add_zero] using h.symm
  have hp : HasDerivAt (fun t : ℝ => a + c * t) c 0 := by
    simpa only [mul_one, id_eq] using! ((hasDerivAt_id (0 : ℝ)).const_mul c).const_add a
  have hd := ParallelTransport.metric_pairing_deriv C g hC.2
    (mem_univ 0) uniqueDiffWithinAt_univ hdJ (hq 0 h0).2
  have hd' : HasDerivAt (fun t => pairing g (q t).1 (J t) (q t).2) 0 0 := by
    change HasDerivWithinAt (fun t => pairing g (q t).1 (J t) (q t).2)
      (pairing g (q 0).1 w (q 0).2 + pairing g (q 0).1 (J 0) 0) univ 0 at hd
    rw [hw, LinearMap.BilinForm.zero_right (B := pairing g (q 0).1), add_zero] at hd
    exact hasDerivWithinAt_univ.mp hd
  have heq : (fun t => pairing g (q t).1 (J t) (q t).2) =ᶠ[𝓝 0]
      (fun t : ℝ => a + c * t) := by
    filter_upwards [I.isOpen.mem_nhds h0] with t ht using hac t ht
  have hc : c = 0 := hp.unique (hd'.congr_of_eventuallyEq heq.symm)
  intro t ht
  rw [hac t ht, ha, hc, zero_mul, add_zero]

/-- Nonconjugacy at a particular time prevents a nonzero-initial-derivative
Jacobi field starting at zero from vanishing there. -/
theorem jacobi_value_ne_zero (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (w : TangentSpace S (q 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w) (hw : w ≠ 0)
    (t : ℝ) (ht : t ∈ I.carrier)
    (hnc : ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) : J t ≠ 0 := by
  intro hJt
  let j : RestrictedField S I q := fun s => J s.val
  have hj : j ∈ EndpointFields S C R I q ⟨0,h0⟩ ⟨t,ht⟩ :=
    ⟨⟨J, hJ, fun _ => rfl⟩, hJ0, hJt⟩
  have hj0 : j = 0 := by
    by_contra hjne
    exact hnc ⟨j, hj, hjne⟩
  have hd : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 w := by
    apply ParallelTransport.derivative_field_congr C (mem_univ 0) _ hdJ
    rw [nhdsWithin_univ]
    filter_upwards [I.isOpen.mem_nhds h0] with s hs
    exact congrFun hj0 ⟨s,hs⟩
  have hd0 : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq 0 h0).2 (0 : ℝ)
  exact hw (CurveCovariantDerivative.covariantDerivative_unique C
    (mem_univ 0) uniqueDiffWithinAt_univ hd hd0)

/-- Positivity is for the metric norm on the actual fiber, not a coordinate
norm chosen independently of the metric. -/
theorem jacobi_norm_pos (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (w : TangentSpace S (q 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w) (hw : w ≠ 0)
    (t : ℝ) (ht : t ∈ I.carrier)
    (hnc : ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) :
    0 < tangentNorm g (q t).1 (J t) := by
  exact lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g (q t).1 (J t))
    (Ne.symm ((SmoothMetrics.tangentNorm_eq_zero_iff g (q t).1 (J t)).not.mpr
      (jacobi_value_ne_zero C R I q hq h0 J hJ hJ0 w hdJ hw t ht hnc)))

theorem normal_of_two_orthogonal_values (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J)
    (b : ℝ) (hb : b ∈ I.carrier) (hbne : b ≠ 0)
    (hJ0 : pairing g (q 0).1 (J 0) (q 0).2 = 0)
    (hJb : pairing g (q b).1 (J b) (q b).2 = 0) :
    NormalFieldOn g q J I.carrier := by
  obtain ⟨a, c, hac⟩ := JacobiIVP.pairing_velocity_affine g C hC R hR I q hq J hJ
  have ha : a = 0 := by
    simpa only [hJ0, mul_zero, add_zero] using (hac 0 h0).symm
  have hc : c = 0 := by
    have h := hac b hb
    rw [ha, hJb, zero_add] at h
    exact (mul_eq_zero.mp h.symm).resolve_right hbne
  intro t ht
  rw [hac t ht, ha, hc, zero_mul, add_zero]

/-- Orthogonality at the prescribed terminal endpoint forces normality.
The parameterized version also records the boundary-value interface explicitly. -/
theorem normal_endpoint_conditional
    (endpoint : P202Specs.Geometry.IndexLemma.endpointType.{u})
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (b : ℝ) (hbpos : 0 < b) (hb : b ∈ I.carrier)
    (hnc : ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨b,hb⟩)
    (z : TangentSpace S (q b).1) (hz : pairing g (q b).1 z (q b).2 = 0) :
    ∃ J : (t : ℝ) → TangentSpace S (q t).1,
      IsJacobiField C R I.carrier q J ∧ J 0 = 0 ∧ J b = z ∧
      NormalFieldOn g q J I.carrier ∧
      ∀ K : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q K → K 0 = 0 → K b = z →
        ∀ t ∈ I.carrier, K t = J t := by
  obtain ⟨J, hJ, hJ0, hJb, huniq⟩ := endpoint S g C hC R hR I q hq h0 b hbpos hb hnc z
  refine ⟨J, hJ, hJ0, hJb, ?_, huniq⟩
  apply normal_of_two_orthogonal_values g C hC R hR I q hq h0 J hJ b hb (ne_of_gt hbpos)
  · rw [hJ0, LinearMap.BilinForm.zero_left]
  · rw [hJb]
    exact hz

/-- The actual covariant derivative differentiates the metric square norm. -/
theorem square_norm_hasDerivAt (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (q : ℝ → Phase S) (J : (t : ℝ) → TangentSpace S (q t).1)
    (t : ℝ) (w : TangentSpace S (q t).1)
    (hd : HasCovariantDerivativeAt C (fun s => (q s).1) J t w) :
    HasDerivAt (fun s => tangentNorm g (q s).1 (J s) ^ 2)
      (2 * pairing g (q t).1 w (J t)) t := by
  have h := ParallelTransport.metric_pairing_deriv C g hC.2
    (mem_univ t) uniqueDiffWithinAt_univ hd hd
  have heq : (fun s => tangentNorm g (q s).1 (J s) ^ 2) =
      (fun s => pairing g (q s).1 (J s) (J s)) :=
    funext (fun s => SmoothMetrics.tangentNorm_sq g (q s).1 (J s))
  rw [heq]
  change HasDerivWithinAt (fun s => pairing g (q s).1 (J s) (J s))
    (pairing g (q t).1 w (J t) + pairing g (q t).1 (J t) w) univ t at h
  have hs : pairing g (q t).1 (J t) w = pairing g (q t).1 w (J t) :=
    g.symmetric (q t).1 (J t) w
  rw [hs, ← two_mul] at h
  exact hasDerivWithinAt_univ.mp h

/-- In a parallel frame the Gram form is constant, even when the frame is
not orthonormal or not surjective onto the full tangent fiber. -/
theorem parallel_frame_pairing_constant {r : ℕ} (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (D : JacobiSystem S C R I q r) (h0 : 0 ∈ I.carrier)
    (x y : Euclidean r) (t : ℝ) (ht : t ∈ I.carrier) :
    pairing g (q t).1 (D.frame t x) (D.frame t y) =
      pairing g (q 0).1 (D.frame 0 x) (D.frame 0 y) := by
  have hd (s : ℝ) (hs : s ∈ I.carrier) :
      HasDerivAt (fun z => pairing g (q z).1 (D.frame z x) (D.frame z y)) 0 s := by
    have h := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ s) uniqueDiffWithinAt_univ (D.frame_parallel x s hs) (D.frame_parallel y s hs)
    simpa only [pairing, hasDerivWithinAt_univ, map_zero,
      LinearMap.zero_apply, add_zero] using h
  obtain ⟨a, ha⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv)
  exact (ha t ht).trans (ha 0 h0).symm

section TwoManifolds
variable {N : Type u} [TopologicalSpace N] {Sbar : SmoothManifold n .euclidean N}

/-- The curvature-form predicate in the independent Specs has exactly the
all-pairs sectional-curvature meaning in the source. -/
theorem radialSectionalBound_iff (g : RiemannianMetric S)
    (gbar : RiemannianMetric Sbar) (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar) (K : Set ℝ)
    (hunit : UnitSpeedOn g q K) (hunitbar : UnitSpeedOn gbar qbar K) :
    RadialSectionalBound g gbar R Rbar q qbar K ↔
      ∀ (t : ℝ) (ht : t ∈ K), ∀ (v : TangentSpace S (q t).1) (vbar : TangentSpace Sbar (qbar t).1)
        (hv : pairing g (q t).1 v (q t).2 = 0) (hvv : pairing g (q t).1 v v = 1)
        (hvbar : pairing gbar (qbar t).1 vbar (qbar t).2 = 0)
        (hvvbar : pairing gbar (qbar t).1 vbar vbar = 1),
      sectionalCurvature g R (q t).1 (q t).2 v
        (orthonormal_independent g (q t).1 (q t).2 v (hunit t ht) hvv hv) ≤
      sectionalCurvature gbar Rbar (qbar t).1 (qbar t).2 vbar
        (orthonormal_independent gbar (qbar t).1 (qbar t).2 vbar
          (hunitbar t ht) hvvbar hvbar) := by
  constructor
  · intro h t ht v vbar hv hvv hvbar hvvbar
    rw [sectionalCurvature_of_orthonormal g R _ _ _ (hunit t ht) hvv hv,
      sectionalCurvature_of_orthonormal gbar Rbar _ _ _ (hunitbar t ht) hvvbar hvbar]
    exact h t ht v vbar hv hvv hvbar hvvbar
  · intro h t ht v vbar hv hvv hvbar hvvbar
    have hc := h t ht v vbar hv hvv hvbar hvvbar
    rw [sectionalCurvature_of_orthonormal g R _ _ _ (hunit t ht) hvv hv,
      sectionalCurvature_of_orthonormal gbar Rbar _ _ _ (hunitbar t ht) hvvbar hvbar] at hc
    exact hc

theorem radial_quadratic_comparison (g : RiemannianMetric S)
    (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar) (K : Set ℝ)
    (hbound : RadialSectionalBound g gbar R Rbar q qbar K)
    (t : ℝ) (ht : t ∈ K)
    (v : TangentSpace S (q t).1) (vbar : TangentSpace Sbar (qbar t).1)
    (hv : pairing g (q t).1 v (q t).2 = 0)
    (hvbar : pairing gbar (qbar t).1 vbar (qbar t).2 = 0)
    (hn : tangentNorm g (q t).1 v = tangentNorm gbar (qbar t).1 vbar) :
    pairing g (q t).1 (R.val (q t).1 v (q t).2 (q t).2) v ≤
      pairing gbar (qbar t).1 (Rbar.val (qbar t).1 vbar (qbar t).2 (qbar t).2) vbar := by
  by_cases hz : v = 0
  · have hzbar : vbar = 0 := by
      apply (SmoothMetrics.tangentNorm_eq_zero_iff gbar (qbar t).1 vbar).mp
      rw [← hn, hz, SmoothMetrics.tangentNorm_zero]
    subst v
    subst vbar
    simp only [map_zero, LinearMap.zero_apply, le_refl]
  have hzbar : vbar ≠ 0 := by
    intro h
    apply hz
    apply (SmoothMetrics.tangentNorm_eq_zero_iff g (q t).1 v).mp
    rw [hn, h, SmoothMetrics.tangentNorm_zero]
  have hnpos : 0 < tangentNorm g (q t).1 v := Real.sqrt_pos.mpr (g.positive _ _ hz)
  let c : ℝ := (tangentNorm g (q t).1 v)⁻¹
  have hc : 0 < c := inv_pos.mpr hnpos
  have hunit := normalized_pairing g (q t).1 v hz
  have hunitbar := normalized_pairing gbar (qbar t).1 vbar hzbar
  rw [← hn] at hunitbar
  have h := hbound t ht (c • v) (c • vbar)
    (by simp only [LinearMap.BilinForm.smul_left, hv, mul_zero]) hunit
    (by simp only [LinearMap.BilinForm.smul_left, hvbar, mul_zero]) hunitbar
  simp only [CurvatureAlgebra.form_smul_second,
    CurvatureAlgebra.form_smul_third] at h
  have h' := le_of_mul_le_mul_left (le_of_mul_le_mul_left h hc) hc
  rw [CurvatureAlgebra.form_pair_exchange C g hC R hR,
    CurvatureAlgebra.form_pair_exchange Cbar gbar hCbar Rbar hRbar] at h'
  exact h'


/-- The degenerate initial-derivative case of Rauch is unconditional: equal
initial norms force both derivatives, and hence both fields, to be zero. -/
theorem zero_initial_comparison (g : RiemannianMetric S)
    (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (Jbar : (t : ℝ) → TangentSpace Sbar (qbar t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJbar : IsJacobiField Cbar Rbar Ibar.carrier qbar Jbar)
    (hJ0 : J 0 = 0) (hJbar0 : Jbar 0 = 0)
    (w : TangentSpace S (q 0).1) (wbar : TangentSpace Sbar (qbar 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w)
    (hdJbar : HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) Jbar 0 wbar)
    (hnorm : tangentNorm g (q 0).1 w = tangentNorm gbar (qbar 0).1 wbar)
    (hw : w = 0) :
    ∀ t ∈ I.carrier ∩ Ibar.carrier,
      tangentNorm gbar (qbar t).1 (Jbar t) = tangentNorm g (q t).1 (J t) := by
  have hwbar : wbar = 0 := by
    apply (SmoothMetrics.tangentNorm_eq_zero_iff gbar (qbar 0).1 wbar).mp
    rw [← hnorm, hw, SmoothMetrics.tangentNorm_zero]
  subst w
  subst wbar
  have hz := jacobi_zero_of_zero_initial g C hC R hR I q hq h0 J hJ hJ0 hdJ
  have hzbar := jacobi_zero_of_zero_initial gbar Cbar hCbar Rbar hRbar
    Ibar qbar hqbar hbar0 Jbar hJbar hJbar0 hdJbar
  intro t ht
  rw [hz t ht.1, hzbar t ht.2, SmoothMetrics.tangentNorm_zero,
    SmoothMetrics.tangentNorm_zero]

end TwoManifolds
theorem eventually_bijective_jacobi_operator {r : ℕ}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (h0 : 0 ∈ I.carrier) :
    ∀ᶠ t in 𝓝[≠] (0 : ℝ), Function.Bijective (D.A t) := by
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • D.A t)
      (𝓝[≠] 0) (𝓝 (1 : Operator r)) := by
    simpa only [zero_add, D.initial_A, D.initial_B, sub_zero] using
      ((D.derivatives 0 h0).1.tendsto_slope_zero)
  have hunit : ∀ᶠ t in 𝓝[≠] (0 : ℝ), IsUnit (t⁻¹ • D.A t) :=
    hlim.eventually (Units.isOpen.mem_nhds isUnit_one)
  filter_upwards [hunit, self_mem_nhdsWithin] with t ht htne
  have htn : t ≠ 0 := by simpa only [mem_compl_iff, mem_singleton_iff] using htne
  have hbij := ContinuousLinearMap.isUnit_iff_bijective.mp ht
  constructor
  · intro x y hxy
    apply hbij.1
    change t⁻¹ • D.A t x = t⁻¹ • D.A t y
    rw [hxy]
  · intro y
    obtain ⟨x, hx⟩ := hbij.2 (t⁻¹ • y)
    refine ⟨x, ?_⟩
    have hh := congrArg (fun v => t • v) hx
    change t • (t⁻¹ • D.A t x) = t • (t⁻¹ • y) at hh
    simpa only [smul_smul, mul_inv_cancel₀ htn, one_smul] using hh

/-- Scalar comparison allowing the smaller-curvature square norm to vanish.
The denominator is the square norm on the nonconjugate comparison geodesic. -/
theorem comparison_of_cross_derivative {f g f' g' : ℝ → ℝ} {b : ℝ}
    (hgpos : ∀ t ∈ Ioc 0 b, 0 < g t)
    (hf : ∀ t ∈ Ioc 0 b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ioc 0 b, HasDerivAt g (g' t) t)
    (hd : ∀ t ∈ Ioc 0 b, 0 ≤ f' t * g t - f t * g' t)
    (hlim : Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 1)) :
    ∀ t ∈ Ioc 0 b, g t ≤ f t := by
  have hder (t : ℝ) (ht : t ∈ Ioc 0 b) :
      HasDerivAt (fun s => f s / g s)
        ((f' t * g t - f t * g' t) / (g t)^2) t :=
    (hf t ht).div (hg t ht) (ne_of_gt (hgpos t ht))
  have hmono : MonotoneOn (fun t => f t / g t) (Ioc 0 b) := by
    apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 b)
      (fun t ht => (hder t ht).continuousAt.continuousWithinAt)
      (fun t ht => (hder t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => div_nonneg (hd t (interior_subset ht)) (sq_nonneg _))
  intro t ht
  have hge : (1 : ℝ) ≤ f t / g t := by
    apply le_of_tendsto hlim
    filter_upwards [self_mem_nhdsWithin, (eventually_lt_nhds ht.1).filter_mono nhdsWithin_le_nhds]
      with s hs hst
    exact hmono ⟨hs, hst.le.trans ht.2⟩ ht hst.le
  simpa only [one_mul] using (le_div_iff₀ (hgpos t ht)).mp hge

/-- Integration of the logarithmic-derivative comparison used in the paper. -/
theorem comparison_of_log_derivative {f g f' g' : ℝ → ℝ} {b : ℝ}
    (hfpos : ∀ t ∈ Ioc 0 b, 0 < f t) (hgpos : ∀ t ∈ Ioc 0 b, 0 < g t)
    (hf : ∀ t ∈ Ioc 0 b, HasDerivAt f (f' t) t)
    (hg : ∀ t ∈ Ioc 0 b, HasDerivAt g (g' t) t)
    (hd : ∀ t ∈ Ioc 0 b, g' t / g t ≤ f' t / f t)
    (hlim : Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 1)) :
    ∀ t ∈ Ioc 0 b, g t ≤ f t := by
  apply comparison_of_cross_derivative hgpos hf hg _ hlim
  intro t ht
  have hm := (div_le_div_iff₀ (hgpos t ht) (hfpos t ht)).mp (hd t ht)
  nlinarith

/-- Equal nonzero first-order coefficients give ratio one at the singular
initial endpoint, without dividing by a function at zero. -/
theorem ratio_tendsto_one_of_first_order {f g : ℝ → ℝ} {a : ℝ}
    (ha : a ≠ 0)
    (hf : Tendsto (fun t => f t / t) (𝓝[>] 0) (𝓝 a))
    (hg : Tendsto (fun t => g t / t) (𝓝[>] 0) (𝓝 a)) :
    Tendsto (fun t => f t / g t) (𝓝[>] 0) (𝓝 1) := by
  have h := hf.div hg ha
  rw [div_self ha] at h
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact div_div_div_cancel_right₀ (show t ≠ 0 from ne_of_gt ht) (f t) (g t)


/-- Parallel coordinates preserve the original metric pairing on the entire
open affine time domain. The coordinates need not be orthonormal. -/
theorem parallel_equiv_pairing_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (hP : ∀ x, ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => P s x) t 0)
    {a t : ℝ} (ha : a ∈ I.carrier) (ht : t ∈ I.carrier)
    (x y : Euclidean n) :
    pairing g (q t).1 (P t x) (P t y) = pairing g (q a).1 (P a x) (P a y) := by
  have hd (s : ℝ) (hs : s ∈ I.carrier) :
      HasDerivAt (fun z => pairing g (q z).1 (P z x) (P z y)) 0 s := by
    have h := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ s) uniqueDiffWithinAt_univ (hP x s hs) (hP y s hs)
    simpa only [pairing, hasDerivWithinAt_univ, map_zero,
      LinearMap.zero_apply, add_zero] using h
  obtain ⟨c, hc⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv)
  exact (hc t ht).trans (hc a ha).symm

/-- The metric norm has its expected first-order behavior at an initially
zero field. Only the actual covariant derivative at zero is required. -/
theorem tangentNorm_div_time_tendsto (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1) (hJ0 : J 0 = 0)
    (w : TangentSpace S (q 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w) :
    Tendsto (fun t => tangentNorm g (q t).1 (J t) / t)
      (𝓝[>] 0) (𝓝 (tangentNorm g (q 0).1 w)) := by
  let P := JacobiIVP.intervalParallelEquiv C I q hq 0 h0
  have hP (x : Euclidean n) :=
    JacobiIVP.intervalParallelEquiv_parallel C I q hq 0 h0 x
  let j : ℝ → Euclidean n := fun t => (P t).symm (J t)
  have hj0 : j 0 = 0 := by simp only [j, hJ0, map_zero]
  have hj : HasDerivAt j ((P 0).symm w) 0 := by
    apply (JacobiIVP.derivative_parallel_equiv C P (hq 0 h0).1
      (fun i => hP (Pi.single i 1) 0 h0) j ((P 0).symm w)).mpr
    simpa only [j, LinearEquiv.apply_symm_apply] using hdJ
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • j t)
      (𝓝[>] 0) (𝓝 ((P 0).symm w)) := by
    have h := hj.tendsto_slope_zero.mono_left (nhdsWithin_mono 0 (by
      intro t ht
      exact ne_of_gt ht : Ioi (0 : ℝ) ⊆ {0}ᶜ))
    simpa only [zero_add, hj0, sub_zero] using h
  let B : LinearMap.BilinForm ℝ (Euclidean n) :=
    (pairing g (q 0).1).compl₁₂ (P 0).toLinearMap (P 0).toLinearMap
  have hB : Continuous (fun xy : Euclidean n × Euclidean n => B xy.1 xy.2) :=
    IndexLemma.continuous_bilin B
  have hlimB := hB.continuousAt.tendsto.comp (hlim.prodMk_nhds hlim)
  have hlimN : Tendsto (fun t => Real.sqrt (B (t⁻¹ • j t) (t⁻¹ • j t)))
      (𝓝[>] 0) (𝓝 (tangentNorm g (q 0).1 w)) := by
    simpa only [B, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, tangentNorm, Function.comp_apply] using hlimB.sqrt
  apply hlimN.congr'
  have hI : I.carrier ∈ 𝓝[>] (0 : ℝ) := nhdsWithin_le_nhds (I.isOpen.mem_nhds h0)
  filter_upwards [self_mem_nhdsWithin, hI] with t ht htI
  have hpair := parallel_equiv_pairing_constant g C hC I q P hP h0 htI
    (t⁻¹ • j t) (t⁻¹ • j t)
  change pairing g (q t).1 (P t (t⁻¹ • j t)) (P t (t⁻¹ • j t)) =
    B (t⁻¹ • j t) (t⁻¹ • j t) at hpair
  rw [← hpair]
  change tangentNorm g (q t).1 (P t (t⁻¹ • j t)) = _
  rw [map_smul, show P t (j t) = J t from (P t).apply_symm_apply (J t),
    SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr ht), div_eq_inv_mul]

/-- In particular, equal nonzero initial derivative norms give the limiting
ratio used in Rauch, in the intrinsic metrics on the two manifolds. -/
theorem jacobi_norm_ratio_tendsto {N : Type u} [TopologicalSpace N]
    {Sbar : SmoothManifold n .euclidean N}
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (Jbar : (t : ℝ) → TangentSpace Sbar (qbar t).1)
    (hJ0 : J 0 = 0) (hJbar0 : Jbar 0 = 0)
    (w : TangentSpace S (q 0).1) (wbar : TangentSpace Sbar (qbar 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w)
    (hdJbar : HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) Jbar 0 wbar)
    (hn : tangentNorm g (q 0).1 w = tangentNorm gbar (qbar 0).1 wbar) (hw : w ≠ 0) :
    Tendsto (fun t => tangentNorm g (q t).1 (J t) / tangentNorm gbar (qbar t).1 (Jbar t))
      (𝓝[>] 0) (𝓝 1) := by
  have ha : tangentNorm g (q 0).1 w ≠ 0 :=
    (SmoothMetrics.tangentNorm_eq_zero_iff g (q 0).1 w).not.mpr hw
  have hlimbar := tangentNorm_div_time_tendsto gbar Cbar hCbar Ibar qbar hqbar hbar0
    Jbar hJbar0 wbar hdJbar
  rw [← hn] at hlimbar
  exact ratio_tendsto_one_of_first_order ha
    (tangentNorm_div_time_tendsto g C hC I q hq h0 J hJ0 w hdJ) hlimbar


open Module SmoothManifolds.FrameData P202.SecondVariationData P202.IndexLemmaData MeasureTheory
universe v

private def realInnerCore {V : Type u} [AddCommGroup V] [Module ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) : InnerProductSpace.Core ℝ V where
  inner := fun x y => B x y
  conj_inner_symm x y := by simpa only [conj_trivial] using hs y x
  re_inner_nonneg x := by
    change 0 ≤ B x x
    by_cases hx : x = 0
    · simp [hx]
    · exact (hp x hx).le
  add_left x y z := B.map_add₂ x y z
  smul_left x y r := by simpa only [conj_trivial, smul_eq_mul] using B.map_smul₂ r x y
  definite x h := by
    by_contra hx
    exact (ne_of_gt (hp x hx)) h

 theorem pairing_equiv_matching_pair
    {V : Type u} {W : Type v} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ V] [FiniteDimensional ℝ W]
    (B : LinearMap.BilinForm ℝ V) (D : LinearMap.BilinForm ℝ W)
    (hBs : ∀ x y, B x y = B y x) (hBp : ∀ x, x ≠ 0 → 0 < B x x)
    (hDs : ∀ x y, D x y = D y x) (hDp : ∀ x, x ≠ 0 → 0 < D x x)
    (hdim : finrank ℝ V = finrank ℝ W)
    (x₁ x₂ : V) (y₁ y₂ : W)
    (hx₁ : B x₁ x₁ = 1) (hx₂ : B x₂ x₂ = 1) (hx₁₂ : B x₁ x₂ = 0)
    (hy₁ : D y₁ y₁ = 1) (hy₂ : D y₂ y₂ = 1) (hy₁₂ : D y₁ y₂ = 0) :
    ∃ e : V ≃ₗ[ℝ] W, e x₁ = y₁ ∧ e x₂ = y₂ ∧ ∀ x y, D (e x) (e y) = B x y := by
  let cV := realInnerCore B hBs hBp
  let cW := realInnerCore D hDs hDp
  letI : NormedAddCommGroup V := cV.toNormedAddCommGroup
  letI : InnerProductSpace ℝ V := InnerProductSpace.ofCore cV.toCore
  letI : NormedAddCommGroup W := cW.toNormedAddCommGroup
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore cW.toCore
  let e₀ : V ≃ₗᵢ[ℝ] W :=
    (stdOrthonormalBasis ℝ V).repr.trans
      ((stdOrthonormalBasis ℝ W).reindex (finCongr hdim.symm)).repr.symm
  have hxnorm₁ : ‖x₁‖ = 1 := by
    change Real.sqrt (B x₁ x₁) = 1
    rw [hx₁, Real.sqrt_one]
  have hynorm₁ : ‖y₁‖ = 1 := by
    change Real.sqrt (D y₁ y₁) = 1
    rw [hy₁, Real.sqrt_one]
  have hxnorm₂ : ‖x₂‖ = 1 := by
    change Real.sqrt (B x₂ x₂) = 1
    rw [hx₂, Real.sqrt_one]
  have hynorm₂ : ‖y₂‖ = 1 := by
    change Real.sqrt (D y₂ y₂) = 1
    rw [hy₂, Real.sqrt_one]
  let r₁ : W ≃ₗᵢ[ℝ] W := (ℝ ∙ (e₀ x₁ - y₁))ᗮ.reflection
  let e₁ := e₀.trans r₁
  have he₁ : e₁ x₁ = y₁ := Submodule.reflection_sub (by simp only [e₀.norm_map, hxnorm₁, hynorm₁])
  have horth : inner ℝ y₁ (e₁ x₂) = 0 := by
    rw [← he₁, e₁.inner_map_map]
    exact hx₁₂
  let r₂ : W ≃ₗᵢ[ℝ] W := (ℝ ∙ (e₁ x₂ - y₂))ᗮ.reflection
  have hr₂ : r₂ y₁ = y₁ := by
    apply Submodule.reflection_mem_subspace_eq_self
    rw [Submodule.mem_orthogonal_singleton_iff_inner_left]
    rw [inner_sub_right, horth]
    change 0 - D y₁ y₂ = 0
    rw [hy₁₂, sub_self]
  have he₂ : r₂ (e₁ x₂) = y₂ := Submodule.reflection_sub (by simp only [e₁.norm_map, hxnorm₂, hynorm₂])
  let e := e₁.trans r₂
  refine ⟨e.toLinearEquiv, ?_, he₂, fun x y => e.inner_map_map x y⟩
  change r₂ (e₁ x₁) = y₁
  rw [he₁, hr₂]

/-- Coordinates of any parallel field are constant on the affine domain. -/
theorem parallel_coordinates_constant
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (hP : ∀ x, ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => P s x) t 0)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun s => (q s).1) J t 0)
    {a t : ℝ} (ha : a ∈ I.carrier) (ht : t ∈ I.carrier) :
    (P t).symm (J t) = (P a).symm (J a) := by
  let j : ℝ → Euclidean n := fun s => (P s).symm (J s)
  have hd (s : ℝ) (hs : s ∈ I.carrier) : HasDerivAt j 0 s := by
    apply (JacobiIVP.derivative_parallel_equiv C P (hq s hs).1
      (fun i => hP (Pi.single i 1) s hs) j 0).mpr
    simpa only [j, LinearEquiv.apply_symm_apply, map_zero] using hJ s hs
  exact I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht ha

/-- A single constant map between parallel coordinate spaces preserves the
metrics, the radial velocities and a prescribed terminal normal unit vector. -/
theorem exists_parallel_matching_map {N : Type u} [TopologicalSpace N]
    {Sbar : SmoothManifold n .euclidean N}
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (Pbar : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace Sbar (qbar t).1)
    (hP : ∀ x, ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun s => (q s).1) (fun s => P s x) t 0)
    (hPbar : ∀ x, ∀ t ∈ Ibar.carrier,
      HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) (fun s => Pbar s x) t 0)
    (b : ℝ) (hb : b ∈ I.carrier) (hbbar : b ∈ Ibar.carrier)
    (hunit : pairing g (q b).1 (q b).2 (q b).2 = 1)
    (hunitbar : pairing gbar (qbar b).1 (qbar b).2 (qbar b).2 = 1)
    (v : TangentSpace S (q b).1) (vbar : TangentSpace Sbar (qbar b).1)
    (hv : pairing g (q b).1 v v = 1) (hvbar : pairing gbar (qbar b).1 vbar vbar = 1)
    (hvn : pairing g (q b).1 v (q b).2 = 0)
    (hvnb : pairing gbar (qbar b).1 vbar (qbar b).2 = 0) :
    ∃ L : Euclidean n →ₗ[ℝ] Euclidean n,
      (∀ t ∈ I.carrier, ∀ htbar : t ∈ Ibar.carrier, ∀ x y,
        pairing gbar (qbar t).1 (Pbar t (L x)) (Pbar t (L y)) =
          pairing g (q t).1 (P t x) (P t y)) ∧
      (∀ t ∈ I.carrier, ∀ htbar : t ∈ Ibar.carrier,
        Pbar t (L ((P t).symm (q t).2)) = (qbar t).2) ∧
      Pbar b (L ((P b).symm v)) = vbar := by
  let B : LinearMap.BilinForm ℝ (Euclidean n) :=
    (pairing g (q b).1).compl₁₂ (P b).toLinearMap (P b).toLinearMap
  let D : LinearMap.BilinForm ℝ (Euclidean n) :=
    (pairing gbar (qbar b).1).compl₁₂ (Pbar b).toLinearMap (Pbar b).toLinearMap
  have hBs : ∀ x y, B x y = B y x := fun x y => g.symmetric _ _ _
  have hDs : ∀ x y, D x y = D y x := fun x y => gbar.symmetric _ _ _
  have hBp : ∀ x, x ≠ 0 → 0 < B x x := by
    intro x hx
    apply g.positive
    intro hz
    exact hx ((P b).injective (hz.trans (map_zero (P b)).symm))
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := by
    intro x hx
    apply gbar.positive
    intro hz
    exact hx ((Pbar b).injective (hz.trans (map_zero (Pbar b)).symm))
  have horth : B ((P b).symm (q b).2) ((P b).symm v) = 0 := by
    simpa only [B, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, pairing] using (g.symmetric _ (q b).2 v).trans hvn
  have horthbar : D ((Pbar b).symm (qbar b).2) ((Pbar b).symm vbar) = 0 := by
    simpa only [D, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply, pairing] using (gbar.symmetric _ (qbar b).2 vbar).trans hvnb
  obtain ⟨e, heT, hev, he⟩ := pairing_equiv_matching_pair B D hBs hBp hDs hDp rfl
    ((P b).symm (q b).2) ((P b).symm v)
    ((Pbar b).symm (qbar b).2) ((Pbar b).symm vbar)
    (by simpa only [B, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using hunit)
    (by simpa only [B, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using hv) horth
    (by simpa only [D, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using hunitbar)
    (by simpa only [D, LinearMap.compl₁₂_apply, LinearEquiv.coe_toLinearMap,
      LinearEquiv.apply_symm_apply] using hvbar) horthbar
  refine ⟨e.toLinearMap, ?_, ?_, ?_⟩
  · intro t ht htbar x y
    exact (parallel_equiv_pairing_constant gbar Cbar hCbar Ibar qbar Pbar hPbar hbbar htbar
      (e x) (e y)).trans ((he x y).trans
      (parallel_equiv_pairing_constant g C hC I q P hP hb ht x y).symm)
  · intro t ht htbar
    have hT := parallel_coordinates_constant C I q hq P hP (fun s => (q s).2)
      (fun s hs => (hq s hs).2) hb ht
    have hTbar := parallel_coordinates_constant Cbar Ibar qbar hqbar Pbar hPbar
      (fun s => (qbar s).2) (fun s hs => (hqbar s hs).2) hbbar htbar
    change Pbar t (e ((P t).symm (q t).2)) = _
    rw [hT, heT, ← hTbar, LinearEquiv.apply_symm_apply]
  · change Pbar b (e ((P b).symm v)) = vbar
    rw [hev, LinearEquiv.apply_symm_apply]

/-- A metric map taking radial velocities to radial velocities preserves
normality of every field. -/
theorem normal_of_parallel_matching_map {N : Type u} [TopologicalSpace N]
    {Sbar : SmoothManifold n .euclidean N}
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (Pbar : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace Sbar (qbar t).1)
    (L : Euclidean n →ₗ[ℝ] Euclidean n) {U : Set ℝ}
    (hm : ∀ t ∈ U, ∀ x y,
      pairing gbar (qbar t).1 (Pbar t (L x)) (Pbar t (L y)) =
        pairing g (q t).1 (P t x) (P t y))
    (hT : ∀ t ∈ U, Pbar t (L ((P t).symm (q t).2)) = (qbar t).2)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hn : ∀ t ∈ U, pairing g (q t).1 (J t) (q t).2 = 0) :
    ∀ t ∈ U, pairing gbar (qbar t).1
      (Pbar t (L ((P t).symm (J t)))) (qbar t).2 = 0 := by
  intro t ht
  rw [← hT t ht, hm t ht, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply, hn t ht]

/-- A single closed C¹ piece is an admissible piecewise C¹ competitor. -/
theorem piecewiseC1_of_c1 {c : ℝ → M}
    {W : (t : ℝ) → TangentSpace S (c t)} {b : ℝ} (hb : 0 < b)
    (hW : C1FieldOn (B := tangentBundle S) c W (Icc 0 b)) :
    PiecewiseC1FieldOn c W 0 b := by
  let node : Fin 2 → ℝ := ![0,b]
  refine ⟨0,node,?_,rfl,rfl,?_⟩
  · intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [node]
  · intro i
    fin_cases i
    exact hW


/-- The full index lemma compares against any specified Jacobi field with
matching endpoints, because its constructed minimizer is unique. -/
theorem indexForm_le_of_jacobi
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    {b : ℝ} (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier)
    (hnc : ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
      ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩)
    (K V : (t : ℝ) → TangentSpace S (q t).1)
    (hK : IsJacobiField C R I.carrier q K) (hK0 : K 0 = 0)
    (hV : PiecewiseC1FieldOn (fun t => (q t).1) V 0 b)
    (hV0 : V 0 = 0) (hVb : V b = K b) :
    indexForm g C R (fun t => (q t).1) 0 b K K ≤
      indexForm g C R (fun t => (q t).1) 0 b V V := by
  obtain ⟨J,hJ,hJ0,hJb,hunique,hmin⟩ :=
    IndexLemma.index_lemma S g C hC R hR I q hq h0 b hb hsub hnc (K b)
  have heq := hunique K hK hK0 rfl
  have hsplit := IndexLemma.indexForm_split_jacobi g C hC R hR I q hq hb hsub hJ
    (piecewiseC1_of_c1 hb
      (IndexLemma.c1FieldOn_mono (IndexLemma.jacobi_c1FieldOn C R I q hq hK) hsub))
    (hK0.trans hJ0.symm)
    hJb.symm
  have hz := IndexLemma.indexForm_eq_zero_of_eqOn_zero g C R I q hq hb hsub
    (V := fun t => K t - J t) (fun t ht => sub_eq_zero.mpr (heq t (hsub ht)))
  have hi : indexForm g C R (fun t => (q t).1) 0 b K K =
      indexForm g C R (fun t => (q t).1) 0 b J J := by linarith
  rw [hi]
  exact (hmin V hV hV0 hVb).1

/-- C¹ coordinate coefficients and C¹ frame columns give a C¹ intrinsic field. -/
theorem c1FieldOn_equiv_expansion
    {c : ℝ → M} {U : Set ℝ}
    (hc1 : P202.CurveData.CoordinateC1On S c U) (hc : ContinuousOn c U)
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    (hP : ∀ i : Fin n, C1FieldOn (B := tangentBundle S) c
      (fun s => P s (Pi.single i 1)) U)
    (x : ℝ → Euclidean n) (hx : ∀ t ∈ U, ContDiffAt ℝ 1 x t) :
    C1FieldOn (B := tangentBundle S) c (fun s => P s (x s)) U := by
  intro t ht
  obtain ⟨O,hO,hp,⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) (c t)
  choose v hv heq using (fun i => IndexLemma.c1_coefficients_in_frame hc1 hc (hP i) b ht hp)
  let a : ℝ → Euclidean n := fun s => ∑ i : Fin n, x s i • v i s
  have ha : ContDiffAt ℝ 1 a t := by
    apply ContDiffAt.sum
    intro i _
    exact ((contDiff_apply ℝ (fun _ : Fin n => ℝ) i).contDiffAt.comp t (hx t ht)).smul (hv i)
  have heqa : coefficientsAlong b c (fun s => P s (x s)) =ᶠ[𝓝[U] t] a := by
    filter_upwards [Filter.eventually_all.mpr heq,
      (hc t ht).eventually (hO.mem_nhds hp)] with s hs hsp
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b c _ s hsp]
    rw [JacobiIVP.equivalence_expansion (P s) (x s)]
    simp only [map_sum, map_smul, a]
    apply Finset.sum_congr rfl
    intro i _
    rw [← hs i, CurveCovariantDerivative.coefficientsAlong_of_mem b c _ s hsp]
  exact ⟨O,hO,b,hp,a,ha,heqa.self_of_nhdsWithin ht,heqa⟩


/-- Jacobi coefficients in an arbitrary actual parallel equivalence are C¹. -/
theorem jacobi_parallel_coordinates_c1
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q s).1)
    (hP : ∀ x, ∀ s ∈ I.carrier, HasCovariantDerivativeAt C (fun r => (q r).1)
      (fun r => P r x) s 0)
    {J : (s : ℝ) → TangentSpace S (q s).1}
    (hJ : IsJacobiField C R I.carrier q J) :
    ∀ t ∈ I.carrier, ContDiffAt ℝ 1 (fun s => (P s).symm (J s)) t := by
  intro t ht
  have hc : ContinuousOn (fun s => (q s).1) I.carrier :=
    fun s hs => ((hq s hs).1.1.continuousAt (by simp)).continuousWithinAt
  obtain ⟨v,hv,heq⟩ := IndexLemma.inverse_coordinates_c1_germ
    (JacobiIVP.geodesic_coordinateC1 C I q hq) hc P
    (fun i => IndexLemma.parallel_c1FieldOn C I q hq (hP (Pi.single i 1)))
    (IndexLemma.jacobi_c1FieldOn C R I q hq hJ) ht
    ((hq t ht).1.1.continuousAt (by simp))
  rw [nhdsWithin_eq_nhds.mpr (I.isOpen.mem_nhds ht)] at heq
  exact hv.congr_of_eventuallyEq heq

variable {N : Type u} [TopologicalSpace N]
    {Sbar : SmoothManifold n .euclidean N}

/-- Transporting a normal Jacobi competitor by an actual parallel metric map
compares its index form to that of the higher-curvature Jacobi minimizer. -/
theorem index_transfer_le
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    {b : ℝ} (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier)
    (hbarsub : Icc 0 b ⊆ Ibar.carrier)
    (hbound : RadialSectionalBound g gbar R Rbar q qbar (Icc 0 b))
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q s).1)
    (Pbar : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace Sbar (qbar s).1)
    (hP : ∀ x, ∀ s ∈ I.carrier, HasCovariantDerivativeAt C (fun r => (q r).1)
      (fun r => P r x) s 0)
    (hPbar : ∀ x, ∀ s ∈ Ibar.carrier,
      HasCovariantDerivativeAt Cbar (fun r => (qbar r).1) (fun r => Pbar r x) s 0)
    (L : Euclidean n →ₗ[ℝ] Euclidean n)
    (hL : ∀ s ∈ Icc 0 b, ∀ x y,
      pairing gbar (qbar s).1 (Pbar s (L x)) (Pbar s (L y)) =
        pairing g (q s).1 (P s x) (P s y))
    (J : (s : ℝ) → TangentSpace S (q s).1)
    (hJ : IsJacobiField C R I.carrier q J)
    (hJn : NormalFieldOn g q J (Icc 0 b))
    (hVn : NormalFieldOn gbar qbar
      (fun s => Pbar s (L ((P s).symm (J s)))) (Icc 0 b))
    : C1FieldOn (B := tangentBundle Sbar) (fun s => (qbar s).1)
        (fun s => Pbar s (L ((P s).symm (J s)))) (Icc 0 b) ∧
      indexForm gbar Cbar Rbar (fun s => (qbar s).1) 0 b
        (fun s => Pbar s (L ((P s).symm (J s))))
        (fun s => Pbar s (L ((P s).symm (J s)))) ≤
      indexForm g C R (fun s => (q s).1) 0 b J J := by
  let x : ℝ → Euclidean n := fun s => (P s).symm (J s)
  let V : (s : ℝ) → TangentSpace Sbar (qbar s).1 := fun s => Pbar s (L (x s))
  let U : Set ℝ := I.carrier ∩ Ibar.carrier
  have hU : IsOpen U := I.isOpen.inter Ibar.isOpen
  have hUsub : Icc 0 b ⊆ U := fun s hs => ⟨hsub hs,hbarsub hs⟩
  have hx := jacobi_parallel_coordinates_c1 C R I q hq P hP hJ
  have hVbig : C1FieldOn (B := tangentBundle Sbar) (fun s => (qbar s).1) V U := by
    apply c1FieldOn_equiv_expansion
      (PiecewiseCurves.CoordinateC1On.mono
        (JacobiIVP.geodesic_coordinateC1 Cbar Ibar qbar hqbar) inter_subset_right)
      (fun s hs => ((hqbar s hs.2).1.1.continuousAt (by simp)).continuousWithinAt)
      Pbar
      (fun i => IndexLemma.c1FieldOn_mono
        (IndexLemma.parallel_c1FieldOn Cbar Ibar qbar hqbar (hPbar (Pi.single i 1)))
        inter_subset_right)
      (fun s => L (x s))
    intro s hs
    exact L.toContinuousLinearMap.contDiff.contDiffAt.comp s (hx s hs.1)
  have hV := IndexLemma.c1FieldOn_mono hVbig hUsub
  have hJc := IndexLemma.c1FieldOn_mono (IndexLemma.jacobi_c1FieldOn C R I q hq hJ) hsub
  refine ⟨hV, ?_⟩
  apply intervalIntegral.integral_mono_on hb.le
    (SecondVariation.indexIntegrand_intervalIntegrable gbar Cbar Rbar hb
      (IndexLemma.geodesic_smoothVariation Cbar Ibar qbar hqbar hbarsub) hV hV)
    (SecondVariation.indexIntegrand_intervalIntegrable g C R hb
      (IndexLemma.geodesic_smoothVariation C I q hq hsub) hJc hJc)
  intro s hs
  obtain ⟨D,hD⟩ := hJ
  have hxD : HasDerivAt x ((P s).symm (D s)) s := by
    apply (JacobiIVP.derivative_parallel_equiv C P (hq s (hsub hs)).1
      (fun i => hP (Pi.single i 1) s (hsub hs)) x ((P s).symm (D s))).mpr
    simpa only [x,LinearEquiv.apply_symm_apply] using (hD s (hsub hs)).1
  have hVD : HasCovariantDerivativeAt Cbar (fun r => (qbar r).1) V s
      (Pbar s (L ((P s).symm (D s)))) := by
    apply JacobiIVP.derivative_parallel_expansion Cbar Pbar (hqbar s (hbarsub hs)).1
      (fun i => hPbar (Pi.single i 1) s (hbarsub hs))
    exact L.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt s hxD
  have hJDval := CurveCovariantDerivative.covariantDerivativeWithin_eq C hs
    (uniqueDiffOn_Icc hb s hs)
    (ParallelTransport.covariantDerivative_mono (hD s (hsub hs)).1 (subset_univ (Icc 0 b)))
  have hVDval := CurveCovariantDerivative.covariantDerivativeWithin_eq Cbar hs
    (uniqueDiffOn_Icc hb s hs)
    (ParallelTransport.covariantDerivative_mono hVD (subset_univ (Icc 0 b)))
  have hnorm : tangentNorm g (q s).1 (J s) = tangentNorm gbar (qbar s).1 (V s) := by
    unfold tangentNorm
    congr 1
    simpa only [V,x,LinearEquiv.apply_symm_apply] using
      (hL s hs ((P s).symm (J s)) ((P s).symm (J s))).symm
  have hc := radial_quadratic_comparison g gbar C Cbar hC hCbar R Rbar hR hRbar
    q qbar (Icc 0 b) hbound s hs (J s) (V s) (hJn s hs) (hVn s hs) hnorm
  have hderiv : pairing gbar (qbar s).1
      (Pbar s (L ((P s).symm (D s)))) (Pbar s (L ((P s).symm (D s)))) =
        pairing g (q s).1 (D s) (D s) := by
    simpa only [LinearEquiv.apply_symm_apply] using
      hL s hs ((P s).symm (D s)) ((P s).symm (D s))
  simp only [indexIntegrand,hJDval,hVDval,
    IndexLemma.segmentTangent_eq_phase C I q hq hb hsub hs,
    IndexLemma.segmentTangent_eq_phase Cbar Ibar qbar hqbar hb hbarsub hs,
    hderiv]
  exact sub_le_sub_left hc _


theorem index_compare_of_parallel_map
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier)
    {b : ℝ} (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier)
    (hbarsub : Icc 0 b ⊆ Ibar.carrier)
    (hbound : RadialSectionalBound g gbar R Rbar q qbar (Icc 0 b))
    (hnc : ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ Ibar.carrier,
      ¬ ConjugateAlong Sbar Cbar Rbar Ibar qbar ⟨0,hbar0⟩ ⟨t,ht⟩)
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q s).1)
    (Pbar : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace Sbar (qbar s).1)
    (hP : ∀ x, ∀ s ∈ I.carrier, HasCovariantDerivativeAt C (fun r => (q r).1)
      (fun r => P r x) s 0)
    (hPbar : ∀ x, ∀ s ∈ Ibar.carrier,
      HasCovariantDerivativeAt Cbar (fun r => (qbar r).1) (fun r => Pbar r x) s 0)
    (L : Euclidean n →ₗ[ℝ] Euclidean n)
    (hL : ∀ s ∈ Icc 0 b, ∀ x y,
      pairing gbar (qbar s).1 (Pbar s (L x)) (Pbar s (L y)) =
        pairing g (q s).1 (P s x) (P s y))
    (J : (s : ℝ) → TangentSpace S (q s).1)
    (K : (s : ℝ) → TangentSpace Sbar (qbar s).1)
    (hJ : IsJacobiField C R I.carrier q J)
    (hK : IsJacobiField Cbar Rbar Ibar.carrier qbar K)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0)
    (hJn : NormalFieldOn g q J (Icc 0 b))
    (hVn : NormalFieldOn gbar qbar
      (fun s => Pbar s (L ((P s).symm (J s)))) (Icc 0 b))
    (hmatch : Pbar b (L ((P b).symm (J b))) = K b) :
    indexForm gbar Cbar Rbar (fun s => (qbar s).1) 0 b K K ≤
      indexForm g C R (fun s => (q s).1) 0 b J J := by
  let V : (s : ℝ) → TangentSpace Sbar (qbar s).1 :=
    fun s => Pbar s (L ((P s).symm (J s)))
  obtain ⟨hV,hi⟩ := index_transfer_le g gbar C Cbar hC hCbar R Rbar hR hRbar
    I Ibar q qbar hq hqbar hb hsub hbarsub hbound P Pbar hP hPbar L hL J hJ hJn hVn
  have hV0 : V 0 = 0 := by simp only [V,hJ0,map_zero]
  have hmin := indexForm_le_of_jacobi gbar Cbar hCbar Rbar hRbar Ibar qbar hqbar hbar0
    hb hbarsub hnc K V hK hK0 (piecewiseC1_of_c1 hb hV) hV0 hmatch
  exact hmin.trans hi


theorem terminal_pairing_compare_of_parallel_map
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier)
    {b : ℝ} (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier)
    (hbarsub : Icc 0 b ⊆ Ibar.carrier)
    (hbound : RadialSectionalBound g gbar R Rbar q qbar (Icc 0 b))
    (hnc : ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ Ibar.carrier,
      ¬ ConjugateAlong Sbar Cbar Rbar Ibar qbar ⟨0,hbar0⟩ ⟨t,ht⟩)
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q s).1)
    (Pbar : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace Sbar (qbar s).1)
    (hP : ∀ x, ∀ s ∈ I.carrier, HasCovariantDerivativeAt C (fun r => (q r).1)
      (fun r => P r x) s 0)
    (hPbar : ∀ x, ∀ s ∈ Ibar.carrier,
      HasCovariantDerivativeAt Cbar (fun r => (qbar r).1) (fun r => Pbar r x) s 0)
    (L : Euclidean n →ₗ[ℝ] Euclidean n)
    (hL : ∀ s ∈ Icc 0 b, ∀ x y,
      pairing gbar (qbar s).1 (Pbar s (L x)) (Pbar s (L y)) =
        pairing g (q s).1 (P s x) (P s y))
    (J : (s : ℝ) → TangentSpace S (q s).1)
    (K : (s : ℝ) → TangentSpace Sbar (qbar s).1)
    (hJ : IsJacobiField C R I.carrier q J)
    (hK : IsJacobiField Cbar Rbar Ibar.carrier qbar K)
    (hJ0 : J 0 = 0) (hK0 : K 0 = 0)
    (hJn : NormalFieldOn g q J (Icc 0 b))
    (hVn : NormalFieldOn gbar qbar
      (fun s => Pbar s (L ((P s).symm (J s)))) (Icc 0 b))
    (hmatch : Pbar b (L ((P b).symm (J b))) = K b) :
    pairing gbar (qbar b).1
      (covariantDerivative Cbar (fun s => (qbar s).1) K b) (K b) ≤
    pairing g (q b).1 (covariantDerivative C (fun s => (q s).1) J b) (J b) := by
  have hi := index_compare_of_parallel_map g gbar C Cbar hC hCbar R Rbar hR hRbar
    I Ibar q qbar hq hqbar h0 hbar0 hb hsub hbarsub hbound hnc
    P Pbar hP hPbar L hL J K hJ hK hJ0 hK0 hJn hVn hmatch
  rw [IndexLemma.jacobi_green_identity gbar Cbar hCbar Rbar Ibar qbar hqbar hb hbarsub hK
    (IndexLemma.c1FieldOn_mono (IndexLemma.jacobi_c1FieldOn Cbar Rbar Ibar qbar hqbar hK) hbarsub),
    IndexLemma.jacobi_green_identity g C hC R I q hq hb hsub hJ
    (IndexLemma.c1FieldOn_mono (IndexLemma.jacobi_c1FieldOn C R I q hq hJ) hsub)] at hi
  simpa only [hJ0,hK0,map_zero,sub_zero] using hi


/-- Integrating the normalized terminal-pairing comparison does not require
nonconjugacy of the lower-curvature geodesic. -/
theorem norm_comparison_of_terminal_pairing
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier)
    (b : ℝ) (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier) (hsubbar : Icc 0 b ⊆ Ibar.carrier)
    (hnc : ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ Ibar.carrier,
      ¬ ConjugateAlong Sbar Cbar Rbar Ibar qbar ⟨0,hbar0⟩ ⟨t,ht⟩)
    (hterminal : ∀ (K : (s : ℝ) → TangentSpace S (q s).1)
      (Kbar : (s : ℝ) → TangentSpace Sbar (qbar s).1),
      IsJacobiField C R I.carrier q K → IsJacobiField Cbar Rbar Ibar.carrier qbar Kbar →
      K 0 = 0 → Kbar 0 = 0 →
      NormalFieldOn g q K (Icc 0 b) → NormalFieldOn gbar qbar Kbar (Icc 0 b) →
      ∀ t ∈ Ioc 0 b,
      tangentNorm g (q t).1 (K t) = 1 → tangentNorm gbar (qbar t).1 (Kbar t) = 1 →
      pairing gbar (qbar t).1 (covariantDerivative Cbar (fun s => (qbar s).1) Kbar t) (Kbar t) ≤
      pairing g (q t).1 (covariantDerivative C (fun s => (q s).1) K t) (K t))
    (J : (s : ℝ) → TangentSpace S (q s).1)
    (Jbar : (s : ℝ) → TangentSpace Sbar (qbar s).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJbar : IsJacobiField Cbar Rbar Ibar.carrier qbar Jbar)
    (hJ0 : J 0 = 0) (hJbar0 : Jbar 0 = 0)
    (hJn : NormalFieldOn g q J (Icc 0 b)) (hJbarn : NormalFieldOn gbar qbar Jbar (Icc 0 b))
    (w : TangentSpace S (q 0).1) (wbar : TangentSpace Sbar (qbar 0).1)
    (hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w)
    (hdJbar : HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) Jbar 0 wbar)
    (hn : tangentNorm g (q 0).1 w = tangentNorm gbar (qbar 0).1 wbar) :
    ∀ t ∈ Icc 0 b, tangentNorm gbar (qbar t).1 (Jbar t) ≤ tangentNorm g (q t).1 (J t) := by
  by_cases hw : w = 0
  · intro t ht
    exact (zero_initial_comparison g gbar C Cbar hC hCbar R Rbar hR hRbar
      I Ibar q qbar hq hqbar h0 hbar0 J Jbar hJ hJbar hJ0 hJbar0
      w wbar hdJ hdJbar hn hw t ⟨hsub ht,hsubbar ht⟩).le
  have hwbar : wbar ≠ 0 := by
    intro hz
    apply hw
    apply (SmoothMetrics.tangentNorm_eq_zero_iff g (q 0).1 w).mp
    rw [hn, hz, SmoothMetrics.tangentNorm_zero]
  obtain ⟨D,hD⟩ := hJ
  obtain ⟨Dbar,hDbar⟩ := hJbar
  have hJ : IsJacobiField C R I.carrier q J := ⟨D,hD⟩
  have hJbar : IsJacobiField Cbar Rbar Ibar.carrier qbar Jbar := ⟨Dbar,hDbar⟩
  have hpos (t : ℝ) (ht : t ∈ Ioc 0 b) : 0 < tangentNorm gbar (qbar t).1 (Jbar t) :=
    jacobi_norm_pos gbar Cbar Rbar Ibar qbar hqbar hbar0 Jbar hJbar hJbar0
      wbar hdJbar hwbar t (hsubbar ⟨ht.1.le,ht.2⟩) (hnc t ht _)
  have hf (t : ℝ) (ht : t ∈ Ioc 0 b) :=
    square_norm_hasDerivAt g C hC q J t (D t) (hD t (hsub ⟨ht.1.le,ht.2⟩)).1
  have hg (t : ℝ) (ht : t ∈ Ioc 0 b) :=
    square_norm_hasDerivAt gbar Cbar hCbar qbar Jbar t (Dbar t)
      (hDbar t (hsubbar ⟨ht.1.le,ht.2⟩)).1
  have hcross (t : ℝ) (ht : t ∈ Ioc 0 b) :
      0 ≤ (2 * pairing g (q t).1 (D t) (J t)) * tangentNorm gbar (qbar t).1 (Jbar t)^2 -
        tangentNorm g (q t).1 (J t)^2 * (2 * pairing gbar (qbar t).1 (Dbar t) (Jbar t)) := by
    by_cases hz : J t = 0
    · simp only [hz, SmoothMetrics.tangentNorm_zero, map_zero, mul_zero, zero_pow (by decide : 2 ≠ 0),
        zero_mul, sub_self, le_refl]
    have hp : 0 < tangentNorm g (q t).1 (J t) := Real.sqrt_pos.mpr (g.positive _ _ hz)
    let a := (tangentNorm g (q t).1 (J t))⁻¹
    let abar := (tangentNorm gbar (qbar t).1 (Jbar t))⁻¹
    have hK := JacobiIVP.jacobi_smul C R hJ a
    have hKbar := JacobiIVP.jacobi_smul Cbar Rbar hJbar abar
    have hunit : tangentNorm g (q t).1 (a • J t) = 1 := by
      rw [SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ (ne_of_gt hp)]
    have hunitbar : tangentNorm gbar (qbar t).1 (abar • Jbar t) = 1 := by
      rw [SmoothMetrics.tangentNorm_smul, abs_of_pos (inv_pos.mpr (hpos t ht)), inv_mul_cancel₀ (ne_of_gt (hpos t ht))]
    have hterm := hterminal (fun s => a • J s) (fun s => abar • Jbar s) hK hKbar
      (by rw [hJ0,smul_zero]) (by rw [hJbar0,smul_zero])
      (fun s hs => by rw [LinearMap.BilinForm.smul_left,hJn s hs,mul_zero])
      (fun s hs => by rw [LinearMap.BilinForm.smul_left,hJbarn s hs,mul_zero]) t ht hunit hunitbar
    have hda := CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ t)
      uniqueDiffWithinAt_univ (CurveCovariantDerivative.derivative_const_smul C
        (hD t (hsub ⟨ht.1.le,ht.2⟩)).1 a)
    have hdabar := CurveCovariantDerivative.covariantDerivativeWithin_eq Cbar (mem_univ t)
      uniqueDiffWithinAt_univ (CurveCovariantDerivative.derivative_const_smul Cbar
        (hDbar t (hsubbar ⟨ht.1.le,ht.2⟩)).1 abar)
    change covariantDerivative C (fun s => (q s).1) (fun s => a • J s) t = a • D t at hda
    change covariantDerivative Cbar (fun s => (qbar s).1) (fun s => abar • Jbar s) t = abar • Dbar t at hdabar
    rw [hda,hdabar,LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right,
      LinearMap.BilinForm.smul_left,LinearMap.BilinForm.smul_right] at hterm
    have hterm' : pairing gbar (qbar t).1 (Dbar t) (Jbar t) / tangentNorm gbar (qbar t).1 (Jbar t)^2 ≤
        pairing g (q t).1 (D t) (J t) / tangentNorm g (q t).1 (J t)^2 := by
      convert hterm using 1 <;> dsimp [a,abar] <;> simp only [div_eq_mul_inv,inv_pow] <;> ring
    have hmul := (div_le_div_iff₀ (sq_pos_of_pos (hpos t ht)) (sq_pos_of_pos hp)).mp hterm'
    nlinarith
  have hlim : Tendsto (fun t => tangentNorm g (q t).1 (J t)^2 / tangentNorm gbar (qbar t).1 (Jbar t)^2)
      (𝓝[>] 0) (𝓝 1) := by
    simpa only [div_pow,one_pow] using
      (jacobi_norm_ratio_tendsto g gbar C Cbar hC hCbar I Ibar q qbar hq hqbar
        h0 hbar0 J Jbar hJ0 hJbar0 w wbar hdJ hdJbar hn hw).pow 2
  have hsq := comparison_of_cross_derivative (fun t ht => sq_pos_of_pos (hpos t ht)) hf hg hcross hlim
  intro t ht
  by_cases ht0 : t = 0
  · subst t
    rw [hJ0,hJbar0,SmoothMetrics.tangentNorm_zero,SmoothMetrics.tangentNorm_zero]
  have ht' : t ∈ Ioc 0 b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
  exact (sq_le_sq₀ (SmoothMetrics.tangentNorm_nonneg _ _ _) (SmoothMetrics.tangentNorm_nonneg _ _ _)).mp (hsq t ht')

lemma exists_kernel_vector (n : ℕ) (hn : 2 ≤ n) (L : (Fin n → ℝ) →ₗ[ℝ] ℝ) :
    ∃ v : Fin n → ℝ, v ≠ 0 ∧ L v = 0 := by
  classical
  let i : Fin n := ⟨0, Nat.lt_of_lt_of_le (by decide : 0 < 2) hn⟩
  let j : Fin n := ⟨1, Nat.lt_of_lt_of_le (by decide : 1 < 2) hn⟩
  have hij : i ≠ j := by simp [i, j]
  let e : Fin n → ℝ := Pi.single i 1
  let f : Fin n → ℝ := Pi.single j 1
  by_cases he : L e = 0
  · refine ⟨e, ?_, he⟩
    intro h
    have hh := congrFun h i
    simp [e] at hh
  · refine ⟨L e • f - L f • e, ?_, ?_⟩
    · intro h
      have hh := congrFun h j
      exact he (by simpa [e, f, hij, hij.symm] using hh)
    · simp only [map_sub, map_smul, smul_eq_mul]
      exact sub_eq_zero.mpr (mul_comm _ _)

lemma exists_normal_of_norm (hn : 2 ≤ n) (g : RiemannianMetric S)
    (p : M) (P : Euclidean n ≃ₗ[ℝ] TangentSpace S p)
    (T : TangentSpace S p) (a : ℝ) (ha : 0 ≤ a) :
    ∃ w : TangentSpace S p, pairing g p w T = 0 ∧ tangentNorm g p w = a := by
  let L : Euclidean n →ₗ[ℝ] ℝ := ((pairing g p).flip T).comp P.toLinearMap
  obtain ⟨v, hv, hLv⟩ := exists_kernel_vector n hn L
  have hPv : P v ≠ 0 := by exact fun h => hv (P.injective (h.trans (map_zero P).symm))
  have hpos : 0 < tangentNorm g p (P v) := Real.sqrt_pos.mpr (g.positive p (P v) hPv)
  refine ⟨(a / tangentNorm g p (P v)) • P v, ?_, ?_⟩
  · rw [LinearMap.BilinForm.smul_left]
    change a / tangentNorm g p (P v) * L v = 0
    rw [hLv, mul_zero]
  · rw [SmoothMetrics.tangentNorm_smul, abs_of_nonneg (div_nonneg ha hpos.le),
      div_mul_cancel₀ _ (ne_of_gt hpos)]

lemma nonconjugacy_of_norm_comparison {N : Type u} [TopologicalSpace N]
    {Sbar : SmoothManifold n .euclidean N} (hn : 2 ≤ n)
    (g : RiemannianMetric S) (gbar : RiemannianMetric Sbar)
    (C : Connection (tangentBundle S)) (Cbar : Connection (tangentBundle Sbar))
    (hC : IsLeviCivita g C) (hCbar : IsLeviCivita gbar Cbar)
    (R : CurvatureTensor S) (Rbar : CurvatureTensor Sbar)
    (hR : RepresentsCurvature C R) (hRbar : RepresentsCurvature Cbar Rbar)
    (I Ibar : D13Unified.OpenTimeInterval) (q : ℝ → Phase S) (qbar : ℝ → Phase Sbar)
    (hq : IsGeodesicOn S C I.carrier q) (hqbar : IsGeodesicOn Sbar Cbar Ibar.carrier qbar)
    (h0 : 0 ∈ I.carrier) (hbar0 : 0 ∈ Ibar.carrier) (b : ℝ)
    (hbI : Icc 0 b ⊆ I.carrier) (hbIbar : Icc 0 b ⊆ Ibar.carrier)
    (hncbar : ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ Ibar.carrier,
      ¬ ConjugateAlong Sbar Cbar Rbar Ibar qbar ⟨0,hbar0⟩ ⟨t,ht⟩)
    (hcompare : ∀ (J : (t : ℝ) → TangentSpace S (q t).1)
        (Jbar : (t : ℝ) → TangentSpace Sbar (qbar t).1),
      IsJacobiField C R I.carrier q J → IsJacobiField Cbar Rbar Ibar.carrier qbar Jbar →
      J 0 = 0 → Jbar 0 = 0 →
      NormalFieldOn g q J (Icc 0 b) → NormalFieldOn gbar qbar Jbar (Icc 0 b) →
      ∀ (w : TangentSpace S (q 0).1) (wbar : TangentSpace Sbar (qbar 0).1),
      HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w →
      HasCovariantDerivativeAt Cbar (fun s => (qbar s).1) Jbar 0 wbar →
      tangentNorm g (q 0).1 w = tangentNorm gbar (qbar 0).1 wbar →
      ∀ t ∈ Icc 0 b,
        tangentNorm gbar (qbar t).1 (Jbar t) ≤ tangentNorm g (q t).1 (J t)) :
    ∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
      ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩ := by
  intro t ht htI hconj
  obtain ⟨j, ⟨⟨J, hJ, hj⟩, hj0, hjt⟩, hjne⟩ := hconj
  have hJ0 : J 0 = 0 := (hj ⟨0,h0⟩).trans hj0
  have hJt : J t = 0 := (hj ⟨t,htI⟩).trans hjt
  obtain ⟨V, hV⟩ := hJ
  have hJ : IsJacobiField C R I.carrier q J := ⟨V, hV⟩
  let w := V 0
  have hdJ : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 w := (hV 0 h0).1
  have hw : w ≠ 0 := by
    intro hw
    have hzero := jacobi_zero_of_zero_initial g C hC R hR I q hq h0 J hJ hJ0 (hw ▸ hdJ)
    apply hjne
    funext s
    exact (hj s).symm.trans (hzero s.val s.property)
  let Pbar := JacobiIVP.intervalParallelEquiv Cbar Ibar qbar hqbar 0 hbar0 0
  obtain ⟨wbar, hwbarorth, hnw⟩ := exists_normal_of_norm hn gbar (qbar 0).1 Pbar
    (qbar 0).2 (tangentNorm g (q 0).1 w) (SmoothMetrics.tangentNorm_nonneg _ _ _)
  have hwbar : wbar ≠ 0 := by
    intro hz
    rw [hz, SmoothMetrics.tangentNorm_zero] at hnw
    exact hw ((SmoothMetrics.tangentNorm_eq_zero_iff _ _ _).mp hnw.symm)
  obtain ⟨Jbar, hJbar, hJbar0, hdJbar, _⟩ :=
    JacobiIVP.exists_unique Sbar gbar Cbar hCbar Rbar hRbar Ibar qbar hqbar 0 hbar0 0 wbar
  have hnormal := normal_of_two_orthogonal_values g C hC R hR I q hq h0 J hJ t htI
    (ne_of_gt ht.1) (by rw [hJ0, LinearMap.BilinForm.zero_left])
    (by rw [hJt, LinearMap.BilinForm.zero_left])
  have hnormalbar := normal_of_initial gbar Cbar hCbar Rbar hRbar Ibar qbar hqbar hbar0
    Jbar hJbar hJbar0 wbar hdJbar hwbarorth
  have hle := hcompare J Jbar hJ hJbar hJ0 hJbar0
    (fun s hs => hnormal s (hbI hs)) (fun s hs => hnormalbar s (hbIbar hs))
    w wbar hdJ hdJbar hnw.symm t ⟨ht.1.le, ht.2⟩
  have hpos := jacobi_norm_pos gbar Cbar Rbar Ibar qbar hqbar hbar0 Jbar hJbar hJbar0
    wbar hdJbar hwbar t (hbIbar ⟨ht.1.le, ht.2⟩) (hncbar t ht _)
  rw [hJt, SmoothMetrics.tangentNorm_zero] at hle
  exact (not_lt_of_ge hle) hpos

/-- Rauch comparison, with nonconjugacy through the terminal endpoint and
with the initially trivial fields included. -/
theorem rauch : P202Specs.Geometry.RauchComparison.rauchType.{u} := by
  intro n hn M N _ _ S Sbar g gbar C Cbar hC hCbar R Rbar hR hRbar
    I Ibar q qbar hq hqbar h0 hbar0 b hb hsub hsubbar hunit hunitbar hbound hnc
  have hterminal (K : (s : ℝ) → TangentSpace S (q s).1)
      (Kbar : (s : ℝ) → TangentSpace Sbar (qbar s).1)
      (hK : IsJacobiField C R I.carrier q K) (hKbar : IsJacobiField Cbar Rbar Ibar.carrier qbar Kbar)
      (hK0 : K 0 = 0) (hKbar0 : Kbar 0 = 0)
      (hKn : NormalFieldOn g q K (Icc 0 b)) (hKbarn : NormalFieldOn gbar qbar Kbar (Icc 0 b))
      (t : ℝ) (ht : t ∈ Ioc 0 b)
      (hKt : tangentNorm g (q t).1 (K t) = 1)
      (hKbart : tangentNorm gbar (qbar t).1 (Kbar t) = 1) :
      pairing gbar (qbar t).1 (covariantDerivative Cbar (fun s => (qbar s).1) Kbar t) (Kbar t) ≤
      pairing g (q t).1 (covariantDerivative C (fun s => (q s).1) K t) (K t) := by
    let P := JacobiIVP.intervalParallelEquiv C I q hq 0 h0
    let Pbar := JacobiIVP.intervalParallelEquiv Cbar Ibar qbar hqbar 0 hbar0
    have hP := JacobiIVP.intervalParallelEquiv_parallel C I q hq 0 h0
    have hPbar := JacobiIVP.intervalParallelEquiv_parallel Cbar Ibar qbar hqbar 0 hbar0
    have htcc : t ∈ Icc 0 b := ⟨ht.1.le,ht.2⟩
    obtain ⟨L,hL,hLT,hLK⟩ := exists_parallel_matching_map g gbar C Cbar hC hCbar
      I Ibar q qbar hq hqbar P Pbar hP hPbar t (hsub htcc) (hsubbar htcc)
      (hunit t htcc) (hunitbar t htcc) (K t) (Kbar t)
      ((tangentNorm_eq_one_iff g _ _).mp hKt) ((tangentNorm_eq_one_iff gbar _ _).mp hKbart)
      (hKn t htcc) (hKbarn t htcc)
    have hsmall : Icc 0 t ⊆ Icc 0 b := Icc_subset_Icc le_rfl ht.2
    apply terminal_pairing_compare_of_parallel_map g gbar C Cbar hC hCbar R Rbar hR hRbar
      I Ibar q qbar hq hqbar h0 hbar0 ht.1 (hsmall.trans hsub) (hsmall.trans hsubbar)
      (fun s hs => hbound s (hsmall hs))
      (fun s hs hsI => hnc s ⟨hs.1,hs.2.trans ht.2⟩ hsI)
      P Pbar hP hPbar L (fun s hs => hL s (hsub (hsmall hs)) (hsubbar (hsmall hs)))
      K Kbar hK hKbar hK0 hKbar0 (fun s hs => hKn s (hsmall hs)) _ hLK
    intro s hs
    rw [← hLT s (hsub (hsmall hs)) (hsubbar (hsmall hs))]
    have hp := hL s (hsub (hsmall hs)) (hsubbar (hsmall hs))
      ((P s).symm (K s)) ((P s).symm (q s).2)
    simp only [LinearEquiv.apply_symm_apply] at hp
    exact hp.trans (hKn s (hsmall hs))
  have hcompare := norm_comparison_of_terminal_pairing g gbar C Cbar hC hCbar R Rbar hR hRbar
    I Ibar q qbar hq hqbar h0 hbar0 b hb hsub hsubbar hnc hterminal
  exact ⟨nonconjugacy_of_norm_comparison hn g gbar C Cbar hC hCbar R Rbar hR hRbar
    I Ibar q qbar hq hqbar h0 hbar0 b hsub hsubbar hnc hcompare, hcompare⟩

end P202.Geometry.RauchComparison
