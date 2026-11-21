import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.IndexLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiMatrix
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SecondVariation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Ring.Units
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Order.Monotone.Union
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.LocallyFinite
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps


/-! The index lemma, paper.tex 4103–4143, for the full tangent Jacobi operator.
The proof uses the continuous inverse-coordinate extension at zero and a
primitive-minus-boundary potential that is monotone on the smooth pieces.
This treats piecewise C¹ fields without requiring derivative regularity at zero. -/
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
namespace P202.Geometry.IndexLemma
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialJacobiData
  P202.JacobiMatrixData P202.SecondVariationData P202.IndexLemmaData
open Set Filter MeasureTheory
open scoped Topology ContDiff
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Nonconjugacy makes evaluation at the two endpoints injective on Jacobi
fields. This argument uses the actual restricted fields in ConjugateAlong. -/
theorem jacobi_eq_of_endpoints
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    {a b : I.carrier} (hnc : ¬ ConjugateAlong S C R I q a b)
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J)
    (hK : IsJacobiField C R I.carrier q K)
    (ha : J a.val = K a.val) (hb : J b.val = K b.val) :
    ∀ t ∈ I.carrier, J t = K t := by
  let W : RestrictedField S I q := fun t => J t.val - K t.val
  have hW : W ∈ EndpointFields S C R I q a b := by
    refine ⟨⟨fun t => J t - K t, JacobiIVP.jacobi_sub C R hJ hK, fun _ => rfl⟩,
      ?_, ?_⟩
    · exact sub_eq_zero.mpr ha
    · exact sub_eq_zero.mpr hb
  have hzero : W = 0 := by
    by_contra h
    exact hnc ⟨W, hW, h⟩
  intro t ht
  exact sub_eq_zero.mp (congrFun hzero ⟨t, ht⟩)

/-- Every terminal vector is attained, including in dimension zero and along
constant affine geodesics. Only terminal nonconjugacy is used in this step. -/
theorem endpoint : P202Specs.Geometry.IndexLemma.endpointType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 b hb hbI hnc z
  obtain ⟨D, hD⟩ := JacobiMatrix.construction S g C hC R hR I q hq h0
  have hAb := JacobiMatrix.invertible S g C hC R hR I q hq h0 D b hb hbI hnc
  obtain ⟨y, hy⟩ := (hD b hbI).2 z
  obtain ⟨x, hx⟩ := hAb.2 y
  obtain ⟨hJ, hJ0, _, _⟩ :=
    JacobiMatrix.field_representation S g C hC R hR I q hq h0 D x
  let J := fun t => D.frame t (D.A t x)
  have hJb : J b = z := by
    dsimp only [J]
    rw [hx, hy]
  refine ⟨J, hJ, hJ0, hJb, ?_⟩
  intro K hK hK0 hKb
  exact jacobi_eq_of_endpoints C R I q hnc hK hJ
    (hK0.trans hJ0.symm) (hKb.trans hJb.symm)

/-- The square identity behind the index comparison, in the original metric.
Only differentiability at the specified time is needed. No regularity of the
coefficient field at zero, and no inverse-matrix estimate, is assumed. -/
theorem jacobi_square_identity
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    {r : ℕ} (D : JacobiSystem S C R I q r)
    {f : ℝ → Euclidean r} {t : ℝ} {w : Euclidean r}
    (ht : t ∈ I.carrier) (hf : HasDerivAt f w t) :
    let W := fun s => D.frame s (D.A s (f s))
    let Z := fun s => D.frame s (D.B s (f s))
    let P := D.frame t (D.A t w)
    let Q := D.frame t (D.B t (f t))
    HasDerivAt (fun s => pairing g (q s).1 (W s) (Z s))
      (pairing g (q t).1 (Q + P) (Q + P) -
        pairing g (q t).1 (R.val (q t).1 (W t) (q t).2 (q t).2) (W t) -
        pairing g (q t).1 P P) t := by
  dsimp only
  have hA : HasDerivAt (fun s => D.A s (f s))
      (D.B t (f t) + D.A t w) t := (D.derivatives t ht).1.clm_apply hf
  have hB : HasDerivAt (fun s => D.B s (f s))
      (-(D.curvature t (D.A t (f t))) + D.B t w) t := by
    simpa only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.mul_apply] using
      (D.derivatives t ht).2.clm_apply hf
  have hW := JacobiMatrix.derivative_in_frame C D.frame (hq t ht).1
    (fun i => D.frame_parallel (Pi.single i 1) t ht) hA
  have hZ := JacobiMatrix.derivative_in_frame C D.frame (hq t ht).1
    (fun i => D.frame_parallel (Pi.single i 1) t ht) hB
  simp only [map_add, map_neg, D.curvature_eq t ht] at hW hZ
  have hd : HasDerivAt
      (fun s => pairing g (q s).1 (D.frame s (D.A s (f s)))
        (D.frame s (D.B s (f s))))
      (pairing g (q t).1
        (D.frame t (D.B t (f t)) + D.frame t (D.A t w))
        (D.frame t (D.B t (f t))) +
       pairing g (q t).1 (D.frame t (D.A t (f t)))
        (-(R.val (q t).1 (D.frame t (D.A t (f t))) (q t).2 (q t).2) +
          D.frame t (D.B t w))) t :=
    hasDerivWithinAt_univ.mp
      (ParallelTransport.metric_pairing_deriv C g hC.2 (mem_univ t)
        uniqueDiffWithinAt_univ hW hZ)
  have hwr := JacobiMatrix.wronskian S g C hC R hR I q hq h0 D t ht (f t) w
  have hsym :
      pairing g (q t).1
        (R.val (q t).1 (D.frame t (D.A t (f t))) (q t).2 (q t).2)
        (D.frame t (D.A t (f t))) =
      pairing g (q t).1 (D.frame t (D.A t (f t)))
        (R.val (q t).1 (D.frame t (D.A t (f t))) (q t).2 (q t).2) :=
    g.symmetric _ _ _
  have hvalue :
      pairing g (q t).1
        (D.frame t (D.B t (f t)) + D.frame t (D.A t w))
        (D.frame t (D.B t (f t))) +
       pairing g (q t).1 (D.frame t (D.A t (f t)))
        (-(R.val (q t).1 (D.frame t (D.A t (f t))) (q t).2 (q t).2) +
          D.frame t (D.B t w)) =
      pairing g (q t).1
        (D.frame t (D.B t (f t)) + D.frame t (D.A t w))
        (D.frame t (D.B t (f t)) + D.frame t (D.A t w)) -
      pairing g (q t).1
        (R.val (q t).1 (D.frame t (D.A t (f t))) (q t).2 (q t).2)
        (D.frame t (D.A t (f t))) -
      pairing g (q t).1 (D.frame t (D.A t w)) (D.frame t (D.A t w)) := by
    simp only [map_add, LinearMap.add_apply]
    rw [LinearMap.BilinForm.neg_right (R₁ := ℝ) (M₁ := TangentSpace S (q t).1)
      (B₁ := pairing g (q t).1), hwr, ← hsym]
    ring
  exact hvalue ▸ hd

/-- The constant transverse extension of an affine geodesic is smooth on
any compact subsegment of its open time domain. This supplies the actual
smoothness hypothesis of the upstream index-form calculus. -/
theorem geodesic_smoothVariation
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hsub : Icc a b ⊆ I.carrier) :
    P202.FirstVariationData.SmoothVariationOn S (fun z => (q z.2).1) 1 a b := by
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hqi := (hbridge I q).mpr hq
  have hπ := SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S)
  have hc : ContinuousOn (fun t => (q t).1) I.carrier := by
    intro t ht
    exact ((hπ (q t)).1.comp (hqi.1.continuousAt (I.isOpen.mem_nhds ht))).continuousWithinAt
  constructor
  · exact (hc.mono hsub).comp continuousOn_snd (fun _ hz => hz.2)
  · intro z hz
    have ht := hsub hz.2
    obtain ⟨e, he, hp⟩ := (phaseManifold S).smoothStructure.property.1.1 (q z.2)
    obtain ⟨d, hd, hpd⟩ := S.smoothStructure.property.1.1 (q z.2).1
    obtain ⟨U, hU, hpU, F, hF, hrep⟩ := (hπ (q z.2)).2 e he d hd hp hpd
    have hcoord := (hqi.2 z.2 ht e he hp).1
    have hcomp := (hF.contDiffAt (hU.mem_nhds hpU)).comp z.2 hcoord
    have heq := hrep.comp_tendsto (hqi.1.continuousAt (I.isOpen.mem_nhds ht))
    refine ⟨d, hd, hpd, (fun w => F (e (q w.2)).val),
      hcomp.comp z contDiffAt_snd, heq.eq_of_nhds, ?_⟩
    exact (heq.symm.comp_tendsto continuousAt_snd).filter_mono nhdsWithin_le_nhds

/-- On an open parameter domain, a field with continuous actual covariant
derivative is C¹ in local smooth frames. In particular no extra regularity
certificate is needed for a Jacobi field. -/
theorem c1FieldOn_of_continuous_derivative
    (C : Connection (tangentBundle S)) {c : ℝ → M} {U : Set ℝ}
    (hU : IsOpen U) (hc1 : P202.CurveData.CoordinateC1On S c U)
    (hc : ContinuousOn c U)
    {J V : (t : ℝ) → TangentSpace S (c t)}
    (hJ : ∀ t ∈ U, HasCovariantDerivativeAt C c J t (V t))
    (hV : ContinuousOn (fun t => (⟨c t, V t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) U) :
    C1FieldOn (B := tangentBundle S) c J U := by
  classical
  intro t ht
  obtain ⟨O, hO, hp, ⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) (c t)
  let K := U ∩ c ⁻¹' O
  have hK : IsOpen K := hc.isOpen_inter_preimage hU hO
  have htK : t ∈ K := ⟨ht, hp⟩
  have hmaps : MapsTo c K O := fun _ hs => hs.2
  have hcK := hc.mono (show K ⊆ U from inter_subset_left)
  have hc1K := PiecewiseCurves.CoordinateC1On.mono hc1 (show K ⊆ U from inter_subset_left)
  have hJC : ContinuousOn (fun s => (⟨c s, J s⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K := by
    intro s hs
    exact (JacobiIVP.covariantDerivative_continuousAt C (hJ s hs.1)).continuousWithinAt
  have hcoefJ := ParallelTransport.coefficients_continuousOn b hJC hmaps
  have hcoefV := ParallelTransport.coefficients_continuousOn b
    (hV.mono (show K ⊆ U from inter_subset_left)) hmaps
  let d : ℝ → Euclidean n := fun s => coefficientsAlong b c V s -
    (ParallelTransport.matrixAlong C b c K s).mulVec (coefficientsAlong b c J s)
  have hd : ∀ s ∈ K, HasDerivAt (coefficientsAlong b c J) (d s) s := by
    intro s hs
    have hf := ParallelTransport.covariantDerivative_mono (hJ s hs.1) (subset_univ K)
    obtain ⟨w, hw⟩ := CurveCovariantDerivative.exists_coefficients_deriv C hs hf b hs.2
    have hvel := PiecewiseCurves.withinVelocity_spec hc1K hcK hs
    have heq := CurveCovariantDerivative.local_formula C hs (hK.uniqueDiffOn s hs)
      hf b hs.2 hvel hw
    have heq' := congrArg (b.basis ⟨c s, hs.2⟩).equivFun heq
    simp only [frameDerivative, LinearEquiv.apply_symm_apply] at heq'
    have hwval : w = d s := by
      dsimp only [d, ParallelTransport.matrixAlong]
      rw [dite_eq_left (show c s ∈ O from hs.2), CurveCovariantDerivative.coefficientsAlong_of_mem b c V s hs.2,
        heq']
      abel
    exact hwval ▸ hw.hasDerivAt (hK.mem_nhds hs)
  have hdC : ContinuousOn d K := by
    apply hcoefV.sub
    apply continuousOn_pi.mpr
    intro i
    change ContinuousOn (fun s => ∑ j,
      ParallelTransport.matrixAlong C b c K s i j * coefficientsAlong b c J s j) K
    apply continuousOn_finsetSum
    intro j _
    exact ((continuous_apply j).comp_continuousOn
      ((continuous_apply i).comp_continuousOn
        (ParallelTransport.matrixAlong_continuousOn C b hc1K hcK hK.uniqueDiffOn hmaps))).mul
      ((continuous_apply j).comp_continuousOn hcoefJ)
  have hc1coef : ContDiffOn ℝ 1 (coefficientsAlong b c J) K := by
    rw [show (1 : ℕ∞ω) = 0 + 1 from rfl, contDiffOn_succ_iff_deriv_of_isOpen hK]
    refine ⟨fun s hs => (hd s hs).differentiableAt.differentiableWithinAt,
      by simp, ?_⟩
    exact contDiffOn_zero.mpr (hdC.congr (fun s hs => (hd s hs).deriv))
  exact ⟨O, hO, b, hp, coefficientsAlong b c J,
    hc1coef.contDiffAt (hK.mem_nhds htK), rfl, Filter.EventuallyEq.rfl⟩


/-- A Jacobi field is C¹ on its actual open geodesic domain, directly from
the two derivative relations in the definition. -/
theorem jacobi_c1FieldOn
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {J : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J) :
    C1FieldOn (B := tangentBundle S) (fun t => (q t).1) J I.carrier := by
  obtain ⟨V, hV⟩ := hJ
  apply c1FieldOn_of_continuous_derivative C I.isOpen
    (JacobiIVP.geodesic_coordinateC1 C I q hq)
    (fun t ht => ((hq t ht).1.1.continuousAt (by simp)).continuousWithinAt)
    (fun t ht => (hV t ht).1)
  exact fun t ht => (JacobiIVP.covariantDerivative_continuousAt C (hV t ht).2).continuousWithinAt

/-- The segment tangent agrees with the affine phase velocity, including
at either end of a nondegenerate segment. -/
theorem segmentTangent_eq_phase
    (C : Connection (tangentBundle S)) (I : D13Unified.OpenTimeInterval)
    (q : ℝ → Phase S) (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I.carrier)
    {t : ℝ} (ht : t ∈ Icc a b) :
    segmentTangent S (fun s => (q s).1) a b t = (q t).2 := by
  have hv := FirstVariation.segmentVelocity_spec
    (geodesic_smoothVariation C I q hq hsub) (by norm_num) ht
  have hv' := (hq t (hsub ht)).1
  have hwithin : HasVelocityWithinAt S (fun s => (q s).1) (Icc a b) t (q t).2 :=
    ⟨hv'.1.mono (subset_univ _), hv'.2.choose, hv'.2.choose_spec.choose,
      hv'.2.choose_spec.choose_spec.choose, hv'.2.choose_spec.choose_spec.choose_spec.mono
        (subset_univ _)⟩
  exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hab t ht) hv hwithin

/-- Green's identity for a Jacobi field on one closed C¹ piece. The
right-hand side uses its actual covariant derivative, which is determined by
the Jacobi equation rather than supplied as an extra analytic hypothesis. -/
theorem jacobi_green_identity
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I.carrier)
    {J W : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J)
    (hW : C1FieldOn (B := tangentBundle S) (fun s => (q s).1) W (Icc a b)) :
    indexForm g C R (fun s => (q s).1) a b J W =
      pairing g (q b).1 (covariantDerivative C (fun s => (q s).1) J b) (W b) -
      pairing g (q a).1 (covariantDerivative C (fun s => (q s).1) J a) (W a) := by
  have hJC := jacobi_c1FieldOn C R I q hq hJ
  have hJpiece : C1FieldOn (B := tangentBundle S) (fun s => (q s).1) J (Icc a b) := by
    intro t ht
    obtain ⟨O,hO,d,hp,v,hv,hval,heq⟩ := hJC t (hsub ht)
    exact ⟨O,hO,d,hp,v,hv,hval,heq.filter_mono (nhdsWithin_mono t hsub)⟩
  obtain ⟨V, hV⟩ := hJ
  have hγ := geodesic_smoothVariation C I q hq hsub
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ h0
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  have hDW (t : ℝ) (ht : t ∈ Icc a b) :=
    (CurveCovariantDerivative.segment_derivative C hab hc1 hc hW ht).1
  have hDJ (t : ℝ) (ht : t ∈ Icc a b) :=
    ParallelTransport.covariantDerivative_mono (hV t (hsub ht)).1 (subset_univ (Icc a b))
  have hDV (t : ℝ) (ht : t ∈ Icc a b) :=
    ParallelTransport.covariantDerivative_mono (hV t (hsub ht)).2 (subset_univ (Icc a b))
  let F : ℝ → ℝ := fun t => pairing g (q t).1 (V t) (W t)
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivWithinAt F
        (indexIntegrand g C R (fun s => (q s).1) a b J W t) (Icc a b) t := by
    have hpair : HasDerivWithinAt F
        (pairing g (q t).1
          (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (W t) +
        pairing g (q t).1 (V t)
          (covariantDerivativeWithin C (fun s => (q s).1) W (Icc a b) t)) (Icc a b) t :=
      ParallelTransport.metric_pairing_deriv C g hC.2 ht
        (uniqueDiffOn_Icc hab t ht) (hDV t ht) (hDW t ht)
    have hval : covariantDerivativeWithin C (fun s => (q s).1) J (Icc a b) t = V t :=
      CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
        (uniqueDiffOn_Icc hab t ht) (hDJ t ht)
    have htangent := segmentTangent_eq_phase C I q hq hab hsub ht
    rw [LinearMap.BilinForm.neg_left (R₁ := ℝ) (M₁ := TangentSpace S (q t).1)
      (B₁ := pairing g (q t).1)] at hpair
    simpa only [indexIntegrand, hval, htangent, neg_add_eq_sub] using hpair
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab.le
    (fun t ht => (hd t ht).continuousWithinAt)
    (fun t ht => (hd t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (SecondVariation.indexIntegrand_intervalIntegrable g C R hab hγ hJpiece hW)
  have hda : covariantDerivative C (fun s => (q s).1) J a = V a :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ a)
      uniqueDiffWithinAt_univ (hV a (hsub (left_mem_Icc.mpr hab.le))).1
  have hdb : covariantDerivative C (fun s => (q s).1) J b = V b :=
    CurveCovariantDerivative.covariantDerivativeWithin_eq C (mem_univ b)
      uniqueDiffWithinAt_univ (hV b (hsub (right_mem_Icc.mpr hab.le))).1
  simpa only [indexForm, F, hda, hdb] using hFTC

/-- A Jacobi field is index-orthogonal to every continuous piecewise C¹
field with zero endpoints. Internal boundary pairings cancel because both
traces use the same field values and the same Jacobi derivative. -/
theorem indexForm_jacobi_zero
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I.carrier)
    {J W : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J)
    (hW : PiecewiseC1FieldOn (fun s => (q s).1) W a b)
    (hWa : W a = 0) (hWb : W b = 0) :
    indexForm g C R (fun s => (q s).1) a b J W = 0 := by
  obtain ⟨k,node,hnode,ha,hb,hW⟩ := hW
  subst a
  subst b
  have hsmall (i : Fin (k+1)) : Icc (node i.castSucc) (node i.succ) ⊆ I.carrier :=
    (Icc_subset_Icc (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _))).trans hsub
  have hJC := jacobi_c1FieldOn C R I q hq hJ
  have hJpiece (i : Fin (k+1)) : C1FieldOn (B := tangentBundle S)
      (fun s => (q s).1) J (Icc (node i.castSucc) (node i.succ)) := by
    intro t ht
    obtain ⟨O,hO,d,hp,v,hv,hval,heq⟩ := hJC t (hsmall i ht)
    exact ⟨O,hO,d,hp,v,hv,hval,heq.filter_mono (nhdsWithin_mono t (hsmall i))⟩
  have hdiv : indexForm g C R (fun s => (q s).1)
      (node 0) (node (Fin.last (k+1))) J W =
      ∑ i : Fin (k+1), indexForm g C R (fun s => (q s).1)
        (node i.castSucc) (node i.succ) J W :=
    SecondVariation.indexForm_subdivision_of_integrable g C R node hnode
      (geodesic_smoothVariation C I q hq hsub) hJpiece hW
      (fun i => SecondVariation.indexIntegrand_intervalIntegrable g C R
        (hnode (Fin.castSucc_lt_succ (i := i)))
        (geodesic_smoothVariation C I q hq (hsmall i)) (hJpiece i) (hW i))
  rw [hdiv]
  simp_rw [jacobi_green_identity g C hC R I q hq
    (hnode (Fin.castSucc_lt_succ (i := _))) (hsmall _) hJ (hW _)]
  rw [FirstVariation.sum_segment_boundary node
    (fun _ t => pairing g (q t).1
      (covariantDerivative C (fun s => (q s).1) J t) (W t))]
  simp only [hWa, hWb, map_zero, sub_self, Finset.sum_const_zero, add_zero]


/-- A C¹ field has C¹ coefficient germs in every smooth local frame. -/
theorem c1_coefficients_in_frame
    {c : ℝ → M} {U : Set ℝ}
    (hc1 : P202.CurveData.CoordinateC1On S c U) (hc : ContinuousOn c U)
    {J : (t : ℝ) → TangentSpace S (c t)}
    (hJ : C1FieldOn (B := tangentBundle S) c J U)
    {O : Set M} {hO : IsOpen O} (b : LocalFrame (tangentBundle S) O hO)
    {t : ℝ} (ht : t ∈ U) (hp : c t ∈ O) :
    ∃ v : ℝ → Euclidean n, ContDiffAt ℝ 1 v t ∧
      coefficientsAlong b c J =ᶠ[𝓝[U] t] v := by
  classical
  obtain ⟨W,hW,d,hpW,v,hv,_,heqv⟩ := hJ t ht
  let hOW := hO.inter hW
  let b' := restrictFrame (hU := hOW) b inter_subset_left
  let d' := restrictFrame (hU := hOW) d inter_subset_right
  have hsmooth (i j : Fin n) := FirstVariation.scalar_c1_extension hc1 hc ht
    (SmoothManifolds.FrameData.VectorSmoothAt.totalize hOW
      (ConnectionForms.localTransition_smooth (tangentBundle S) b' d' i j
        ⟨c t,⟨hp,hpW⟩⟩))
  choose G hG hGeq using hsmooth
  let f : ℝ → Euclidean n := fun s i => ∑ j : Fin n, G i j s * v s j
  refine ⟨f, ?_, ?_⟩
  · apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro j _
    exact (hG i j).mul (contDiffAt_pi.mp hv j)
  · have hGeqall := Filter.eventually_all.mpr (fun i =>
      Filter.eventually_all.mpr (hGeq i))
    filter_upwards [heqv,hGeqall,(hc t ht).eventually (hOW.mem_nhds ⟨hp,hpW⟩)]
      with s hs hGs hsOW
    rw [← CurveCovariantDerivative.coefficients_restrict (hW := hOW) b inter_subset_left c J s hsOW,
      CurveCovariantDerivative.coefficients_change b' d' c J s hsOW,
      CurveCovariantDerivative.coefficients_restrict (hW := hOW) d inter_subset_right c J s hsOW, hs]
    funext i
    dsimp only [f, Matrix.mulVec, dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    exact (SmoothManifolds.FrameData.totalize_of_mem
      (fun p : ↥(O ∩ W) => localTransition b' d' p i j) (c s) hsOW).symm.trans (hGs i j)

/-- The same finite partition supports subtraction of a C¹ field. -/
theorem c1FieldOn_add
    {c : ℝ → M} {U : Set ℝ}
    (hc1 : P202.CurveData.CoordinateC1On S c U) (hc : ContinuousOn c U)
    {J W : (t : ℝ) → TangentSpace S (c t)}
    (hJ : C1FieldOn (B := tangentBundle S) c J U)
    (hW : C1FieldOn (B := tangentBundle S) c W U) :
    C1FieldOn (B := tangentBundle S) c (fun s => J s + W s) U := by
  intro t ht
  obtain ⟨O,hO,b,hp,v,hv,_,heqv⟩ := hJ t ht
  obtain ⟨w,hw,heqw⟩ := c1_coefficients_in_frame hc1 hc hW b ht hp
  have heq : coefficientsAlong b c (fun s => J s + W s) =ᶠ[𝓝[U] t]
      fun s => v s + w s := by
    filter_upwards [heqv,heqw] with s hs hws
    simp only [CurveCovariantDerivative.coefficients_add, hs, hws]
  exact ⟨O,hO,b,hp,_,hv.add hw,heq.self_of_nhdsWithin ht,heq⟩

theorem c1FieldOn_sub
    {c : ℝ → M} {U : Set ℝ}
    (hc1 : P202.CurveData.CoordinateC1On S c U) (hc : ContinuousOn c U)
    {J W : (t : ℝ) → TangentSpace S (c t)}
    (hJ : C1FieldOn (B := tangentBundle S) c J U)
    (hW : C1FieldOn (B := tangentBundle S) c W U) :
    C1FieldOn (B := tangentBundle S) c (fun s => J s - W s) U := by
  intro t ht
  obtain ⟨O,hO,b,hp,v,hv,_,heqv⟩ := hJ t ht
  obtain ⟨w,hw,heqw⟩ := c1_coefficients_in_frame hc1 hc hW b ht hp
  have heq : coefficientsAlong b c (fun s => J s - W s) =ᶠ[𝓝[U] t]
      fun s => v s - w s := by
    filter_upwards [heqv,heqw] with s hs hws
    have hcoef : coefficientsAlong b c (fun s => J s - W s) s =
        coefficientsAlong b c J s - coefficientsAlong b c W s := by
      classical
      unfold coefficientsAlong
      split_ifs with hp
      · exact (b.basis ⟨c s, hp⟩).equivFun.map_sub (J s) (W s)
      · exact (sub_self (0 : Euclidean n)).symm
    rw [hcoef,hs,hws]
  exact ⟨O,hO,b,hp,_,hv.sub hw,heq.self_of_nhdsWithin ht,heq⟩

/-- Subtracting a Jacobi field preserves the competitor's finite partition. -/
theorem piecewiseC1_sub_jacobi
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hsub : Icc a b ⊆ I.carrier)
    {J V : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J)
    (hV : PiecewiseC1FieldOn (fun s => (q s).1) V a b) :
    PiecewiseC1FieldOn (fun s => (q s).1) (fun s => V s - J s) a b := by
  obtain ⟨k,node,hnode,ha,hb,hV⟩ := hV
  have hJC := jacobi_c1FieldOn C R I q hq hJ
  refine ⟨k,node,hnode,ha,hb,fun i => ?_⟩
  have hsmall : Icc (node i.castSucc) (node i.succ) ⊆ I.carrier := by
    apply Set.Subset.trans _ hsub
    rw [← ha, ← hb]
    exact Icc_subset_Icc (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _))
  have hγ := geodesic_smoothVariation C I q hq hsmall
  have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  apply c1FieldOn_sub (FirstVariation.variation_coordinateC1On_slice hγ hzero)
    (FirstVariation.variation_continuousOn_slice hγ hzero) (hV i)
  intro t ht
  obtain ⟨O,hO,d,hp,v,hv,hval,heq⟩ := hJC t (hsmall ht)
  exact ⟨O,hO,d,hp,v,hv,hval,heq.filter_mono (nhdsWithin_mono t hsmall)⟩

/-- Index-form splitting at the Jacobi field, for continuous piecewise C¹ competitors. -/
theorem indexForm_split_jacobi
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I.carrier)
    {J V : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I.carrier q J)
    (hV : PiecewiseC1FieldOn (fun s => (q s).1) V a b)
    (hVa : V a = J a) (hVb : V b = J b) :
    indexForm g C R (fun s => (q s).1) a b V V =
      indexForm g C R (fun s => (q s).1) a b J J +
      indexForm g C R (fun s => (q s).1) a b (fun s => V s - J s) (fun s => V s - J s) := by
  let W := fun s => V s - J s
  have hW := piecewiseC1_sub_jacobi C R I q hq hsub hJ hV
  have hzero := indexForm_jacobi_zero g C hC R I q hq hab hsub hJ hW
    (sub_eq_zero.mpr hVa) (sub_eq_zero.mpr hVb)
  obtain ⟨k,node,hnode,ha,hb,hVp⟩ := hV
  have hJC := jacobi_c1FieldOn C R I q hq hJ
  have hsmall (i : Fin (k+1)) : Icc (node i.castSucc) (node i.succ) ⊆ I.carrier := by
    apply Set.Subset.trans _ hsub
    rw [← ha, ← hb]
    exact Icc_subset_Icc (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _))
  have hJp (i : Fin (k+1)) : C1FieldOn (B := tangentBundle S)
      (fun s => (q s).1) J (Icc (node i.castSucc) (node i.succ)) := by
    intro t ht
    obtain ⟨O,hO,d,hp,v,hv,hval,heq⟩ := hJC t (hsmall i ht)
    exact ⟨O,hO,d,hp,v,hv,hval,heq.filter_mono (nhdsWithin_mono t (hsmall i))⟩
  have hWp (i : Fin (k+1)) : C1FieldOn (B := tangentBundle S)
      (fun s => (q s).1) W (Icc (node i.castSucc) (node i.succ)) := by
    have hγ := geodesic_smoothVariation C I q hq (hsmall i)
    have hzero : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
    exact c1FieldOn_sub (FirstVariation.variation_coordinateC1On_slice hγ hzero)
      (FirstVariation.variation_continuousOn_slice hγ hzero) (hVp i) (hJp i)
  have hγ := geodesic_smoothVariation C I q hq hsub
  have hsum : (fun s => J s + W s) = V := by
    funext s
    dsimp [W]
    abel
  have hleft := (SecondVariation.indexForm_bilinear g C R
    (fun s => (q s).1) a b hab hγ node hnode ha hb J W V hJp hWp hVp).1
  have hright1 := (SecondVariation.indexForm_bilinear g C R
    (fun s => (q s).1) a b hab hγ node hnode ha hb J J W hJp hJp hWp).2.1
  have hright2 := (SecondVariation.indexForm_bilinear g C R
    (fun s => (q s).1) a b hab hγ node hnode ha hb W J W hWp hJp hWp).2.1
  rw [hsum] at hleft hright1 hright2
  have hsym : indexForm g C R (fun s => (q s).1) a b W J =
      indexForm g C R (fun s => (q s).1) a b J W :=
    SecondVariation.indexForm_symmetric g C hC R hR (fun s => (q s).1) a b W J
  rw [hleft, hright1, hright2, hsym]
  change indexForm g C R (fun s => (q s).1) a b J J +
    indexForm g C R (fun s => (q s).1) a b J W +
    (indexForm g C R (fun s => (q s).1) a b J W +
      indexForm g C R (fun s => (q s).1) a b W W) = _
  change indexForm g C R (fun s => (q s).1) a b J W = 0 at hzero
  rw [hzero]
  simp only [add_zero, zero_add]
  rfl
/-- A field vanishing on the segment has zero index, regardless of its representative outside. -/
theorem indexForm_eq_zero_of_eqOn_zero
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {a b : ℝ} (hab : a < b) (hsub : Icc a b ⊆ I.carrier)
    {V : (t : ℝ) → TangentSpace S (q t).1}
    (hV : ∀ t ∈ Icc a b, V t = 0) :
    indexForm g C R (fun s => (q s).1) a b V V = 0 := by
  have hint (t : ℝ) (ht : t ∈ Icc a b) :
      indexIntegrand g C R (fun s => (q s).1) a b V V t = 0 := by
    have hDzero : HasCovariantDerivativeAt C (fun s => (q s).1)
        (fun _ => 0) t 0 := by
      simpa only [zero_smul, add_zero] using
        CurveCovariantDerivative.derivative_smul C (hq t (hsub ht)).2
          (hasDerivWithinAt_const t univ (0 : ℝ))
    have hDzero' := ParallelTransport.covariantDerivative_mono hDzero (subset_univ (Icc a b))
    have hDV := ParallelTransport.covariantDerivative_congr ht hDzero' hV
    have hd := CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
      (uniqueDiffOn_Icc hab t ht) hDV
    simp only [indexIntegrand, hd, hV t ht, map_zero, LinearMap.zero_apply, sub_self]
  change (∫ t in a..b, indexIntegrand g C R (fun s => (q s).1) a b V V t) = 0
  calc
    (∫ t in a..b, indexIntegrand g C R (fun s => (q s).1) a b V V t) =
        ∫ _ in a..b, (0 : ℝ) := by
      apply intervalIntegral.integral_congr
      rw [uIcc_of_le hab.le]
      exact hint
    _ = 0 := by simp



/-- A parallel field has C¹ coefficient extensions on the open geodesic domain. -/
theorem parallel_c1FieldOn
    (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    {W : (t : ℝ) → TangentSpace S (q t).1}
    (hW : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun s => (q s).1) W t 0) :
    C1FieldOn (B := tangentBundle S) (fun t => (q t).1) W I.carrier := by
  have hc : ContinuousOn (fun t => (q t).1) I.carrier :=
    fun t ht => ((hq t ht).1.1.continuousAt (by simp)).continuousWithinAt
  apply c1FieldOn_of_continuous_derivative C I.isOpen
    (JacobiIVP.geodesic_coordinateC1 C I q hq) hc hW
  intro t ht
  exact ((tangentBundle S).zero_smooth (q t).1).1.comp_continuousWithinAt
    (f := fun s : ℝ => (q s).1) (hc t ht)

/-- Totalize a surjective Jacobi frame by arbitrary fiber coordinates away
from its actual time domain. -/
noncomputable def jacobiFrameEquiv
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    (t : ℝ) : Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1 := by
  classical
  exact if ht : t ∈ I.carrier then LinearEquiv.ofBijective (D.frame t) (hD t ht)
    else JacobiIVP.tangentCoordinates (q t).1

theorem jacobiFrameEquiv_apply
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    {t : ℝ} (ht : t ∈ I.carrier) (x : Euclidean n) :
    jacobiFrameEquiv D hD t x = D.frame t x := by
  simp only [jacobiFrameEquiv, dif_pos ht, LinearEquiv.ofBijective_apply]

theorem jacobiFrameEquiv_parallel
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    (x : Euclidean n) {t : ℝ} (ht : t ∈ I.carrier) :
    HasCovariantDerivativeAt C (fun s => (q s).1)
      (fun s => jacobiFrameEquiv D hD s x) t 0 := by
  apply ParallelTransport.derivative_field_congr C (mem_univ t) _ (D.frame_parallel x t ht)
  rw [nhdsWithin_univ]
  filter_upwards [I.isOpen.mem_nhds ht] with s hs
  exact (jacobiFrameEquiv_apply D hD hs x).symm



/-- C¹ coefficient germs remain C¹ in a moving C¹ fiber equivalence.
Only the germs on the closed parameter set enter this statement. -/
theorem inverse_coordinates_c1_germ
    {c : ℝ → M} {U : Set ℝ}
    (hc1 : P202.CurveData.CoordinateC1On S c U) (hc : ContinuousOn c U)
    (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    (hP : ∀ i : Fin n, C1FieldOn (B := tangentBundle S) c
      (fun s => P s (Pi.single i 1)) U)
    {W : (s : ℝ) → TangentSpace S (c s)}
    (hW : C1FieldOn (B := tangentBundle S) c W U)
    {t : ℝ} (ht : t ∈ U) (hcAt : ContinuousAt c t) :
    ∃ v : ℝ → Euclidean n, ContDiffAt ℝ 1 v t ∧
      (fun s => (P s).symm (W s)) =ᶠ[𝓝[U] t] v := by
  classical
  obtain ⟨O,hO,b,hp,v,hv,_,heqv⟩ := hW t ht
  choose p hp1 hpeq using
    (fun i => c1_coefficients_in_frame hc1 hc (hP i) b ht hp)
  let Q : ℝ → (Euclidean n →L[ℝ] Euclidean n) :=
    fun s => JacobiIVP.columnOperator (fun i => p i s)
  have hQ : ContDiffAt ℝ 1 Q t := by
    apply ContDiffAt.sum
    intro i _
    exact (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
      (ContinuousLinearMap.proj i)).contDiff.contDiffAt.comp t (hp1 i)
  have hQeq : Q =ᶠ[𝓝[U] t] JacobiIVP.frameCoordinateOperator b P := by
    filter_upwards [Filter.eventually_all.mpr hpeq] with s hs
    simp only [Q, JacobiIVP.frameCoordinateOperator]
    congr 1
    funext i
    exact (hs i).symm
  have hu : IsUnit (Q t) := by
    rw [hQeq.eq_of_nhdsWithin ht]
    exact JacobiIVP.frameCoordinateOperator_isUnit b P hp
  have hinv : ContDiffAt ℝ 1 Ring.inverse (Q t) := by
    simpa only [hu.unit_spec] using (contDiffAt_ringInverse ℝ hu.unit (n := 1))
  refine ⟨fun s => Ring.inverse (Q s) (v s),
    (hinv.comp t hQ).clm_apply hv, ?_⟩
  have hcoord := (JacobiIVP.inverse_coordinates_eventuallyEq b P W hp hcAt).filter_mono
    (show 𝓝[U] t ≤ 𝓝 t from nhdsWithin_le_nhds)
  filter_upwards [hcoord, hQeq, heqv] with s hs hQs hvs
  rw [hs, hQs, hvs]



/-- Restricting a C¹ field only restricts its coefficient germs. -/
theorem c1FieldOn_mono {c : ℝ → M} {W : (s : ℝ) → TangentSpace S (c s)}
    {U V : Set ℝ} (hW : C1FieldOn (B := tangentBundle S) c W V) (hUV : U ⊆ V) :
    C1FieldOn (B := tangentBundle S) c W U := by
  intro t ht
  obtain ⟨O,hO,b,hp,v,hv,hval,heq⟩ := hW t (hUV ht)
  exact ⟨O,hO,b,hp,v,hv,hval,heq.filter_mono (nhdsWithin_mono t hUV)⟩

/-- A competitor's closed-piece C¹ extensions induce C¹ extensions of its
coefficients in the full parallel Jacobi frame, including at zero. -/
theorem jacobi_coordinates_c1_germ
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (hq : IsGeodesicOn S C I.carrier q)
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    {U : Set ℝ} (hU : U ⊆ I.carrier)
    {W : (t : ℝ) → TangentSpace S (q t).1}
    (hW : C1FieldOn (B := tangentBundle S) (fun t => (q t).1) W U)
    {t : ℝ} (ht : t ∈ U) :
    ∃ v : ℝ → Euclidean n, ContDiffAt ℝ 1 v t ∧
      (fun s => (jacobiFrameEquiv D hD s).symm (W s)) =ᶠ[𝓝[U] t] v := by
  have hc : ContinuousOn (fun t => (q t).1) I.carrier :=
    fun t ht => ((hq t ht).1.1.continuousAt (by simp)).continuousWithinAt
  apply inverse_coordinates_c1_germ
    (PiecewiseCurves.CoordinateC1On.mono (JacobiIVP.geodesic_coordinateC1 C I q hq) hU)
    (hc.mono hU) (jacobiFrameEquiv D hD) _ hW ht
    ((hq t (hU ht)).1.1.continuousAt (by simp))
  intro i
  exact c1FieldOn_mono (parallel_c1FieldOn C I q hq
    (fun s hs => jacobiFrameEquiv_parallel D hD (Pi.single i 1) hs)) hU


/-- Every point of an ordered compact partition belongs to a closed piece. -/
theorem exists_closed_piece {k : ℕ} (node : Fin (k+2) → ℝ)
    (hnode : Monotone node) {t : ℝ}
    (ht : t ∈ Icc (node 0) (node (Fin.last (k+1)))) :
    ∃ i : Fin (k+1), t ∈ Icc (node i.castSucc) (node i.succ) := by
  classical
  by_cases h : ∃ j, t = node j
  · obtain ⟨j,rfl⟩ := h
    by_cases hj : j.val < k+1
    · let i : Fin (k+1) := ⟨j.val,hj⟩
      refine ⟨i,?_,?_⟩
      · exact hnode (show j.val ≤ i.castSucc.val from le_rfl)
      · exact hnode (show j.val ≤ i.succ.val from Nat.le_succ _)
    · have hjlast : j = Fin.last (k+1) := by apply Fin.ext; simp only [Fin.val_last]; omega
      subst j
      exact ⟨Fin.last k,hnode (Fin.le_last _),le_rfl⟩
  · have hne : ∀ j, t ≠ node j := by simpa only [not_exists] using h
    obtain ⟨i,hi⟩ := PiecewiseCurves.exists_piece_between_nodes node
      (lt_of_le_of_ne ht.1 (hne 0).symm) (lt_of_le_of_ne ht.2 (hne _)) hne
    exact ⟨i,hi.1.le,hi.2.le⟩

/-- Continuous traces on finitely many closed pieces glue at their common
nodes without any equality hypotheses beyond using the same function. -/
theorem continuousOn_of_partition {X : Type*} [TopologicalSpace X]
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : Monotone node)
    {f : ℝ → X}
    (hf : ∀ i : Fin (k+1), ContinuousOn f (Icc (node i.castSucc) (node i.succ))) :
    ContinuousOn f (Icc (node 0) (node (Fin.last (k+1)))) := by
  have h := (locallyFinite_of_finite
    (fun i : Fin (k+1) => Icc (node i.castSucc) (node i.succ))).continuousOn_iUnion
      (fun _ => isClosed_Icc) hf
  apply h.mono
  intro t ht
  obtain ⟨i,hi⟩ := exists_closed_piece node hnode ht
  exact mem_iUnion.mpr ⟨i,hi⟩

/-- Piecewise C¹ competitors have continuous parallel coordinates, including
all matching nodes. -/
theorem jacobi_coordinates_continuousOn
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (hq : IsGeodesicOn S C I.carrier q)
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    {a b : ℝ} (hsub : Icc a b ⊆ I.carrier)
    {W : (t : ℝ) → TangentSpace S (q t).1}
    (hW : PiecewiseC1FieldOn (fun t => (q t).1) W a b) :
    ContinuousOn (fun s => (jacobiFrameEquiv D hD s).symm (W s)) (Icc a b) := by
  obtain ⟨k,node,hnode,ha,hb,hW⟩ := hW
  subst a
  subst b
  apply continuousOn_of_partition node hnode.monotone
  intro i t ht
  have hsmall : Icc (node i.castSucc) (node i.succ) ⊆ I.carrier :=
    (Icc_subset_Icc (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _))).trans hsub
  obtain ⟨v,hv,heq⟩ := jacobi_coordinates_c1_germ hq D hD hsmall (hW i) ht
  exact hv.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin ht)

/-- Coefficient germs give actual within derivatives on each closed piece. -/
theorem jacobi_coordinates_differentiableWithinAt
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (hq : IsGeodesicOn S C I.carrier q)
    (D : JacobiSystem S C R I q n)
    (hD : ∀ t ∈ I.carrier, Function.Bijective (D.frame t))
    {U : Set ℝ} (hU : U ⊆ I.carrier)
    {W : (t : ℝ) → TangentSpace S (q t).1}
    (hW : C1FieldOn (B := tangentBundle S) (fun t => (q t).1) W U)
    {t : ℝ} (ht : t ∈ U) :
    DifferentiableWithinAt ℝ (fun s => (jacobiFrameEquiv D hD s).symm (W s)) U t := by
  obtain ⟨v,hv,heq⟩ := jacobi_coordinates_c1_germ hq D hD hU hW ht
  exact (hv.differentiableAt (by simp)).differentiableWithinAt.congr_of_eventuallyEq heq (heq.eq_of_nhdsWithin ht)


section EndpointCoefficients
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma inverse_smul_clm (c : ℝ) (hc : c ≠ 0) (A : E →L[ℝ] E) :
    Ring.inverse (c • A) = c⁻¹ • Ring.inverse A := by
  let u : (E →L[ℝ] E)ˣ :=
    ⟨c • 1, c⁻¹ • 1, by ext x; simp [hc], by ext x; simp [hc]⟩
  have hu : c • A = (u : E →L[ℝ] E) * A := by
    simp [u]
  rw [hu, Ring.inverse_mul (Or.inl u.isUnit), Ring.inverse_unit]
  ext x
  simp [u]

lemma inverse_quotient_apply (A : E →L[ℝ] E) (w : E) (t : ℝ) (ht : t ≠ 0) :
    Ring.inverse (t⁻¹ • A) (t⁻¹ • w) = Ring.inverse A w := by
  rw [inverse_smul_clm _ (inv_ne_zero ht)]
  simp [ht]

lemma inverse_endpoint_limit [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E) (v : E)
    (hA : HasDerivAt A 1 0) (hA0 : A 0 = 0)
    (hw : HasDerivWithinAt w v (Ici 0) 0) (hw0 : w 0 = 0) :
    Tendsto (fun t => Ring.inverse (A t) (w t)) (𝓝[>] 0) (𝓝 v) := by
  have hAQ : Tendsto (fun t => t⁻¹ • A t) (𝓝[>] 0) (𝓝 1) := by
    simpa [hA0] using hA.tendsto_slope_zero_right
  have hwQ : Tendsto (fun t => t⁻¹ • w t) (𝓝[>] 0) (𝓝 v) := by
    have h := hasDerivWithinAt_iff_tendsto_slope.mp hw
    rw [Ici_sdiff_left] at h
    convert h using 1
    ext t
    simp only [slope_def_module, sub_zero, hw0]
  have hAI : Tendsto (fun t => Ring.inverse (t⁻¹ • A t)) (𝓝[>] 0) (𝓝 1) := by
    simpa only [Function.comp_def, Units.val_one, Ring.inverse_one] using (NormedRing.inverse_continuousAt (1 : (E →L[ℝ] E)ˣ)).tendsto.comp hAQ
  have hlim : Tendsto (fun t => Ring.inverse (t⁻¹ • A t) (t⁻¹ • w t))
      (𝓝[>] 0) (𝓝 v) := by
    simpa only [Function.comp_def, one_apply_eq_self] using (isBoundedBilinearMap_apply.continuous.tendsto (1, v)).comp
      (hAI.prodMk_nhds hwQ)
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact inverse_quotient_apply (A t) (w t) t (ne_of_gt ht)

lemma inverse_endpoint_extension [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E) (v : E)
    (hA : HasDerivAt A 1 0) (hA0 : A 0 = 0)
    (hw : HasDerivWithinAt w v (Ici 0) 0) (hw0 : w 0 = 0) :
    ContinuousWithinAt (Function.update (fun t => Ring.inverse (A t) (w t)) 0 v)
      (Ici 0) 0 := by
  rw [continuousWithinAt_update_same, Ici_sdiff_left]
  exact inverse_endpoint_limit A w v hA hA0 hw hw0

lemma inverse_endpoint_bounded [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E) (v : E)
    (hA : HasDerivAt A 1 0) (hA0 : A 0 = 0)
    (hw : HasDerivWithinAt w v (Ici 0) 0) (hw0 : w 0 = 0) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ t in 𝓝[>] 0, ‖Ring.inverse (A t) (w t)‖ ≤ c := by
  refine ⟨‖v‖ + 1, by positivity, ?_⟩
  have hlim := inverse_endpoint_limit A w v hA hA0 hw hw0
  filter_upwards [hlim.norm.eventually (gt_mem_nhds (lt_add_one ‖v‖))] with t ht
  exact le_of_lt ht

lemma inverse_endpoint_limit_Icc [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E) (v : E) {a : ℝ} (ha : 0 < a)
    (hA : HasDerivAt A 1 0) (hA0 : A 0 = 0)
    (hw : HasDerivWithinAt w v (Icc 0 a) 0) (hw0 : w 0 = 0) :
    Tendsto (fun t => Ring.inverse (A t) (w t)) (𝓝[>] 0) (𝓝 v) := by
  exact inverse_endpoint_limit A w v hA hA0
    (hw.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ha)) hw0

lemma inverse_apply_continuousOn [CompleteSpace E] {s : Set ℝ}
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E)
    (hA : ContinuousOn A s) (hw : ContinuousOn w s)
    (hu : ∀ t ∈ s, Function.Bijective (A t)) :
    ContinuousOn (fun t => Ring.inverse (A t) (w t)) s := by
  intro t ht
  obtain ⟨u, huval⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr (hu t ht)
  have hi : ContinuousAt Ring.inverse (A t) := huval ▸ NormedRing.inverse_continuousAt u
  exact isBoundedBilinearMap_apply.continuous.continuousAt.comp_continuousWithinAt
    ((hi.comp_continuousWithinAt (hA t ht)).prodMk (hw t ht))

lemma inverse_endpoint_package [CompleteSpace E]
    (A : ℝ → E →L[ℝ] E) (w : ℝ → E) (v : E)
    {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (hAc : ContinuousOn A (Icc 0 b)) (hwc : ContinuousOn w (Icc 0 b))
    (hA : HasDerivAt A 1 0) (hA0 : A 0 = 0)
    (hw : HasDerivWithinAt w v (Icc 0 a) 0) (hw0 : w 0 = 0) (hwb : w b = 0)
    (hu : ∀ t ∈ Ioc 0 b, Function.Bijective (A t)) :
    let f := Function.update (fun t => Ring.inverse (A t) (w t)) 0 v
    ContinuousOn f (Icc 0 b) ∧ f b = 0 ∧
      ∀ t ∈ Icc 0 b, A t (f t) = w t := by
  let f := Function.update (fun t => Ring.inverse (A t) (w t)) 0 v
  change ContinuousOn f (Icc 0 b) ∧ f b = 0 ∧
    ∀ t ∈ Icc 0 b, A t (f t) = w t
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hwIci : HasDerivWithinAt w v (Ici 0) 0 :=
    hw.mono_of_mem_nhdsWithin (Icc_mem_nhdsGE ha)
  refine ⟨?_, ?_, ?_⟩
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      exact (inverse_endpoint_extension A w v hA hA0 hwIci hw0).mono Icc_subset_Ici_self
    · change ContinuousWithinAt (Function.update _ 0 v) (Icc 0 b) t
      rw [continuousWithinAt_update_of_ne ht0]
      obtain ⟨u, huval⟩ := ContinuousLinearMap.isUnit_iff_bijective.mpr
        (hu t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩)
      have hi : ContinuousAt Ring.inverse (A t) :=
        huval ▸ NormedRing.inverse_continuousAt u
      exact isBoundedBilinearMap_apply.continuous.continuousAt.comp_continuousWithinAt
        ((hi.comp_continuousWithinAt (hAc t ht)).prodMk (hwc t ht))
  · simp [f, Function.update_of_ne (ne_of_gt hb), hwb]
  · intro t ht
    by_cases ht0 : t = 0
    · subst t
      simp [f, hA0, hw0]
    · have hunit := ContinuousLinearMap.isUnit_iff_bijective.mpr
        (hu t ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0), ht.2⟩)
      simpa [f, Function.update_of_ne ht0] using
        congrArg (fun L : E →L[ℝ] E => L (w t)) (Ring.mul_inverse_cancel (A t) hunit)

end EndpointCoefficients

section ScalarPositivity
/-- A finite set of exceptional derivative points does not affect monotonicity. -/
theorem monotoneOn_Icc_of_hasDerivAt_nonneg_off_finset
    (s : Finset ℝ) {f d : ℝ → ℝ} {a b : ℝ}
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, x ∉ s → HasDerivAt f (d x) x)
    (hn : ∀ x ∈ Ioo a b, x ∉ s → 0 ≤ d x) :
    MonotoneOn f (Icc a b) := by
  classical
  induction s using Finset.induction generalizing a b with
  | empty =>
    apply monotoneOn_of_deriv_nonneg (convex_Icc a b) hc
    · intro x hx
      rw [interior_Icc] at hx
      exact (hd x hx (by simp)).differentiableAt.differentiableWithinAt
    · intro x hx
      rw [interior_Icc] at hx
      rw [(hd x hx (by simp)).deriv]
      exact hn x hx (by simp)
  | @insert c s hcs ih =>
    by_cases hac : a < c
    · by_cases hcb : c < b
      · have hleft : MonotoneOn f (Icc a c) := by
          apply ih (hc.mono (Icc_subset_Icc le_rfl hcb.le))
          · intro x hx hxs
            exact hd x ⟨hx.1, hx.2.trans hcb⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxs⟩)
          · intro x hx hxs
            exact hn x ⟨hx.1, hx.2.trans hcb⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt hx.2, hxs⟩)
        have hright : MonotoneOn f (Icc c b) := by
          apply ih (hc.mono (Icc_subset_Icc hac.le le_rfl))
          · intro x hx hxs
            exact hd x ⟨hac.trans hx.1, hx.2⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxs⟩)
          · intro x hx hxs
            exact hn x ⟨hac.trans hx.1, hx.2⟩ (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt hx.1, hxs⟩)
        intro x hx y hy hxy
        by_cases hxc : x ≤ c
        · by_cases hyc : y ≤ c
          · exact hleft ⟨hx.1,hxc⟩ ⟨hy.1,hyc⟩ hxy
          · exact (hleft ⟨hx.1,hxc⟩ ⟨hac.le,le_rfl⟩ hxc).trans
              (hright ⟨le_rfl,hcb.le⟩ ⟨(not_le.mp hyc).le,hy.2⟩ (not_le.mp hyc).le)
        · exact hright ⟨(not_le.mp hxc).le,hx.2⟩
            ⟨(not_le.mp hxc).le.trans hxy,hy.2⟩ hxy
      · apply ih hc
        · intro x hx hxs
          exact hd x hx (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt (hx.2.trans_le (not_lt.mp hcb)),hxs⟩)
        · intro x hx hxs
          exact hn x hx (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_lt (hx.2.trans_le (not_lt.mp hcb)),hxs⟩)
    · apply ih hc
      · intro x hx hxs
        exact hd x hx (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ((not_lt.mp hac).trans_lt hx.1),hxs⟩)
      · intro x hx hxs
        exact hn x hx (by simp only [Finset.mem_insert, not_or]; exact ⟨ne_of_gt ((not_lt.mp hac).trans_lt hx.1),hxs⟩)

/-- The primitive-minus-boundary argument for a singular endpoint. It requires
no integrability assumption on the nonnegative remainder `p`. -/
theorem integral_nonneg_of_square_potential
    (s : Finset ℝ) {e g p : ℝ → ℝ} {b : ℝ} (hb : 0 < b)
    (he : IntervalIntegrable e MeasureTheory.volume 0 b)
    (hec : ContinuousOn e (Ioo 0 b \ (s : Set ℝ)))
    (hgc : ContinuousOn g (Icc 0 b)) (hg0 : g 0 = 0) (hgb : g b = 0)
    (hdg : ∀ t ∈ Ioo 0 b, t ∉ s → HasDerivAt g (e t - p t) t)
    (hp : ∀ t ∈ Ioo 0 b, t ∉ s → 0 ≤ p t) :
    0 ≤ (∫ t in (0:ℝ)..b, e t) ∧
    ((∫ t in (0:ℝ)..b, e t) = 0 → ∀ t ∈ Ioo 0 b, t ∉ s → p t = 0) := by
  let h : ℝ → ℝ := fun t => (∫ x in (0:ℝ)..t, e x) - g t
  have hU : IsOpen (Ioo 0 b \ (s : Set ℝ)) :=
    isOpen_Ioo.sdiff s.finite_toSet.isClosed
  have heAt : ∀ t ∈ Ioo 0 b \ (s : Set ℝ), ContinuousAt e t :=
    fun t ht => hec.continuousAt (hU.mem_nhds ht)
  have hhc : ContinuousOn h (Icc 0 b) := by
    apply ContinuousOn.sub _ hgc
    simpa only [Set.uIcc_of_le hb.le] using
      intervalIntegral.continuousOn_primitive_interval' he (left_mem_uIcc : (0:ℝ) ∈ uIcc 0 b)
  have hhd : ∀ t ∈ Ioo 0 b, t ∉ s → HasDerivAt h (p t) t := by
    intro t ht hts
    have hmem : t ∈ Ioo 0 b \ (s : Set ℝ) := ⟨ht,hts⟩
    have heint : IntervalIntegrable e MeasureTheory.volume 0 t :=
      he.mono_set (by simpa only [uIcc_of_le hb.le, uIcc_of_le ht.1.le] using
        Icc_subset_Icc le_rfl ht.2.le)
    have hdint := intervalIntegral.integral_hasDerivAt_right heint
      (ContinuousAt.stronglyMeasurableAtFilter hU heAt t hmem) (heAt t hmem)
    convert hdint.sub (hdg t ht hts) using 1 <;> ring
  have hmono : MonotoneOn h (Icc 0 b) :=
    monotoneOn_Icc_of_hasDerivAt_nonneg_off_finset s hhc hhd hp
  have hh0 : h 0 = 0 := by simp [h,hg0]
  have hhb : h b = ∫ t in (0:ℝ)..b, e t := by simp [h,hgb]
  refine ⟨?_,?_⟩
  · simpa only [hh0,hhb] using hmono (left_mem_Icc.mpr hb.le) (right_mem_Icc.mpr hb.le) hb.le
  · intro hz t ht hts
    have hzero : ∀ x ∈ Icc 0 b, h x = 0 := by
      intro x hx
      apply le_antisymm
      · simpa only [hhb,hz] using hmono hx (right_mem_Icc.mpr hb.le) hx.2
      · simpa only [hh0] using hmono (left_mem_Icc.mpr hb.le) hx hx.1
    have heq : h =ᶠ[𝓝 t] fun _ => (0 : ℝ) :=
      Filter.Eventually.mono (Icc_mem_nhds ht.1 ht.2) hzero
    have hd0 : HasDerivAt h 0 t :=
      (hasDerivAt_const t (0:ℝ)).congr_of_eventuallyEq heq
    exact (hhd t ht hts).unique hd0

/-- A continuous finite-dimensional coefficient field with zero derivative
except at finitely many breaks is constant away from a singular initial point. -/
theorem eq_terminal_of_hasDerivAt_zero_off_finset
    {r : ℕ} (s : Finset ℝ) {f : ℝ → (Fin r → ℝ)} {b : ℝ}
    (hc : ContinuousOn f (Ioc 0 b))
    (hd : ∀ t ∈ Ioo 0 b, t ∉ s → HasDerivAt f 0 t) :
    ∀ t ∈ Ioc 0 b, f t = f b := by
  intro t ht
  have hsub : Icc t b ⊆ Ioc 0 b := by
    intro x hx
    exact ⟨ht.1.trans_le hx.1,hx.2⟩
  ext i
  have hci : ContinuousOn (fun x => f x i) (Icc t b) := (continuous_apply i).continuousOn.comp (hc.mono hsub) (fun _ _ => mem_univ _)
  have hdi : ∀ x ∈ Ioo t b, x ∉ s → HasDerivAt (fun x => f x i) 0 x := by
    intro x hx hxs
    simpa using! (ContinuousLinearMap.proj i).hasFDerivAt.comp_hasDerivAt x
      (hd x ⟨ht.1.trans hx.1,hx.2⟩ hxs)
  have hm := monotoneOn_Icc_of_hasDerivAt_nonneg_off_finset s hci hdi (by intros; exact le_rfl)
  have hnegdi : ∀ x ∈ Ioo t b, x ∉ s → HasDerivAt (fun x => -(f x i)) 0 x := by
    intro x hx hxs
    simpa only [neg_zero] using! (hdi x hx hxs).neg
  have hmn := monotoneOn_Icc_of_hasDerivAt_nonneg_off_finset s hci.neg hnegdi (by intros; exact le_rfl)
  apply le_antisymm
  · exact hm (left_mem_Icc.mpr ht.2) (right_mem_Icc.mpr ht.2) ht.2
  · exact neg_le_neg_iff.mp (hmn (left_mem_Icc.mpr ht.2) (right_mem_Icc.mpr ht.2) ht.2)

/-- The zero terminal value fixes the constant coefficient. -/
theorem eq_zero_of_hasDerivAt_zero_off_finset
    {r : ℕ} (s : Finset ℝ) {f : ℝ → (Fin r → ℝ)} {b : ℝ}
    (hc : ContinuousOn f (Ioc 0 b))
    (hd : ∀ t ∈ Ioo 0 b, t ∉ s → HasDerivAt f 0 t) (hb : f b = 0) :
    ∀ t ∈ Ioc 0 b, f t = 0 := by
  intro t ht
  exact (eq_terminal_of_hasDerivAt_zero_off_finset s hc hd t ht).trans hb

/-- Square-potential positivity and its zero case, already assembled for
finite-dimensional coefficient fields. No regularity at the singular endpoint
is required of the derivative field or of the operator. -/
theorem coefficient_integral_nonneg_eq_zero
    {r : ℕ} (s : Finset ℝ) {b : ℝ} (hb : 0 < b)
    (a : ℝ → (Fin r → ℝ) →L[ℝ] (Fin r → ℝ))
    (h : (Fin r → ℝ) → (Fin r → ℝ) → ℝ)
    (hn : ∀ x, 0 ≤ h x x) (hz : ∀ x, h x x = 0 → x = 0)
    {e g : ℝ → ℝ} {f d : ℝ → (Fin r → ℝ)}
    (he : IntervalIntegrable e MeasureTheory.volume 0 b)
    (hec : ContinuousOn e (Ioo 0 b \ (s : Set ℝ)))
    (hgc : ContinuousOn g (Icc 0 b)) (hg0 : g 0 = 0) (hgb : g b = 0)
    (hdg : ∀ t ∈ Ioo 0 b, t ∉ s →
      HasDerivAt g (e t - h (a t (d t)) (a t (d t))) t)
    (hfc : ContinuousOn f (Ioc 0 b)) (hfb : f b = 0)
    (hfd : ∀ t ∈ Ioo 0 b, t ∉ s → HasDerivAt f (d t) t)
    (ha : ∀ t ∈ Ioo 0 b, t ∉ s → Function.Injective (a t)) :
    0 ≤ (∫ t in (0:ℝ)..b, e t) ∧
    ((∫ t in (0:ℝ)..b, e t) = 0 → ∀ t ∈ Ioc 0 b, f t = 0) := by
  have hi := integral_nonneg_of_square_potential s hb he hec hgc hg0 hgb hdg
    (fun t _ _ => hn (a t (d t)))
  refine ⟨hi.1, ?_⟩
  intro hzero
  apply eq_zero_of_hasDerivAt_zero_off_finset s hfc _ hfb
  intro t ht hts
  have hp : a t (d t) = 0 := hz _ (hi.2 hzero t ht hts)
  have hd0 : d t = 0 := (ha t ht hts) (by simpa only [map_zero] using hp)
  exact hd0 ▸ hfd t ht hts

end ScalarPositivity

section ParallelMetric
variable {r : ℕ}
lemma parallel_frame_pairing_constant
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (h0 : 0 ∈ I.carrier) (D : JacobiSystem S C R I q r)
    (t : ℝ) (ht : t ∈ I.carrier) (x y : Euclidean r) :
    pairing g (q t).1 (D.frame t x) (D.frame t y) =
      pairing g (q 0).1 (D.frame 0 x) (D.frame 0 y) := by
  let f := fun s => pairing g (q s).1 (D.frame s x) (D.frame s y)
  have hd (s : ℝ) (hs : s ∈ I.carrier) : HasDerivAt f 0 s := by
    simpa [f, pairing] using hasDerivWithinAt_univ.mp
      (ParallelTransport.metric_pairing_deriv C g hC.2 (mem_univ s)
        uniqueDiffWithinAt_univ (D.frame_parallel x s hs) (D.frame_parallel y s hs))
  exact I.isOpen.is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun s hs => (hd s hs).differentiableAt.differentiableWithinAt)
    (fun s hs => (hd s hs).deriv) ht h0

noncomputable def continuousBilin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) : E →L[ℝ] E →L[ℝ] ℝ :=
  (((LinearMap.toContinuousLinearMap :
    (E →ₗ[ℝ] ℝ) ≃ₗ[ℝ] E →L[ℝ] ℝ).toLinearMap).comp B).toContinuousLinearMap

lemma continuous_bilin {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (B : E →ₗ[ℝ] E →ₗ[ℝ] ℝ) :
    Continuous (fun p : E × E => B p.1 p.2) :=
  (continuousBilin B).continuous₂

lemma parallel_frame_pairing_continuousWithinAt
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (h0 : 0 ∈ I.carrier) (D : JacobiSystem S C R I q r)
    {s : Set ℝ} (hs : s ⊆ I.carrier) {t : ℝ} (ht : t ∈ s)
    {x y : ℝ → Euclidean r} (hx : ContinuousWithinAt x s t)
    (hy : ContinuousWithinAt y s t) :
    ContinuousWithinAt
      (fun a => pairing g (q a).1 (D.frame a (x a)) (D.frame a (y a))) s t := by
  let B : LinearMap.BilinForm ℝ (Euclidean r) :=
    (pairing g (q 0).1).compl₁₂ (D.frame 0) (D.frame 0)
  have hc : ContinuousWithinAt (fun a => B (x a) (y a)) s t :=
    (continuous_bilin B).continuousAt.comp_continuousWithinAt (hx.prodMk hy)
  apply hc.congr
  · intro a ha
    exact parallel_frame_pairing_constant g C hC R I q h0 D a (hs ha) (x a) (y a)
  · exact parallel_frame_pairing_constant g C hC R I q h0 D t (hs ht) (x t) (y t)

lemma parallel_frame_pairing_continuousOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (h0 : 0 ∈ I.carrier) (D : JacobiSystem S C R I q r)
    {s : Set ℝ} (hs : s ⊆ I.carrier) {x y : ℝ → Euclidean r}
    (hx : ContinuousOn x s) (hy : ContinuousOn y s) :
    ContinuousOn
      (fun a => pairing g (q a).1 (D.frame a (x a)) (D.frame a (y a))) s :=
  fun t ht => parallel_frame_pairing_continuousWithinAt g C hC R I q h0 D hs ht
    (hx t ht) (hy t ht)

lemma jacobi_boundary_potential_continuousOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (h0 : 0 ∈ I.carrier) (D : JacobiSystem S C R I q r)
    {s : Set ℝ} (hs : s ⊆ I.carrier) {f : ℝ → Euclidean r}
    (hf : ContinuousOn f s) :
    ContinuousOn
      (fun t => pairing g (q t).1 (D.frame t (D.A t (f t)))
        (D.frame t (D.B t (f t)))) s := by
  apply parallel_frame_pairing_continuousOn g C hC R I q h0 D hs
  · intro t ht
    exact isBoundedBilinearMap_apply.continuous.continuousAt.comp_continuousWithinAt
      (((D.derivatives t (hs ht)).1.continuousAt.continuousWithinAt).prodMk (hf t ht))
  · intro t ht
    exact isBoundedBilinearMap_apply.continuous.continuousAt.comp_continuousWithinAt
      (((D.derivatives t (hs ht)).2.continuousAt.continuousWithinAt).prodMk (hf t ht))


end ParallelMetric

open P202.FirstVariationData
/-- The original segment's integrand is continuous away from the finite nodes. -/
theorem indexIntegrand_piecewise_continuousAt
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 (node 0) (node (Fin.last (k+1))))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ)))
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)))
    {t : ℝ} (ht : t ∈ Ioo (node 0) (node (Fin.last (k+1))))
    (hne : ∀ i, t ≠ node i) :
    ContinuousAt (indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W) t := by
  obtain ⟨i,hi⟩ := PiecewiseCurves.exists_piece_between_nodes node ht.1 ht.2 hne
  have hlt : node i.castSucc < node i.succ := hnode (Fin.castSucc_lt_succ (i := i))
  have hl : node 0 ≤ node i.castSucc := hnode.monotone (Fin.zero_le _)
  have hr : node i.succ ≤ node (Fin.last (k+1)) := hnode.monotone (Fin.le_last _)
  have hsmall := SecondVariation.smoothVariationOn_mono_interval hγ hl hr
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hci := SecondVariation.indexIntegrand_continuousOn g C R hlt
    (FirstVariation.variation_coordinateC1On_slice hsmall h0)
    (FirstVariation.variation_continuousOn_slice hsmall h0)
    (fun x hx => FirstVariation.segmentVelocity_spec hsmall (by norm_num) hx)
    (FirstVariation.segmentVelocity_c1 hsmall (by norm_num) hlt) (hV i) (hW i)
  apply (hci.continuousAt (Icc_mem_nhds hi.1 hi.2)).congr
  filter_upwards [Ioo_mem_nhds hi.1 hi.2] with x hx
  exact (SecondVariation.indexIntegrand_restrict g C R hγ hl hr hlt (hV i) (hW i) hx).symm


/-- The finite node image is an explicit exceptional set for the global integrand. -/
theorem indexIntegrand_piecewise_continuousOn
    (g : RiemannianMetric S) (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 (node 0) (node (Fin.last (k+1))))
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ V
      (Icc (node i.castSucc) (node i.succ)))
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ))) :
    ContinuousOn (indexIntegrand g C R γ (node 0) (node (Fin.last (k+1))) V W)
      (Ioo (node 0) (node (Fin.last (k+1))) \
        ((Finset.univ.image node : Finset ℝ) : Set ℝ)) := by
  classical
  intro t ht
  apply (indexIntegrand_piecewise_continuousAt g C R node hnode hγ hV hW ht.1 ?_).continuousWithinAt
  intro i heq
  apply ht.2
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩


/-- The square identity expressed in the actual full-segment index integrand.
The competitor only has to equal its coordinate expression on the segment. -/
theorem jacobi_square_indexIntegrand
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    {r : ℕ} (D : JacobiSystem S C R I q r)
    {b : ℝ} (hb : 0 < b) (hsub : Icc 0 b ⊆ I.carrier)
    {W : (t : ℝ) → TangentSpace S (q t).1}
    {f : ℝ → Euclidean r} {t : ℝ} {v : Euclidean r}
    (ht : t ∈ Icc 0 b)
    (hT : segmentTangent S (fun s => (q s).1) 0 b t = (q t).2)
    (hf : HasDerivAt f v t)
    (hW : ∀ s ∈ Icc 0 b, W s = D.frame s (D.A s (f s))) :
    HasDerivAt (fun s => pairing g (q s).1
      (D.frame s (D.A s (f s))) (D.frame s (D.B s (f s))))
      (indexIntegrand g C R (fun s => (q s).1) 0 b W W t -
        pairing g (q t).1 (D.frame t (D.A t v)) (D.frame t (D.A t v))) t := by
  have hti : t ∈ I.carrier := hsub ht
  have hA : HasDerivAt (fun s => D.A s (f s))
      (D.B t (f t) + D.A t v) t := (D.derivatives t hti).1.clm_apply hf
  have hsyn := JacobiMatrix.derivative_in_frame C D.frame (hq t hti).1
    (fun i => D.frame_parallel (Pi.single i 1) t hti) hA
  have hwder := SecondVariation.hasCovariantDerivativeWithinAt_congr_field C ht
    (ParallelTransport.covariantDerivative_mono hsyn (subset_univ (Icc 0 b))) hW
  have hdW := CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
    (uniqueDiffOn_Icc hb t ht) hwder
  have hsquare := jacobi_square_identity g C hC R hR I q hq h0 D hti hf
  simpa only [indexIntegrand, hdW, map_add, hT, hW t ht] using hsquare


/-- The zero-endpoint analytic core, isolated for final algebraic assembly. -/
def zeroEndpointNonnegativeType : Prop :=
  ∀ {n : ℕ} {M : Type u} [TopologicalSpace M]
    (S : SmoothManifold n .euclidean M) (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)), IsLeviCivita g C →
    ∀ R : CurvatureTensor S, RepresentsCurvature C R →
    ∀ (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S),
      IsGeodesicOn S C I.carrier q → ∀ h0 : 0 ∈ I.carrier,
    ∀ b : ℝ, 0 < b → Icc 0 b ⊆ I.carrier →
      (∀ t ∈ Ioc 0 b, ∀ ht : t ∈ I.carrier,
        ¬ ConjugateAlong S C R I q ⟨0,h0⟩ ⟨t,ht⟩) →
    ∀ V : (t : ℝ) → TangentSpace S (q t).1,
      PiecewiseC1FieldOn (fun t => (q t).1) V 0 b → V 0 = 0 → V b = 0 →
      0 ≤ indexForm g C R (fun t => (q t).1) 0 b V V ∧
        (indexForm g C R (fun t => (q t).1) 0 b V V = 0 → ∀ t ∈ Icc 0 b, V t = 0)

/-- The endpoint construction and zero-endpoint core imply the full index comparison. -/
theorem index_lemma_from_nonnegative
    (hpos : zeroEndpointNonnegativeType.{u}) :
    P202Specs.Geometry.IndexLemma.index_lemmaType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 b hb hsub hnc z
  have hbI : b ∈ I.carrier := hsub (right_mem_Icc.mpr hb.le)
  obtain ⟨J,hJ,hJ0,hJb,hunique⟩ := endpoint S g C hC R hR I q hq h0 b hb hbI
    (hnc b ⟨hb,le_rfl⟩ hbI) z
  refine ⟨J,hJ,hJ0,hJb,hunique,?_⟩
  intro V hV hV0 hVb
  let W := fun s => V s - J s
  have hW := piecewiseC1_sub_jacobi C R I q hq hsub hJ hV
  have hW0 : W 0 = 0 := sub_eq_zero.mpr (hV0.trans hJ0.symm)
  have hWb : W b = 0 := sub_eq_zero.mpr (hVb.trans hJb.symm)
  obtain ⟨hnonneg,hzero⟩ := hpos S g C hC R hR I q hq h0 b hb hsub hnc W hW hW0 hWb
  have hsplit := indexForm_split_jacobi g C hC R hR I q hq hb hsub hJ hV
    (hV0.trans hJ0.symm) (hVb.trans hJb.symm)
  change indexForm g C R (fun s => (q s).1) 0 b V V =
    indexForm g C R (fun s => (q s).1) 0 b J J +
    indexForm g C R (fun s => (q s).1) 0 b W W at hsplit
  constructor
  · linarith
  · constructor
    · intro heq
      have hWW : indexForm g C R (fun s => (q s).1) 0 b W W = 0 := by linarith
      intro t ht
      exact sub_eq_zero.mp (hzero hWW t ht)
    · intro heq
      have hWW := indexForm_eq_zero_of_eqOn_zero g C R I q hq hb hsub
        (V := W) (fun t ht => sub_eq_zero.mpr (heq t ht))
      linarith

/-- The same analytic core yields the strict positive-definiteness statement. -/
theorem positive_definite_from_nonnegative
    (hpos : zeroEndpointNonnegativeType.{u}) :
    P202Specs.Geometry.IndexLemma.positive_definiteType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 b hb hsub hnc V hV hV0 hVb hnonzero
  obtain ⟨hnonneg,hzero⟩ := hpos S g C hC R hR I q hq h0 b hb hsub hnc V hV hV0 hVb
  by_contra hnot
  have heq : indexForm g C R (fun s => (q s).1) 0 b V V = 0 :=
    le_antisymm (le_of_not_gt hnot) hnonneg
  obtain ⟨t,ht,hneq⟩ := hnonzero
  exact hneq (hzero heq t ht)

/-- Nonnegativity and the zero case for every zero-endpoint piecewise C¹ field.
All analytic regularity and integrability are derived from the geometric data. -/
theorem zero_endpoint_nonnegative : zeroEndpointNonnegativeType.{u} := by
  intro n M _ S g C hC R hR I q hq h0 b hb hsub hnc W hW hW0 hWb
  classical
  obtain ⟨D,hD⟩ := JacobiMatrix.construction S g C hC R hR I q hq h0
  let w : ℝ → Euclidean n := fun t => (jacobiFrameEquiv D hD t).symm (W t)
  have hwc : ContinuousOn w (Icc 0 b) := jacobi_coordinates_continuousOn hq D hD hsub hW
  have hw0 : w 0 = 0 := by simp only [w,hW0,map_zero]
  have hwb : w b = 0 := by simp only [w,hWb,map_zero]
  obtain ⟨k,node,hnode,hn0,hnb,hpieces⟩ := hW
  have hsmall (i : Fin (k+1)) : Icc (node i.castSucc) (node i.succ) ⊆ I.carrier := by
    apply (Icc_subset_Icc (hnode.monotone (Fin.zero_le _))
      (hnode.monotone (Fin.le_last _))).trans
    simpa only [hn0,hnb] using hsub
  let a : ℝ := node (0 : Fin (k+1)).succ
  have ha : 0 < a := by
    simpa only [a,Fin.castSucc_zero,hn0] using hnode (Fin.castSucc_lt_succ (i := (0 : Fin (k+1))))
  have hab : a ≤ b := by simpa only [a,hnb] using hnode.monotone (Fin.le_last (0 : Fin (k+1)).succ)
  have hfirst : Icc 0 a ⊆ I.carrier := by
    simpa only [a,Fin.castSucc_zero,hn0] using hsmall 0
  have hWfirst : C1FieldOn (B := tangentBundle S) (fun t => (q t).1) W (Icc 0 a) := by
    simpa only [a,Fin.castSucc_zero,hn0] using hpieces 0
  have hwfirst : DifferentiableWithinAt ℝ w (Icc 0 a) 0 :=
    jacobi_coordinates_differentiableWithinAt hq D hD hfirst hWfirst (left_mem_Icc.mpr ha.le)
  let v : Euclidean n := derivWithin w (Icc 0 a) 0
  let f : ℝ → Euclidean n := Function.update (fun t => Ring.inverse (D.A t) (w t)) 0 v
  have hu : ∀ t ∈ Ioc 0 b, Function.Bijective (D.A t) := by
    intro t ht
    have hti := hsub (Ioc_subset_Icc_self ht)
    exact JacobiMatrix.invertible S g C hC R hR I q hq h0 D t ht.1 hti (hnc t ht hti)
  have hAc : ContinuousOn D.A (Icc 0 b) :=
    fun t ht => (D.derivatives t (hsub ht)).1.continuousAt.continuousWithinAt
  have hAder : HasDerivAt D.A 1 0 := by
    simpa only [D.initial_B] using (D.derivatives 0 h0).1
  obtain ⟨hfc,hfb,hrepr⟩ := inverse_endpoint_package D.A w v ha hab hAc hwc hAder
    D.initial_A hwfirst.hasDerivWithinAt hw0 hwb hu
  change ContinuousOn f (Icc 0 b) at hfc
  change f b = 0 at hfb
  change ∀ t ∈ Icc 0 b, D.A t (f t) = w t at hrepr
  have hWrepr : ∀ t ∈ Icc 0 b, W t = D.frame t (D.A t (f t)) := by
    intro t ht
    rw [hrepr t ht,← jacobiFrameEquiv_apply D hD (hsub ht)]
    exact ((jacobiFrameEquiv D hD t).apply_symm_apply (W t)).symm
  let breaks : Finset ℝ := Finset.univ.image node
  have hwDiff : ∀ t ∈ Ioo 0 b, t ∉ breaks → DifferentiableAt ℝ w t := by
    intro t ht hts
    have hne : ∀ i, t ≠ node i := by
      intro i hi
      exact hts (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,hi.symm⟩)
    have htn : t ∈ Ioo (node 0) (node (Fin.last (k+1))) := by
      simpa only [hn0,hnb] using ht
    obtain ⟨i,hi⟩ := PiecewiseCurves.exists_piece_between_nodes node htn.1 htn.2 hne
    exact (jacobi_coordinates_differentiableWithinAt hq D hD (hsmall i) (hpieces i)
      (Ioo_subset_Icc_self hi)).differentiableAt (Icc_mem_nhds hi.1 hi.2)
  have hfDiff : ∀ t ∈ Ioo 0 b, t ∉ breaks → DifferentiableAt ℝ f t := by
    intro t ht hts
    have hunit : IsUnit (D.A t) := ContinuousLinearMap.isUnit_iff_bijective.mpr (hu t ⟨ht.1,ht.2.le⟩)
    have hi : DifferentiableAt ℝ Ring.inverse (D.A t) := differentiableAt_inverse hunit
    have hcomp := (hi.comp t (D.derivatives t (hsub (Ioo_subset_Icc_self ht))).1.differentiableAt).clm_apply
      (hwDiff t ht hts)
    apply hcomp.congr_of_eventuallyEq
    filter_upwards [eventually_ne_nhds (ne_of_gt ht.1)] with s hs
    exact Function.update_of_ne hs _ _
  let G : ℝ → ℝ := fun t => pairing g (q t).1
    (D.frame t (D.A t (f t))) (D.frame t (D.B t (f t)))
  let H : Euclidean n → Euclidean n → ℝ :=
    fun x y => pairing g (q 0).1 (D.frame 0 x) (D.frame 0 y)
  have hHnonneg : ∀ x, 0 ≤ H x x := fun x => SmoothMetrics.pairing_self_nonneg g (q 0).1 (D.frame 0 x)
  have hHzero : ∀ x, H x x = 0 → x = 0 := by
    intro x hx
    have hframe : D.frame 0 x = 0 := by
      by_contra hn
      exact (ne_of_gt (g.positive (q 0).1 (D.frame 0 x) hn)) hx
    exact D.frame_injective 0 h0 (by simpa only [map_zero] using hframe)
  have hGc : ContinuousOn G (Icc 0 b) :=
    jacobi_boundary_potential_continuousOn g C hC R I q h0 D hsub hfc
  have hG0 : G 0 = 0 := by simp only [G,D.initial_A,zero_apply,map_zero,LinearMap.zero_apply]
  have hGb : G b = 0 := by simp only [G,hfb,map_zero]
  have hγ := geodesic_smoothVariation C I q hq hsub
  have heint : IntervalIntegrable
      (indexIntegrand g C R (fun t => (q t).1) 0 b W W) volume 0 b := by
    have hγn : P202.FirstVariationData.SmoothVariationOn S (fun z => (q z.2).1) 1
        (node 0) (node (Fin.last (k+1))) := by simpa only [hn0,hnb] using hγ
    simpa only [hn0,hnb] using SecondVariation.indexIntegrand_piecewise_intervalIntegrable
      g C R node hnode hγn hpieces hpieces
  have hec : ContinuousOn (indexIntegrand g C R (fun t => (q t).1) 0 b W W)
      (Ioo 0 b \ (breaks : Set ℝ)) := by
    have hγn : P202.FirstVariationData.SmoothVariationOn S (fun z => (q z.2).1) 1
        (node 0) (node (Fin.last (k+1))) := by simpa only [hn0,hnb] using hγ
    simpa only [hn0,hnb,breaks] using indexIntegrand_piecewise_continuousOn
      g C R node hnode hγn hpieces hpieces
  have hGder : ∀ t ∈ Ioo 0 b, t ∉ breaks →
      HasDerivAt G
        (indexIntegrand g C R (fun s => (q s).1) 0 b W W t -
          H (D.A t (deriv f t)) (D.A t (deriv f t))) t := by
    intro t ht hts
    have hs := jacobi_square_indexIntegrand g C hC R hR I q hq h0 D hb hsub
      (Ioo_subset_Icc_self ht) (segmentTangent_eq_phase C I q hq hb hsub (Ioo_subset_Icc_self ht))
      (hfDiff t ht hts).hasDerivAt hWrepr
    rw [parallel_frame_pairing_constant g C hC R I q h0 D t (hsub (Ioo_subset_Icc_self ht))] at hs
    exact hs
  have hresult := coefficient_integral_nonneg_eq_zero breaks hb D.A H hHnonneg hHzero
    heint hec hGc hG0 hGb hGder (hfc.mono Ioc_subset_Icc_self) hfb
    (fun t ht hts => (hfDiff t ht hts).hasDerivAt)
    (fun t ht _ => (hu t ⟨ht.1,ht.2.le⟩).1)
  refine ⟨hresult.1, ?_⟩
  intro hzero t ht
  by_cases ht0 : t = 0
  · subst t
    exact hW0
  · have htpos : t ∈ Ioc 0 b := ⟨lt_of_le_of_ne ht.1 (Ne.symm ht0),ht.2⟩
    rw [hWrepr t ht, hresult.2 hzero t htpos, map_zero,map_zero]

/-- The index lemma, including arbitrary terminal vectors and the full
piecewise C¹ comparison and equality case on the closed segment. -/
theorem index_lemma : P202Specs.Geometry.IndexLemma.index_lemmaType.{u} :=
  index_lemma_from_nonnegative zero_endpoint_nonnegative

/-- Strict positive-definiteness on nonzero zero-endpoint fields. -/
theorem positive_definite : P202Specs.Geometry.IndexLemma.positive_definiteType.{u} :=
  positive_definite_from_nonnegative zero_endpoint_nonnegative

end P202.Geometry.IndexLemma
