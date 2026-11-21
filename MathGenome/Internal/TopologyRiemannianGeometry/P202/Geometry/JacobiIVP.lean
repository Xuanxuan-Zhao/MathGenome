import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.JacobiIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GeodesicIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.CurvatureAlgebra
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ParallelTransport
import Mathlib.Analysis.Normed.Operator.Prod
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 800000

namespace P202.Geometry.JacobiIVP
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData
  P202.LeviCivitaData P202.GeodesicData P202.CurvatureData P202.JacobiData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

abbrev IsJacobiField := @P202.JacobiData.IsJacobiField
noncomputable abbrev tangentialPart := @P202.JacobiData.tangentialPart
noncomputable abbrev normalPart := @P202.JacobiData.normalPart

/-- The radial curvature operator kills velocity. -/
theorem curvature_velocity_self (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (p : M) (v : TangentSpace S p) : R.val p v v v = 0 := by
  obtain ⟨X, hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) p v
  have h := congrArg (fun Z : Field S => Z.val p) (CurvatureAlgebra.curvature_skew C X X X)
  rw [ConnectionForms.section_smul_apply, ← hR X X X p, hX, neg_one_smul] at h
  have hadd : R.val p v v v + R.val p v v v = 0 := eq_neg_iff_add_eq_zero.mp h
  have htwo : (2 : ℝ) • R.val p v v v = 0 := by
    simpa only [two_smul] using hadd
  exact (smul_eq_zero.mp htwo).resolve_left (by norm_num)

/-- Affine velocity fields satisfy the equation directly. -/
theorem affine_velocity : P202Specs.Geometry.JacobiIVP.affine_velocityType.{u} := by
  intro n M _ S C R hR I q hq a b
  refine ⟨fun t => b • (q t).2, ?_⟩
  intro t ht
  constructor
  · have hd := CurveCovariantDerivative.derivative_smul C (hq t ht).2
      ((((hasDerivAt_id t).const_mul b).const_add a).hasDerivWithinAt)
    simpa using hd
  · have hd := CurveCovariantDerivative.derivative_const_smul C (hq t ht).2 b
    have hr : -(R.val (q t).1 ((a + b * t) • (q t).2) (q t).2 (q t).2) = 0 := by
      simp only [map_smul, LinearMap.smul_apply, curvature_velocity_self C R hR,
        smul_zero]
      exact @neg_zero (TangentSpace S (q t).1) _
    rw [hr]
    simpa only [smul_zero] using hd

/-- Metric skew symmetry makes radial curvature orthogonal to velocity. -/
theorem curvature_radial_orthogonal (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (p : M) (j v : TangentSpace S p) :
    pairing g p (R.val p j v v) v = 0 := by
  have h := CurvatureAlgebra.form_skew_last C g hC.2 R hR p j v v v
  change pairing g p (R.val p j v v) v = -pairing g p (R.val p j v v) v at h
  linarith

theorem jacobi_add (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {I : Set ℝ} {q : ℝ → Phase S}
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I q J) (hK : IsJacobiField C R I q K) :
    IsJacobiField C R I q (fun t => J t + K t) := by
  obtain ⟨V, hV⟩ := hJ
  obtain ⟨W, hW⟩ := hK
  refine ⟨fun t => V t + W t, ?_⟩
  intro t ht
  constructor
  · exact CurveCovariantDerivative.derivative_add C (mem_univ t)
      uniqueDiffWithinAt_univ (hV t ht).1 (hW t ht).1
  · have heq : -(R.val (q t).1 (J t + K t) (q t).2 (q t).2) =
        -(R.val (q t).1 (J t) (q t).2 (q t).2) +
        -(R.val (q t).1 (K t) (q t).2 (q t).2) := by
      simp only [map_add, LinearMap.add_apply]
      exact neg_add (R.val (q t).1 (J t) (q t).2 (q t).2)
        (R.val (q t).1 (K t) (q t).2 (q t).2)
    rw [heq]
    exact CurveCovariantDerivative.derivative_add C (mem_univ t)
      uniqueDiffWithinAt_univ (hV t ht).2 (hW t ht).2

theorem jacobi_smul (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {I : Set ℝ} {q : ℝ → Phase S}
    {J : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I q J) (a : ℝ) :
    IsJacobiField C R I q (fun t => a • J t) := by
  obtain ⟨V, hV⟩ := hJ
  refine ⟨fun t => a • V t, ?_⟩
  intro t ht
  constructor
  · exact CurveCovariantDerivative.derivative_const_smul C (hV t ht).1 a
  · have heq : -(R.val (q t).1 (a • J t) (q t).2 (q t).2) =
        a • -(R.val (q t).1 (J t) (q t).2 (q t).2) := by
      simp only [map_smul, LinearMap.smul_apply]
      exact (smul_neg a (R.val (q t).1 (J t) (q t).2 (q t).2)).symm
    rw [heq]
    exact CurveCovariantDerivative.derivative_const_smul C (hV t ht).2 a

theorem jacobi_sub (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {I : Set ℝ} {q : ℝ → Phase S}
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : IsJacobiField C R I q J) (hK : IsJacobiField C R I q K) :
    IsJacobiField C R I q (fun t => J t - K t) := by
  have heq : (fun t => J t - K t) = (fun t => J t + (-1 : ℝ) • K t) := by
    funext t
    exact (sub_eq_add_neg (J t) (K t)).trans
      (congrArg (fun z : TangentSpace S (q t).1 => J t + z) (neg_one_smul ℝ (K t)).symm)
  rw [heq]
  exact jacobi_add C R hJ (jacobi_smul C R hK (-1))

/-- Ambient representatives need agree only on the open parameter interval. -/
theorem jacobi_congr (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {I : Set ℝ} (hI : IsOpen I) {q : ℝ → Phase S}
    {J K : (t : ℝ) → TangentSpace S (q t).1}
    (heq : ∀ t ∈ I, J t = K t) (hJ : IsJacobiField C R I q J) :
    IsJacobiField C R I q K := by
  obtain ⟨V, hV⟩ := hJ
  refine ⟨V, ?_⟩
  intro t ht
  constructor
  · apply ParallelTransport.derivative_field_congr C (mem_univ t) _ (hV t ht).1
    simp only [nhdsWithin_univ]
    filter_upwards [hI.mem_nhds ht] with s hs
    exact heq s hs
  · simpa only [← heq t ht] using (hV t ht).2

/-- The nonconstant hypothesis implies nonzero speed at every time; this
uses intrinsic geodesic uniqueness, rather than adding a speed hypothesis. -/
theorem velocity_ne_zero (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (hn : NonconstantOn I.carrier q)
    (t : ℝ) (ht : t ∈ I.carrier) : (q t).2 ≠ 0 := by
  intro hz
  have hmeet : q t = constantCurve S (q t).1 t := by
    have hx : (q t).2 = (constantCurve S (q t).1 t).2 := hz
    exact Sigma.ext rfl (heq_of_eq hx)
  have heq := GeodesicIVP.overlap_unique S C I D13Unified.OpenTimeInterval.whole
    q (constantCurve S (q t).1) hq (GeodesicIVP.constant_is_geodesic C (q t).1)
    t ⟨ht, mem_univ t⟩ hmeet
  obtain ⟨s, hs, r, hr, hsr⟩ := hn
  apply hsr
  exact (congrArg Sigma.fst (heq ⟨hs, mem_univ s⟩)).trans
    (congrArg Sigma.fst (heq ⟨hr, mem_univ r⟩)).symm

/-- A scalar function with a derivative whose derivative vanishes on a
connected open interval is affine on the entire interval. -/
theorem scalar_affine (I : D13Unified.OpenTimeInterval) (f h : ℝ → ℝ)
    (hf : ∀ t ∈ I.carrier, HasDerivAt f (h t) t)
    (hh : ∀ t ∈ I.carrier, HasDerivAt h 0 t) :
    ∃ a b : ℝ, ∀ t ∈ I.carrier, f t = a + b * t := by
  obtain ⟨b, hb⟩ := I.isOpen.exists_is_const_of_deriv_eq_zero I.ordConnected.isPreconnected
    (fun t ht => (hh t ht).differentiableAt.differentiableWithinAt)
    (fun t ht => (hh t ht).deriv)
  obtain ⟨a, ha⟩ := I.isOpen.exists_eq_add_of_deriv_eq I.ordConnected.isPreconnected
    (fun t ht => (hf t ht).differentiableAt.differentiableWithinAt)
    (f := f) (g := fun t => b * t)
    (fun t _ => ((hasDerivAt_id t).const_mul b).differentiableAt.differentiableWithinAt)
    (fun t ht => by rw [(hf t ht).deriv, hb t ht]; simpa using ((hasDerivAt_id t).const_mul b).deriv.symm)
  refine ⟨a, b, ?_⟩
  intro t ht
  simpa only [add_comm] using ha ht

/-- The metric component along velocity has zero second derivative. -/
theorem pairing_velocity_affine (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) :
    ∃ a b : ℝ, ∀ t ∈ I.carrier,
      pairing g (q t).1 (J t) (q t).2 = a + b * t := by
  obtain ⟨V, hV⟩ := hJ
  apply scalar_affine I _ (fun t => pairing g (q t).1 (V t) (q t).2)
  · intro t ht
    have hd := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ t) uniqueDiffWithinAt_univ (hV t ht).1 (hq t ht).2
    simpa only [pairing, hasDerivWithinAt_univ, map_zero, add_zero] using hd
  · intro t ht
    have hd := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ t) uniqueDiffWithinAt_univ (hV t ht).2 (hq t ht).2
    have hz := curvature_radial_orthogonal g C hC R hR (q t).1 (J t) (q t).2
    have heq : pairing g (q t).1 (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (q t).2 = 0 := by
      rw [LinearMap.BilinForm.neg_left (B₁ := pairing g (q t).1)
        (R.val (q t).1 (J t) (q t).2 (q t).2) (q t).2, hz, neg_zero]
    change HasDerivWithinAt (fun s => pairing g (q s).1 (V s) (q s).2)
      (pairing g (q t).1 (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (q t).2 +
        pairing g (q t).1 (V t) 0) univ t at hd
    rw [heq, LinearMap.BilinForm.zero_right (B := pairing g (q t).1) (V t), zero_add] at hd
    exact hasDerivWithinAt_univ.mp hd

/-- No normalization to unit speed is imposed. -/
theorem speed_sq_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {s t : ℝ}
    (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    pairing g (q s).1 (q s).2 (q s).2 = pairing g (q t).1 (q t).2 (q t).2 := by
  have h := congrArg (fun z : ℝ => z ^ 2)
    (GeodesicIVP.speed_is_constant g C hC I q hq hs ht)
  simpa only [SmoothMetrics.tangentNorm_sq] using h

/-- Pointwise orthogonality follows from the actual metric projection. -/
theorem normalPart_orthogonal (g : RiemannianMetric S) (q : ℝ → Phase S)
    (J : (t : ℝ) → TangentSpace S (q t).1) (t : ℝ) (hv : (q t).2 ≠ 0) :
    pairing g (q t).1 (normalPart g q J t) (q t).2 = 0 := by
  have hden : pairing g (q t).1 (q t).2 (q t).2 ≠ 0 :=
    ne_of_gt (g.positive (q t).1 (q t).2 hv)
  change pairing g (q t).1
    (J t - (pairing g (q t).1 (J t) (q t).2 /
      pairing g (q t).1 (q t).2 (q t).2) • (q t).2) (q t).2 = 0
  rw [LinearMap.BilinForm.sub_left (B₁ := pairing g (q t).1)
    (J t) ((pairing g (q t).1 (J t) (q t).2 /
      pairing g (q t).1 (q t).2 (q t).2) • (q t).2) (q t).2]
  rw [LinearMap.BilinForm.smul_left (B := pairing g (q t).1)
    (pairing g (q t).1 (J t) (q t).2 / pairing g (q t).1 (q t).2 (q t).2)
    (q t).2 (q t).2]
  rw [div_mul_cancel₀ _ hden, sub_self]

/-- The complete nonconstant tangential/normal decomposition, on the full
original geodesic interval. -/
theorem decomposition : P202Specs.Geometry.JacobiIVP.decompositionType.{u} := by
  intro n M _ S g C hC R hR I q hq hn J hJ
  obtain ⟨a, b, hab⟩ := pairing_velocity_affine g C hC R hR I q hq J hJ
  obtain ⟨s, hs⟩ := I.nonempty
  let k := pairing g (q s).1 (q s).2 (q s).2
  have htan (t : ℝ) (ht : t ∈ I.carrier) :
      tangentialPart g q J t = (a / k + (b / k) * t) • (q t).2 := by
    change (pairing g (q t).1 (J t) (q t).2 /
      pairing g (q t).1 (q t).2 (q t).2) • (q t).2 = _
    rw [hab t ht, ← speed_sq_constant g C hC I q hq hs ht]
    congr 1
    dsimp only [k]
    ring
  have hjtan : IsJacobiField C R I.carrier q (tangentialPart g q J) :=
    jacobi_congr C R I.isOpen (fun t ht => (htan t ht).symm)
      (affine_velocity S C R hR I.carrier q hq (a / k) (b / k))
  refine ⟨⟨a / k, b / k, htan⟩, hjtan, ?_, ?_⟩
  · exact jacobi_sub C R hJ hjtan
  · intro t ht
    exact normalPart_orthogonal g q J t (velocity_ne_zero C I q hq hn t ht)

/-- The actual phase curve of an intrinsic geodesic is smooth; in particular,
its position has the C¹ coordinate extensions required by compact transport. -/
theorem geodesic_coordinateC1 (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) :
    P202.CurveData.CoordinateC1On S (fun t => (q t).1) I.carrier := by
  obtain ⟨G, _, hbridge⟩ := GeodesicIVP.spray_exists S C
  have hqi := (hbridge I q).mpr hq
  have hphase : P202.CurveData.CoordinateC1On (phaseManifold S) q I.carrier := by
    intro t ht
    obtain ⟨e, he, hp⟩ := (phaseManifold S).smoothStructure.property.1.1 (q t)
    exact ⟨e, he, hp, (fun s => (e (q s)).val),
      ((hqi.2 t ht e he hp).1.of_le (by simp)), rfl, Filter.EventuallyEq.rfl⟩
  exact PiecewiseCurves.CoordinateC1On.postcomp
    (SmoothManifolds.TangentBundle.projection_smooth S (tangentStructure S)) hqi.1 hphase

/-- A within covariant derivative is an ordinary one at an interior time. -/
theorem covariantDerivativeAt_of_mem_nhds (C : Connection (tangentBundle S))
    {c : ℝ → M} {f : (t : ℝ) → TangentSpace S (c t)}
    {K : Set ℝ} {t : ℝ} {D : TangentSpace S (c t)}
    (hK : K ∈ 𝓝 t) (hf : HasCovariantDerivativeWithinAt C c f K t D) :
    HasCovariantDerivativeAt C c f t D := by
  obtain ⟨V, ⟨hc, e, he, hp, hd⟩, U, hU, b, hp', v', hv, hval⟩ := hf
  exact ⟨V, ⟨(hc.continuousAt hK).continuousWithinAt,
      e, he, hp, (hd.hasDerivAt hK).hasDerivWithinAt⟩,
    U, hU, b, hp', v', (hv.hasDerivAt hK).hasDerivWithinAt, hval⟩

/-- Existence of an actual covariant derivative implies continuity of the
field in the original tangent-bundle total space. -/
theorem covariantDerivative_continuousAt (C : Connection (tangentBundle S))
    {c : ℝ → M} {f : (t : ℝ) → TangentSpace S (c t)}
    {t : ℝ} {D : TangentSpace S (c t)}
    (hf : HasCovariantDerivativeAt C c f t D) :
    ContinuousAt (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (SmoothManifolds.ModelData.Euclidean n) (TangentSpace S))) t := by
  obtain ⟨V, hV, U, hU, b, hp, v', hv, _⟩ := hf
  exact (continuousWithinAt_univ _ _).mp
    (ParallelTransport.field_continuousWithinAt_of_coefficients b hp hV.1 hv.continuousWithinAt)

/-- Any two times in an actual open interval lie strictly inside a compact
subinterval of that same domain. No boundedness of the full interval is used. -/
theorem exists_compact_interval (I : D13Unified.OpenTimeInterval)
    {s t : ℝ} (hs : s ∈ I.carrier) (ht : t ∈ I.carrier) :
    ∃ l r : ℝ, l < min s t ∧ max s t < r ∧ Icc l r ⊆ I.carrier := by
  obtain ⟨a, b, hab, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds hs)
  obtain ⟨d, e, hde, hsub'⟩ := mem_nhds_iff_exists_Ioo_subset.mp (I.isOpen.mem_nhds ht)
  let l := min ((a + s) / 2) ((d + t) / 2)
  let r := max ((s + b) / 2) ((t + e) / 2)
  have hl : l ∈ I.carrier := by
    rcases le_total ((a + s) / 2) ((d + t) / 2) with h | h
    · apply hsub; dsimp [l]; rw [min_eq_left h]; constructor <;> linarith [hab.1, hab.2]
    · apply hsub'; dsimp [l]; rw [min_eq_right h]; constructor <;> linarith [hde.1, hde.2]
  have hr : r ∈ I.carrier := by
    rcases le_total ((s + b) / 2) ((t + e) / 2) with h | h
    · apply hsub'; dsimp [r]; rw [max_eq_right h]; constructor <;> linarith [hde.1, hde.2]
    · apply hsub; dsimp [r]; rw [max_eq_left h]; constructor <;> linarith [hab.1, hab.2]
  refine ⟨l, r, ?_, ?_, I.ordConnected.out hl hr⟩
  · exact lt_min (lt_of_le_of_lt (min_le_left _ _) (by linarith [hab.1]))
      (lt_of_le_of_lt (min_le_right _ _) (by linarith [hde.1]))
  · exact max_lt (lt_of_lt_of_le (by linarith [hab.2]) (le_max_left _ _))
      (lt_of_lt_of_le (by linarith [hde.2]) (le_max_right _ _))

section LinearODE
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

/-- The first-order operator for j'' + A(t) j = 0. -/
noncomputable def secondOrderOperator (A : F →L[ℝ] F) : F × F →L[ℝ] F × F :=
  (ContinuousLinearMap.snd ℝ F F).prod
    (-(A.comp (ContinuousLinearMap.fst ℝ F F)))

@[simp] theorem secondOrderOperator_apply (A : F →L[ℝ] F) (x : F × F) :
    secondOrderOperator A x = (x.2, -(A x.1)) := rfl

theorem secondOrderOperator_continuousOn (I : Set ℝ) (A : ℝ → F →L[ℝ] F)
    (hA : ContinuousOn A I) : ContinuousOn (fun t => secondOrderOperator (A t)) I := by
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
    (continuousOn_const.prodMk (hA.clm_comp continuousOn_const).neg)

/-- The entire analytic IVP in fixed parallel coordinates. The geometric
construction and regularity of A are separate obligations. -/
theorem second_order_linear_ivp (I : D13Unified.OpenTimeInterval)
    (A : ℝ → F →L[ℝ] F) (hA : ContinuousOn A I.carrier)
    (s : ℝ) (hs : s ∈ I.carrier) (u w : F) :
    ∃ j v : ℝ → F, j s = u ∧ v s = w ∧
      (∀ t ∈ I.carrier, HasDerivAt j (v t) t ∧ HasDerivAt v (-(A t (j t))) t) ∧
      ∀ k z : ℝ → F, k s = u → z s = w →
        (∀ t ∈ I.carrier, HasDerivAt k (z t) t ∧ HasDerivAt z (-(A t (k t))) t) →
        ∀ t ∈ I.carrier, k t = j t ∧ z t = v t := by
  obtain ⟨Y, hYc, hYs, hYd, _, _, hYu⟩ :=
    D13Unified.Ch07.LinearSystemExistence.existence I.toTimeInterval
      (fun t => secondOrderOperator (A t)) s (u, w) hs
      (secondOrderOperator_continuousOn I.carrier A hA)
  have hd (t : ℝ) (ht : t ∈ I.carrier) :
      HasDerivAt Y ((Y t).2, -(A t (Y t).1)) t :=
    (hYd t ht).hasDerivAt (I.isOpen.mem_nhds ht)
  refine ⟨fun t => (Y t).1, fun t => (Y t).2,
    congrArg Prod.fst hYs, congrArg Prod.snd hYs, ?_, ?_⟩
  · intro t ht
    exact ⟨(ContinuousLinearMap.fst ℝ F F).hasFDerivAt.comp_hasDerivAt t (hd t ht),
      (ContinuousLinearMap.snd ℝ F F).hasFDerivAt.comp_hasDerivAt t (hd t ht)⟩
  · intro k z hks hzs hkd t ht
    have heq := hYu (fun t => (k t, z t))
      (fun r hr => ((hkd r hr).1.continuousAt.prodMk
        (hkd r hr).2.continuousAt).continuousWithinAt)
      (Prod.ext hks hzs)
      (fun r hr => ((hkd r hr).1.prodMk (hkd r hr).2).hasDerivWithinAt)
    exact ⟨congrArg Prod.fst (heq ht), congrArg Prod.snd (heq ht)⟩
end LinearODE

/-- Compact parallel fields agree wherever both compact domains contain the
initial and terminal times. -/
theorem compact_parallel_eq (C : Connection (tangentBundle S))
    {I : Set ℝ} {c : ℝ → M} (hc1 : P202.CurveData.CoordinateC1On S c I)
    (hc : ContinuousOn c I) {a b l r s t : ℝ}
    (hab : Icc a b ⊆ I) (hlr : Icc l r ⊆ I)
    {f g : (t : ℝ) → TangentSpace S (c t)}
    (hf : ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace
      (SmoothManifolds.ModelData.Euclidean n) (TangentSpace S))) (Icc a b))
    (hg : ContinuousOn (fun t => (⟨c t, g t⟩ : Bundle.TotalSpace
      (SmoothManifolds.ModelData.Euclidean n) (TangentSpace S))) (Icc l r))
    (hfd : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C c f (Icc a b) t 0)
    (hgd : ∀ t ∈ Icc l r, HasCovariantDerivativeWithinAt C c g (Icc l r) t 0)
    (hs : s ∈ Icc a b) (hs' : s ∈ Icc l r)
    (ht : t ∈ Icc a b) (ht' : t ∈ Icc l r) (hinit : f s = g s) :
    f t = g t := by
  have hsub : Icc (max a l) (min b r) ⊆ Icc a b := by
    intro x hx
    exact ⟨(le_max_left a l).trans hx.1, hx.2.trans (min_le_left b r)⟩
  have hsub' : Icc (max a l) (min b r) ⊆ Icc l r := by
    intro x hx
    exact ⟨(le_max_right a l).trans hx.1, hx.2.trans (min_le_right b r)⟩
  have hs'' : s ∈ Icc (max a l) (min b r) :=
    ⟨max_le hs.1 hs'.1, le_min hs.2 hs'.2⟩
  exact ParallelTransport.parallel_unique_on_piece C (hs''.1.trans hs''.2)
    (PiecewiseCurves.CoordinateC1On.mono hc1 (hsub.trans hab))
    (hc.mono (hsub.trans hab)) (hf.mono hsub) (hg.mono hsub')
    (fun x hx => ParallelTransport.covariantDerivative_mono (hfd x (hsub hx)) hsub)
    (fun x hx => ParallelTransport.covariantDerivative_mono (hgd x (hsub' hx)) hsub')
    hs'' hinit t ⟨max_le ht.1 ht'.1, le_min ht.2 ht'.2⟩

/-- Actual parallel fields on the whole open parameter interval. -/
theorem global_parallel_ivp (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (ξ : TangentSpace S (q s).1) :
    ∃ f : (t : ℝ) → TangentSpace S (q t).1, f s = ξ ∧
      (∀ t ∈ I.carrier, HasCovariantDerivativeAt C (fun t => (q t).1) f t 0) ∧
      ∀ g : (t : ℝ) → TangentSpace S (q t).1, g s = ξ →
        (∀ t ∈ I.carrier, HasCovariantDerivativeAt C (fun t => (q t).1) g t 0) →
        ∀ t ∈ I.carrier, g t = f t := by
  classical
  let c : ℝ → M := fun t => (q t).1
  have hc1 := geodesic_coordinateC1 C I q hq
  have hc : ContinuousOn c I.carrier := fun t ht =>
    ((hq t ht).1.1.continuousAt (by simp)).continuousWithinAt
  have hlocal : ∀ t : I.carrier, ∃ l r : ℝ,
      ∃ f : (u : ℝ) → TangentSpace S (c u),
      l < min s t.val ∧ max s t.val < r ∧ Icc l r ⊆ I.carrier ∧
      ContinuousOn (fun t => (⟨c t, f t⟩ : Bundle.TotalSpace
        (SmoothManifolds.ModelData.Euclidean n) (TangentSpace S))) (Icc l r) ∧
      f s = ξ ∧ ∀ u ∈ Icc l r,
        HasCovariantDerivativeWithinAt C c f (Icc l r) u 0 := by
    intro t
    obtain ⟨l, r, hl, hr, hsub⟩ := exists_compact_interval I hs t.property
    have hls : l < s := hl.trans_le (min_le_left _ _)
    have hsr : s < r := (le_max_left _ _).trans_lt hr
    obtain ⟨f, hf, _, hfs, hfd⟩ := ParallelTransport.parallel_exists_on_piece C
      (hls.trans hsr).le (PiecewiseCurves.CoordinateC1On.mono hc1 hsub)
      (hc.mono hsub) ⟨hls.le, hsr.le⟩ ξ
    exact ⟨l, r, f, hl, hr, hsub, hf, hfs, hfd (hls.trans hsr)⟩
  choose l r F hl hr hsub hcont hinit hd using hlocal
  let f : (t : ℝ) → TangentSpace S (q t).1 := fun t =>
    if ht : t ∈ I.carrier then F ⟨t, ht⟩ t else 0
  have hsmem (t : I.carrier) : s ∈ Icc (l t) (r t) :=
    ⟨(hl t).le.trans (min_le_left _ _), (le_max_left _ _).trans (hr t).le⟩
  have htmem (t : I.carrier) : t.val ∈ Icc (l t) (r t) :=
    ⟨(hl t).le.trans (min_le_right _ _), (le_max_right _ _).trans (hr t).le⟩
  have hcongr (t : I.carrier) (u : ℝ) (hu : u ∈ Icc (l t) (r t)) :
      f u = F t u := by
    have hui := hsub t hu
    dsimp only [f]
    rw [dite_eq_left hui]
    exact compact_parallel_eq C hc1 hc (hsub ⟨u, hui⟩) (hsub t)
      (hcont ⟨u, hui⟩) (hcont t) (hd ⟨u, hui⟩) (hd t)
      (hsmem ⟨u, hui⟩) (hsmem t) (htmem ⟨u, hui⟩) hu
      ((hinit ⟨u, hui⟩).trans (hinit t).symm)
  have hfd : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) f t 0 := by
    intro t ht
    let T : I.carrier := ⟨t, ht⟩
    have hneigh : Icc (l T) (r T) ∈ 𝓝 t := Icc_mem_nhds
      ((hl T).trans_le (min_le_right _ _)) ((le_max_right _ _).trans_lt (hr T))
    have heq : ∀ᶠ u in 𝓝[univ] t, F T u = f u := by
      rw [nhdsWithin_univ]
      filter_upwards [hneigh] with u hu
      exact (hcongr T u hu).symm
    exact ParallelTransport.derivative_field_congr C (mem_univ t) heq
      (covariantDerivativeAt_of_mem_nhds C hneigh (hd T t (htmem T)))
  refine ⟨f, ?_, hfd, ?_⟩
  · dsimp only [f]
    rw [dite_eq_left hs]
    exact hinit ⟨s, hs⟩
  · intro g hgs hgd t ht
    let T : I.carrier := ⟨t, ht⟩
    have hgc : ContinuousOn (fun u => (⟨c u, g u⟩ : Bundle.TotalSpace
        (SmoothManifolds.ModelData.Euclidean n) (TangentSpace S))) (Icc (l T) (r T)) := by
      intro u hu
      exact (covariantDerivative_continuousAt C (hgd u (hsub T hu))).continuousWithinAt
    have heq : g t = F T t := ParallelTransport.parallel_unique_on_piece C
      ((hsmem T).1.trans (hsmem T).2)
      (PiecewiseCurves.CoordinateC1On.mono hc1 (hsub T)) (hc.mono (hsub T))
      hgc (hcont T)
      (fun u hu => ParallelTransport.covariantDerivative_mono
        (hgd u (hsub T hu)) (subset_univ _))
      (hd T) (hsmem T) (hgs.trans (hinit T).symm) t (htmem T)
    exact heq.trans (hcongr T t (htmem T)).symm


noncomputable def globalParallelField (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (ξ : TangentSpace S (q s).1) : (t : ℝ) → TangentSpace S (q t).1 :=
  Classical.choose (global_parallel_ivp C I q hq s hs ξ)

theorem globalParallelField_initial (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (ξ : TangentSpace S (q s).1) : globalParallelField C I q hq s hs ξ s = ξ :=
  (Classical.choose_spec (global_parallel_ivp C I q hq s hs ξ)).1

theorem globalParallelField_parallel (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (ξ : TangentSpace S (q s).1) : ∀ t ∈ I.carrier,
    HasCovariantDerivativeAt C (fun t => (q t).1)
      (globalParallelField C I q hq s hs ξ) t 0 :=
  (Classical.choose_spec (global_parallel_ivp C I q hq s hs ξ)).2.1

theorem globalParallelField_unique (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (ξ : TangentSpace S (q s).1) (f : (t : ℝ) → TangentSpace S (q t).1)
    (hfs : f s = ξ) (hfd : ∀ t ∈ I.carrier,
      HasCovariantDerivativeAt C (fun t => (q t).1) f t 0) :
    ∀ t ∈ I.carrier, f t = globalParallelField C I q hq s hs ξ t :=
  (Classical.choose_spec (global_parallel_ivp C I q hq s hs ξ)).2.2 f hfs hfd

/-- Initial-fiber evolution as an actual linear map on every relevant fiber. -/
noncomputable def parallelEvolutionLinearMap (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) :
    TangentSpace S (q s).1 →ₗ[ℝ] TangentSpace S (q t).1 where
  toFun := fun ξ => globalParallelField C I q hq s hs ξ t
  map_add' := by
    intro ξ η
    symm
    apply globalParallelField_unique C I q hq s hs (ξ + η)
      (fun t => globalParallelField C I q hq s hs ξ t +
        globalParallelField C I q hq s hs η t) _ _ t ht
    · rw [globalParallelField_initial, globalParallelField_initial]
    · intro u hu
      simpa only [add_zero] using CurveCovariantDerivative.derivative_add C
        (mem_univ u) uniqueDiffWithinAt_univ
        (globalParallelField_parallel C I q hq s hs ξ u hu)
        (globalParallelField_parallel C I q hq s hs η u hu)
  map_smul' := by
    intro a ξ
    symm
    apply globalParallelField_unique C I q hq s hs (a • ξ)
      (fun t => a • globalParallelField C I q hq s hs ξ t) _ _ t ht
    · rw [globalParallelField_initial]
    · intro u hu
      simpa only [smul_zero] using CurveCovariantDerivative.derivative_const_smul C
        (globalParallelField_parallel C I q hq s hs ξ u hu) a

theorem parallelEvolutionLinearMap_bijective (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) :
    Function.Bijective (parallelEvolutionLinearMap C I q hq s hs t ht) := by
  constructor
  · intro ξ η heq
    let F := globalParallelField C I q hq s hs ξ
    let G := globalParallelField C I q hq s hs η
    have hf : F t = G t := heq
    have hfg := globalParallelField_unique C I q hq t ht (G t) F hf
      (globalParallelField_parallel C I q hq s hs ξ)
    have hgg := globalParallelField_unique C I q hq t ht (G t) G rfl
      (globalParallelField_parallel C I q hq s hs η)
    have h := (hfg s hs).trans (hgg s hs).symm
    simpa only [F, G, globalParallelField_initial] using h
  · intro η
    let G := globalParallelField C I q hq t ht η
    refine ⟨G s, ?_⟩
    have heq := globalParallelField_unique C I q hq s hs (G s) G rfl
      (globalParallelField_parallel C I q hq t ht η) t ht
    exact heq.symm.trans (globalParallelField_initial C I q hq t ht η)

/-- Arbitrary coordinates only totalize formulas away from the given domain. -/
noncomputable def tangentCoordinates (p : M) :
    SmoothManifolds.ModelData.Euclidean n ≃ₗ[ℝ] TangentSpace S p :=
  Classical.choice (by
    obtain ⟨U, hU, hp, ⟨b⟩⟩ :=
      SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) p
    exact ⟨(b.basis ⟨p, hp⟩).equivFun.symm⟩)

/-- Coordinates of the whole interval obtained from actual parallel transport. -/
noncomputable def intervalParallelEquiv (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (t : ℝ) : SmoothManifolds.ModelData.Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1 := by
  classical
  exact if ht : t ∈ I.carrier then
    (tangentCoordinates (q s).1).trans
      (LinearEquiv.ofBijective (parallelEvolutionLinearMap C I q hq s hs t ht)
        (parallelEvolutionLinearMap_bijective C I q hq s hs t ht))
    else tangentCoordinates (q t).1

theorem intervalParallelEquiv_apply (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (t : ℝ) (ht : t ∈ I.carrier) (x : SmoothManifolds.ModelData.Euclidean n) :
    intervalParallelEquiv C I q hq s hs t x =
      globalParallelField C I q hq s hs (tangentCoordinates (q s).1 x) t := by
  classical
  simp only [intervalParallelEquiv, dite_eq_left ht, LinearEquiv.trans_apply,
    LinearEquiv.ofBijective_apply, parallelEvolutionLinearMap, LinearMap.coe_mk,
    AddHom.coe_mk]

theorem intervalParallelEquiv_parallel (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (s : ℝ) (hs : s ∈ I.carrier)
    (x : SmoothManifolds.ModelData.Euclidean n) : ∀ t ∈ I.carrier,
    HasCovariantDerivativeAt C (fun t => (q t).1)
      (fun t => intervalParallelEquiv C I q hq s hs t x) t 0 := by
  intro t ht
  apply ParallelTransport.derivative_field_congr C (mem_univ t) _
    (globalParallelField_parallel C I q hq s hs (tangentCoordinates (q s).1 x) t ht)
  rw [nhdsWithin_univ]
  filter_upwards [I.isOpen.mem_nhds ht] with u hu
  exact (intervalParallelEquiv_apply C I q hq s hs u hu x).symm


/-- Finite coordinate expansion for any fiber equivalence. -/
theorem equivalence_expansion {V : Type*} [AddCommMonoid V] [Module ℝ V]
    (e : Euclidean n ≃ₗ[ℝ] V) (v : Euclidean n) :
    e v = ∑ i : Fin n, v i • e (Pi.single i 1) := by
  simpa only [map_sum, map_smul, Pi.basisFun_apply,
    Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
    congrArg e ((Pi.basisFun ℝ (Fin n)).sum_equivFun v).symm

/-- Differentiation in a finite parallel frame, in the forward direction. -/
theorem derivative_parallel_expansion (C : Connection (tangentBundle S))
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} {V : TangentSpace S (c t)}
    (hc : HasVelocityWithinAt S c univ t V)
    (hP : ∀ i : Fin n, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t 0)
    {j : ℝ → Euclidean n} {w : Euclidean n} (hj : HasDerivAt j w t) :
    HasCovariantDerivativeAt C c (fun s => P s (j s)) t (P t w) := by
  have h := ParallelTransport.derivative_field_finset_sum C (mem_univ t)
    uniqueDiffWithinAt_univ hc Finset.univ
    (fun i s => j s i • P s (Pi.single i 1))
    (fun i => w i • P t (Pi.single i 1)) (fun i _ => by
      simpa only [smul_zero, add_zero] using
        CurveCovariantDerivative.derivative_smul C (hP i)
          ((hasDerivAt_pi.mp hj i).hasDerivWithinAt))
  have heq : (fun s => ∑ i : Fin n, j s i • P s (Pi.single i 1)) =
      (fun s => P s (j s)) := by
    funext s
    exact (equivalence_expansion (V := TangentSpace S (c s)) (P s) (j s)).symm
  rw [heq, ← equivalence_expansion (V := TangentSpace S (c t)) (P t) w] at h
  exact h

/-- A matrix represented as a sum of its column operators. -/
noncomputable def columnOperator (v : Fin n → Euclidean n) :
    Euclidean n →L[ℝ] Euclidean n :=
  ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight (v i)

@[simp] theorem columnOperator_apply (v : Fin n → Euclidean n) (x : Euclidean n) :
    columnOperator v x = ∑ i : Fin n, x i • v i := by
  simp [columnOperator]

theorem differentiableAt_columnOperator {v : ℝ → Fin n → Euclidean n} {t : ℝ}
    (hv : ∀ i, DifferentiableAt ℝ (fun s => v s i) t) :
    DifferentiableAt ℝ (fun s => columnOperator (v s)) t := by
  apply DifferentiableAt.fun_sum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
    (ContinuousLinearMap.proj i)).differentiableAt.comp t (hv i)

/-- Local frame coordinates of a moving fiber equivalence. -/
noncomputable def frameCoordinateOperator
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    (t : ℝ) : Euclidean n →L[ℝ] Euclidean n :=
  columnOperator (fun i => coefficientsAlong b c (fun s => P s (Pi.single i 1)) t)

theorem frameCoordinateOperator_apply
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} (hp : c t ∈ U) (x : Euclidean n) :
    frameCoordinateOperator b P t x = (b.basis ⟨c t, hp⟩).equivFun (P t x) := by
  rw [frameCoordinateOperator, columnOperator_apply]
  calc
    _ = (b.basis ⟨c t, hp⟩).equivFun
        (∑ i : Fin n, x i • P t (Pi.single i 1)) := by
      simp only [map_sum, map_smul]
      apply Finset.sum_congr rfl
      intro i _
      exact congrArg (fun v : Euclidean n => x i • v)
        (CurveCovariantDerivative.coefficientsAlong_of_mem b c
          (fun s => P s (Pi.single i 1)) t hp)
    _ = _ := congrArg (b.basis ⟨c t, hp⟩).equivFun
      (equivalence_expansion (V := TangentSpace S (c t)) (P t) x).symm

/-- The local coordinate matrix of a fiber equivalence is invertible. -/
theorem frameCoordinateOperator_isUnit
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} (hp : c t ∈ U) : IsUnit (frameCoordinateOperator b P t) := by
  apply ContinuousLinearMap.isUnit_iff_bijective.mpr
  have heq : (frameCoordinateOperator b P t : Euclidean n → Euclidean n) =
      ((P t).trans (b.basis ⟨c t, hp⟩).equivFun) := by
    funext x
    exact frameCoordinateOperator_apply b P hp x
  rw [heq]
  exact LinearEquiv.bijective _

/-- The matrix of a differentiable moving frame is differentiable. -/
theorem frameCoordinateOperator_differentiableAt
    (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} (hp : c t ∈ U)
    (hP : ∀ i : Fin n, ∃ D, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t D) :
    DifferentiableAt ℝ (fun s => frameCoordinateOperator b P s) t := by
  apply differentiableAt_columnOperator
  intro i
  obtain ⟨D, hD⟩ := hP i
  obtain ⟨v, hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C (mem_univ t) hD b hp
  exact (hasDerivWithinAt_univ.mp hv).differentiableAt

/-- Inverse moving coordinates are locally the inverse of the local matrix. -/
theorem inverse_coordinates_eventuallyEq
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    (f : (s : ℝ) → TangentSpace S (c s))
    {t : ℝ} (hp : c t ∈ U) (hc : ContinuousAt c t) :
    (fun s => (P s).symm (f s)) =ᶠ[𝓝 t]
      (fun s => Ring.inverse (frameCoordinateOperator b P s) (coefficientsAlong b c f s)) := by
  filter_upwards [hc.eventually (hU.mem_nhds hp)] with s hs
  have h := congrArg (fun L : Euclidean n →L[ℝ] Euclidean n =>
    L ((P s).symm (f s)))
    (Ring.inverse_mul_cancel (frameCoordinateOperator b P s)
      (frameCoordinateOperator_isUnit b P hs))
  change Ring.inverse (frameCoordinateOperator b P s)
    (frameCoordinateOperator b P s ((P s).symm (f s))) = (P s).symm (f s) at h
  rw [frameCoordinateOperator_apply b P hs, LinearEquiv.apply_symm_apply,
    ← CurveCovariantDerivative.coefficientsAlong_of_mem b c f s hs] at h
  exact h.symm

/-- A differentiable field has differentiable coordinates in a parallel frame. -/
theorem inverse_coordinates_differentiableAt (C : Connection (tangentBundle S))
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hP : ∀ i : Fin n, ∃ D, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t D)
    {D : TangentSpace S (c t)} (hf : HasCovariantDerivativeAt C c f t D) :
    DifferentiableAt ℝ (fun s => (P s).symm (f s)) t := by
  obtain ⟨U, hU, hp, ⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) (c t)
  obtain ⟨v, hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C (mem_univ t) hf b hp
  have hQ := frameCoordinateOperator_differentiableAt C b P hp hP
  have hk := (hQ.inverse (frameCoordinateOperator_isUnit b P hp)).clm_apply
    (hasDerivWithinAt_univ.mp hv).differentiableAt
  have hc : ContinuousAt c t := (continuousWithinAt_univ _ _).mp hf.choose_spec.1.1
  exact hk.congr_of_eventuallyEq (inverse_coordinates_eventuallyEq b P f hp hc)

/-- Covariant differentiation is ordinary differentiation in parallel coordinates. -/
theorem derivative_parallel_equiv (C : Connection (tangentBundle S))
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {t : ℝ} {V : TangentSpace S (c t)}
    (hc : HasVelocityWithinAt S c univ t V)
    (hP : ∀ i : Fin n, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t 0)
    (j : ℝ → Euclidean n) (w : Euclidean n) :
    HasDerivAt j w t ↔
      HasCovariantDerivativeAt C c (fun s => P s (j s)) t (P t w) := by
  constructor
  · exact derivative_parallel_expansion C P hc hP
  · intro hf
    have hd := inverse_coordinates_differentiableAt C P (fun i => ⟨0, hP i⟩) hf
    simp only [LinearEquiv.symm_apply_apply] at hd
    have heq := CurveCovariantDerivative.covariantDerivative_unique C
      (mem_univ t) uniqueDiffWithinAt_univ
      (derivative_parallel_expansion C P hc hP hd.hasDerivAt) hf
    have hw := (P t).injective heq
    exact hw ▸ hd.hasDerivAt

/-- Inverse parallel coordinates preserve continuity of an actual field. -/
theorem inverse_coordinates_continuousAt (C : Connection (tangentBundle S))
    {c : ℝ → M} (P : (s : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (c s))
    {f : (s : ℝ) → TangentSpace S (c s)} {t : ℝ}
    (hc : ContinuousAt c t)
    (hP : ∀ i : Fin n, ∃ D, HasCovariantDerivativeAt C c
      (fun s => P s (Pi.single i 1)) t D)
    (hf : ContinuousAt (fun s => (⟨c s, f s⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t) :
    ContinuousAt (fun s => (P s).symm (f s)) t := by
  obtain ⟨U, hU, hp, ⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) (c t)
  have hQ := frameCoordinateOperator_differentiableAt C b P hp hP
  have hv := (continuousWithinAt_univ _ _).mp
    (ParallelTransport.coefficients_continuousWithinAt b hp hf.continuousWithinAt)
  have hk := (hQ.inverse (frameCoordinateOperator_isUnit b P hp)).continuousAt.clm_apply hv
  exact hk.congr_of_eventuallyEq (inverse_coordinates_eventuallyEq b P f hp hc)


theorem vector_coordinates {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {d : ℕ}
    (e : V ≃ₗ[ℝ] Euclidean d) (lam : V →ₗ[ℝ] W) (v : V) :
    lam v = ∑ j : Fin d, e v j • lam (e.symm (Pi.single j 1)) := by
  have he : v = ∑ j : Fin d, e v j • e.symm (Pi.single j 1) := by
    simpa only [map_sum, map_smul, LinearEquiv.symm_apply_apply,
      Pi.basisFun_apply, Pi.basisFun_equivFun, LinearEquiv.refl_apply] using
      (congrArg e.symm ((Pi.basisFun ℝ (Fin d)).sum_equivFun (e v))).symm
  conv_lhs => rw [he, map_sum]
  simp only [map_smul]

theorem trilinear_coordinates {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] {d : ℕ}
    (e : V ≃ₗ[ℝ] Euclidean d) (T : V →ₗ[ℝ] V →ₗ[ℝ] V →ₗ[ℝ] W) (x y z : V) :
    T x y z = ∑ j : Fin d, ∑ k : Fin d, ∑ l : Fin d,
      (e x j * (e y k * e z l)) •
        T (e.symm (Pi.single j 1)) (e.symm (Pi.single k 1)) (e.symm (Pi.single l 1)) := by
  rw [vector_coordinates e T x]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply]
  apply Finset.sum_congr rfl
  intro j _
  rw [vector_coordinates e (T (e.symm (Pi.single j 1))) y]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro k _
  rw [vector_coordinates e (T (e.symm (Pi.single j 1)) (e.symm (Pi.single k 1))) z]
  simp only [Finset.smul_sum, smul_smul]

/-- The coordinate output of an actual smooth curvature tensor is continuous
along any continuous base curve and continuous three tangent fields. -/
theorem curvature_coordinates_continuousAt (R : CurvatureTensor S)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {c : ℝ → M} {f g h : (t : ℝ) → TangentSpace S (c t)} {t : ℝ}
    (hp : c t ∈ (tangentBundle S).baseSet i) (hc : ContinuousAt c t)
    (hf : ContinuousAt (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t)
    (hg : ContinuousAt (fun t => (⟨c t, g t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t)
    (hh : ContinuousAt (fun t => (⟨c t, h t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t) :
    ContinuousAt (fun s => ((tangentBundle S).trivialization i
      ⟨c s, R.val (c s) (f s) (g s) (h s)⟩).2) t := by
  classical
  let B := tangentBundle S
  let cf : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, f s⟩).2
  let cg : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, g s⟩).2
  let ch : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, h s⟩).2
  have hcf : ContinuousAt cf t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, f t⟩ hp).1.comp (f := fun s : ℝ => (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hf
  have hcg : ContinuousAt cg t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, g t⟩ hp).1.comp (f := fun s : ℝ => (⟨c s, g s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hg
  have hch : ContinuousAt ch t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, h t⟩ hp).1.comp (f := fun s : ℝ => (⟨c s, h s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hh
  let a : Fin n → Fin n → Fin n → M → Euclidean n := fun j k l q =>
    ((B.trivialization i) ⟨q, R.val q
      ((B.trivialization i).symm q (Pi.single j 1))
      ((B.trivialization i).symm q (Pi.single k 1))
      ((B.trivialization i).symm q (Pi.single l 1))⟩).2
  have ha (j k l : Fin n) : ContinuousAt (fun s => a j k l (c s)) t :=
    (CurvatureAlgebra.tensor_coordinates_smooth R i j k l (c t) hp).1.comp hc
  have hsum : ContinuousAt
      (fun s => ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (cf s j * (cg s k * ch s l)) • a j k l (c s)) t := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    apply tendsto_finsetSum
    intro l _
    exact (((continuous_apply j).continuousAt.comp hcf).mul (((continuous_apply k).continuousAt.comp hcg).mul ((continuous_apply l).continuousAt.comp hch))).smul (ha j k l)
  apply hsum.congr_of_eventuallyEq
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hc.eventually (ho.mem_nhds hp)] with s hs
  have heq := congrArg (B.fiberCoordinates i (c s) hs)
    (trilinear_coordinates (B.fiberCoordinates i (c s) hs) (R.val (c s)) (f s) (g s) (h s))
  simpa only [map_sum, map_smul,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
    SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
    cf, cg, ch, a] using heq

/-- A continuous coordinate formula and base curve determine actual
continuity in the original tangent total space. -/
theorem tangent_continuousAt_of_coordinates
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {c : ℝ → M} {f : (t : ℝ) → TangentSpace S (c t)} {t : ℝ}
    (hp : c t ∈ (tangentBundle S).baseSet i) (hc : ContinuousAt c t)
    (hf : ContinuousAt (fun s => ((tangentBundle S).trivialization i
      ⟨c s, f s⟩).2) t) :
    ContinuousAt (fun s => (⟨c s, f s⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t := by
  let B := tangentBundle S
  let e := B.trivialization i
  let a : ℝ → Euclidean n := fun s => (e ⟨c s, f s⟩).2
  have hp' : c t ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hp
  have hecont : ContinuousAt e.toOpenPartialHomeomorph.symm (c t, a t) :=
    e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hp')
  apply (hecont.comp (f := fun s => (c s, a s)) (x := t) (hc.prodMk hf)).congr_of_eventuallyEq
  filter_upwards [hc.eventually (e.open_baseSet.mem_nhds hp')] with s hs
  have hse : (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)) ∈ e.source :=
    e.mem_source.mpr hs
  have heq : (c s, a s) = e ⟨c s, f s⟩ := by
    apply Prod.ext
    · exact (e.coe_fst hse).symm
    · rfl
  change (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)) =
    e.toOpenPartialHomeomorph.symm (c s, a s)
  rw [heq]
  exact (e.toOpenPartialHomeomorph.left_inv hse).symm

/-- Curvature evaluation preserves total-space continuity along curves. -/
theorem curvature_continuousAt (R : CurvatureTensor S)
    {c : ℝ → M} {f g h : (t : ℝ) → TangentSpace S (c t)} {t : ℝ}
    (hc : ContinuousAt c t)
    (hf : ContinuousAt (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t)
    (hg : ContinuousAt (fun t => (⟨c t, g t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t)
    (hh : ContinuousAt (fun t => (⟨c t, h t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t) :
    ContinuousAt (fun s => (⟨c s, R.val (c s) (f s) (g s) (h s)⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) t := by
  obtain ⟨i, hi⟩ := (tangentBundle S).covers (c t)
  exact tangent_continuousAt_of_coordinates i hi hc
    (curvature_coordinates_continuousAt R i hi hc hf hg hh)

/-- Continuity of the finite sum of its columns, in operator norm. -/
theorem columnOperator_continuousAt {v : ℝ → Fin n → Euclidean n} {t : ℝ}
    (hv : ∀ i, ContinuousAt (fun s => v s i) t) :
    ContinuousAt (fun s => columnOperator (v s)) t := by
  apply tendsto_finsetSum
  intro i _
  exact (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
    (ContinuousLinearMap.proj i)).continuous.continuousAt.comp (hv i)

/-- The actual radial curvature coefficient in the moving parallel coordinates. -/
noncomputable def radialCoordinateOperator (R : CurvatureTensor S) (q : ℝ → P202.GeodesicData.Phase S)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1) (t : ℝ) :
    Euclidean n →L[ℝ] Euclidean n :=
  columnOperator (fun i => (P t).symm
    (R.val (q t).1 (P t (Pi.single i 1)) (q t).2 (q t).2))

/-- Reconstructing the coefficient gives the intrinsic curvature value. -/
theorem radialCoordinateOperator_apply (R : CurvatureTensor S) (q : ℝ → P202.GeodesicData.Phase S)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (t : ℝ) (x : Euclidean n) :
    P t (radialCoordinateOperator R q P t x) = R.val (q t).1 (P t x) (q t).2 (q t).2 := by
  have hx : x = ∑ i : Fin n, x i • Pi.single i 1 := by
    simpa only [Pi.basisFun_apply, Pi.basisFun_equivFun,
      LinearEquiv.refl_apply] using ((Pi.basisFun ℝ (Fin n)).sum_equivFun x).symm
  calc
    P t (radialCoordinateOperator R q P t x) =
        ∑ i : Fin n, x i • R.val (q t).1 (P t (Pi.single i 1)) (q t).2 (q t).2 := by
      simp only [radialCoordinateOperator, columnOperator_apply, map_sum, map_smul,
        LinearEquiv.apply_symm_apply]
    _ = R.val (q t).1 (P t (∑ i : Fin n, x i • Pi.single i 1)) (q t).2 (q t).2 := by
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    _ = R.val (q t).1 (P t x) (q t).2 (q t).2 := by rw [← hx]

/-- The coordinate form of the intrinsic radial curvature value. -/
theorem radialCoordinateOperator_coordinates (R : CurvatureTensor S)
    (q : ℝ → P202.GeodesicData.Phase S)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (t : ℝ) (x : TangentSpace S (q t).1) :
    radialCoordinateOperator R q P t ((P t).symm x) =
      (P t).symm (R.val (q t).1 x (q t).2 (q t).2) := by
  apply (P t).injective
  rw [radialCoordinateOperator_apply, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- The actual geometric radial operator is continuous on the full geodesic
interval. This also includes a constant geodesic and dimension zero. -/
theorem radialCoordinateOperator_continuousOn (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (I : Set ℝ) (q : ℝ → P202.GeodesicData.Phase S)
    (hq : P202.GeodesicData.IsGeodesicOn S C I q)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (hP : ∀ t ∈ I, ∀ i : Fin n, HasCovariantDerivativeAt C
      (fun s => (q s).1) (fun s => P s (Pi.single i 1)) t 0) :
    ContinuousOn (radialCoordinateOperator R q P) I := by
  intro t ht
  have hc : ContinuousAt (fun s => (q s).1) t :=
    (continuousWithinAt_univ _ _).mp (hq t ht).1.1
  have hv := covariantDerivative_continuousAt C (hq t ht).2
  apply ContinuousAt.continuousWithinAt
  apply columnOperator_continuousAt
  intro i
  exact inverse_coordinates_continuousAt C P hc (fun i => ⟨0, hP t ht i⟩)
    (curvature_continuousAt R hc
      (covariantDerivative_continuousAt C (hP t ht i)) hv hv)


open SmoothManifolds.ModelData in
/-- The linear fixed-space IVP transfers through actual parallel coordinates.
This reduction states explicitly the derivative and radial-curvature identities
that the constructed geometric coordinates must satisfy. -/
theorem jacobi_ivp_of_parallel_coordinates
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (P : (t : ℝ) → Euclidean n ≃ₗ[ℝ] TangentSpace S (q t).1)
    (A : ℝ → Euclidean n →L[ℝ] Euclidean n)
    (hA : ContinuousOn A I.carrier)
    (hPA : ∀ t ∈ I.carrier, ∀ x : Euclidean n,
      P t (A t x) = R.val (q t).1 (P t x) (q t).2 (q t).2)
    (hP : ∀ (j : ℝ → Euclidean n) (t : ℝ), t ∈ I.carrier →
      ∀ w : Euclidean n, HasDerivAt j w t ↔
        HasCovariantDerivativeAt C (fun s => (q s).1)
          (fun s => P s (j s)) t (P t w))
    (s : ℝ) (hs : s ∈ I.carrier) (u w : TangentSpace S (q s).1) :
    ∃ J : (t : ℝ) → TangentSpace S (q t).1,
      IsJacobiField C R I.carrier q J ∧ J s = u ∧
      HasCovariantDerivativeAt C (fun t => (q t).1) J s w ∧
      ∀ K : (t : ℝ) → TangentSpace S (q t).1,
        IsJacobiField C R I.carrier q K → K s = u →
        HasCovariantDerivativeAt C (fun t => (q t).1) K s w →
        ∀ t ∈ I.carrier, K t = J t := by
  obtain ⟨j, v, hjs, hvs, hjv, huniq⟩ :=
    second_order_linear_ivp I A hA s hs ((P s).symm u) ((P s).symm w)
  refine ⟨fun t => P t (j t), ?_, ?_, ?_, ?_⟩
  · refine ⟨fun t => P t (v t), ?_⟩
    intro t ht
    constructor
    · exact (hP j t ht (v t)).mp (hjv t ht).1
    · have hd := (hP v t ht (-(A t (j t)))).mp (hjv t ht).2
      simpa only [map_neg, hPA t ht (j t)] using hd
  · change P s (j s) = u
    rw [hjs, LinearEquiv.apply_symm_apply]
  · have hd := (hP j s hs (v s)).mp (hjv s hs).1
    simpa only [hvs, LinearEquiv.apply_symm_apply] using hd
  · intro K hK hKs hKw
    obtain ⟨W, hW⟩ := hK
    let k : ℝ → Euclidean n := fun t => (P t).symm (K t)
    let z : ℝ → Euclidean n := fun t => (P t).symm (W t)
    have hWs : W s = w := CurveCovariantDerivative.covariantDerivative_unique C
      (mem_univ s) uniqueDiffWithinAt_univ (hW s hs).1 hKw
    have hks : k s = (P s).symm u := by simp only [k, hKs]
    have hzs : z s = (P s).symm w := by simp only [z, hWs]
    have hkz : ∀ t ∈ I.carrier,
        HasDerivAt k (z t) t ∧ HasDerivAt z (-(A t (k t))) t := by
      intro t ht
      constructor
      · apply (hP k t ht (z t)).mpr
        simpa only [k, z, LinearEquiv.apply_symm_apply] using (hW t ht).1
      · apply (hP z t ht (-(A t (k t)))).mpr
        have heq : P t (-(A t (k t))) =
            -(R.val (q t).1 (K t) (q t).2 (q t).2) := by
          rw [map_neg, hPA t ht (k t)]
          simp only [k, LinearEquiv.apply_symm_apply]
        rw [heq]
        simpa only [z, LinearEquiv.apply_symm_apply] using (hW t ht).2
    intro t ht
    calc
      K t = P t (k t) := ((P t).apply_symm_apply (K t)).symm
      _ = P t (j t) := congrArg (fun x => P t x) (huniq k z hks hzs hkz t ht).1


/-- Arbitrary Jacobi initial data have a unique solution on the entire
original geodesic interval, in the intrinsic tangent fibers. -/
theorem exists_unique : P202Specs.Geometry.JacobiIVP.exists_uniqueType.{u} := by
  intro n M _ S g C hC R hR I q hq s hs u w
  let P := intervalParallelEquiv C I q hq s hs
  have hP (t : ℝ) (ht : t ∈ I.carrier) (i : Fin n) :
      HasCovariantDerivativeAt C (fun s => (q s).1)
        (fun s => P s (Pi.single i 1)) t 0 :=
    intervalParallelEquiv_parallel C I q hq s hs (Pi.single i 1) t ht
  exact jacobi_ivp_of_parallel_coordinates C R I q P
    (radialCoordinateOperator R q P)
    (radialCoordinateOperator_continuousOn C R I.carrier q hq P hP)
    (fun t _ x => radialCoordinateOperator_apply R q P t x)
    (fun j t ht w => derivative_parallel_equiv C P (hq t ht).1 (hP t ht) j w)
    s hs u w

end P202.Geometry.JacobiIVP
