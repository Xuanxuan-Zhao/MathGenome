import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NonpositiveJacobiGrowth
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ExponentialJacobi
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.SectionalRecovery
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MetricGeodesicCompleteness
import Mathlib.Analysis.SpecialFunctions.Sqrt

import Mathlib.Analysis.Convex.Jensen
import Mathlib.Analysis.Calculus.LHopital

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000
namespace P202.Geometry.NonpositiveJacobiGrowth
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.ConnectionData P202.MetricData P202.CurveConnectionData P202.LeviCivitaData
  P202.GeodesicData P202.CurvatureData P202.JacobiData P202.ExponentialData
  P202.ExponentialJacobiData P202.NonpositiveJacobiData P202.CompletenessData
open Set Filter
open scoped Topology SmoothManifolds.BoundaryConeData
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Nonpositive sectional curvature controls every sectional numerator,
including dependent pairs and fibers with no two-planes. -/
theorem curvature_nonpos (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (hK : NonpositiveSectionalCurvature g R)
    (p : M) (x y : TangentSpace S p) : curvatureForm g R p x y y x ≤ 0 := by
  by_cases h : LinearIndependent ℝ ![x, y]
  · have hp := SectionalRecovery.gram_pos (pairing g p) (g.symmetric p) (g.positive p) x y h
    have hk := (div_le_iff₀ hp).mp (hK p x y h)
    simpa only [zero_mul] using hk
  · have hz := SectionalRecovery.diagonal_dependent (curvatureForm g R p)
      (fun c x y z w => by simp [curvatureForm, pairing, map_smul])
      (fun c x y z w => by simp [curvatureForm, pairing, map_smul])
      (fun x y z w => (CurvatureAlgebra.symmetries g C hC R hR p x y z w).1) x y h
    exact hz.le


/-- The two scalar derivatives needed for convexity. -/
theorem squared_norm_derivatives (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {I : Set ℝ} {q : ℝ → Phase S}
    {J V : (t : ℝ) → TangentSpace S (q t).1}
    (hV : ∀ t ∈ I,
      HasCovariantDerivativeAt C (fun s => (q s).1) J t (V t) ∧
      HasCovariantDerivativeAt C (fun s => (q s).1) V t
        (-(R.val (q t).1 (J t) (q t).2 (q t).2)))
    (t : ℝ) (ht : t ∈ I) :
    HasDerivAt (fun s => pairing g (q s).1 (J s) (J s))
      (2 * pairing g (q t).1 (V t) (J t)) t ∧
    HasDerivAt (fun s => 2 * pairing g (q s).1 (V s) (J s))
      (2 * (pairing g (q t).1 (V t) (V t) -
        curvatureForm g R (q t).1 (J t) (q t).2 (q t).2 (J t))) t := by
  constructor
  · have hd := ParallelTransport.metric_pairing_deriv C g hC.2
      (mem_univ t) uniqueDiffWithinAt_univ (hV t ht).1 (hV t ht).1
    change HasDerivWithinAt (fun s => pairing g (q s).1 (J s) (J s)) (pairing g (q t).1 (V t) (J t) +
      pairing g (q t).1 (J t) (V t)) univ t at hd
    rw [show pairing g (q t).1 (J t) (V t) = pairing g (q t).1 (V t) (J t)
      from g.symmetric (q t).1 (J t) (V t)] at hd
    convert hasDerivWithinAt_univ.mp hd using 1
    ring
  · have hd := (hasDerivWithinAt_univ.mp
      (ParallelTransport.metric_pairing_deriv C g hC.2
        (mem_univ t) uniqueDiffWithinAt_univ (hV t ht).2 (hV t ht).1)).const_mul 2
    change HasDerivAt (fun s => 2 * pairing g (q s).1 (V s) (J s))
      (2 * (pairing g (q t).1 (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (J t) +
        pairing g (q t).1 (V t) (V t))) t at hd
    have he : pairing g (q t).1 (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (J t) =
        -curvatureForm g R (q t).1 (J t) (q t).2 (q t).2 (J t) :=
      by
        change pairing g (q t).1 (-(R.val (q t).1 (J t) (q t).2 (q t).2)) (J t) =
          -pairing g (q t).1 (R.val (q t).1 (J t) (q t).2 (q t).2) (J t)
        exact LinearMap.BilinForm.neg_left (B₁ := pairing g (q t).1)
          (R.val (q t).1 (J t) (q t).2 (q t).2) (J t)
    rw [he] at hd
    convert hd using 1
    ring

/-- Convexity of the squared norm does not require normality or unit speed. -/
theorem squared_norm_convex (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (hK : NonpositiveSectionalCurvature g R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) :
    ConvexOn ℝ I.carrier (fun t => pairing g (q t).1 (J t) (J t)) := by
  obtain ⟨V, hV⟩ := hJ
  apply convexOn_of_hasDerivWithinAt2_nonneg I.ordConnected.convex
    (fun t ht => (squared_norm_derivatives g C hC R hV t ht).1.continuousAt.continuousWithinAt)
    (fun t ht => (squared_norm_derivatives g C hC R hV t (interior_subset ht)).1.hasDerivWithinAt)
    (fun t ht => (squared_norm_derivatives g C hC R hV t (interior_subset ht)).2.hasDerivWithinAt)
  intro t ht
  have hn := SmoothMetrics.pairing_self_nonneg g (q t).1 (V t)
  have hk := curvature_nonpos g C hC R hR hK (q t).1 (J t) (q t).2
  linarith

/-- A field vanishing at two times vanishes on the intervening segment.
At its midpoint it has zero value and zero covariant derivative, so IVP
uniqueness propagates this equality to the whole geodesic interval. -/
theorem two_zeros : P202Specs.Geometry.NonpositiveJacobiGrowth.two_zerosType.{u} := by
  intro n M _ S g C hC R hR hK I q hq J hJ a ha b hb hab hJa hJb
  wlog hlt : a < b generalizing a b
  · exact this b hb a ha hab.symm hJb hJa (lt_of_le_of_ne (le_of_not_gt hlt) hab.symm)
  have hconv := squared_norm_convex g C hC R hR hK I q J hJ
  have hseg : ∀ t ∈ Icc a b, J t = 0 := by
    intro t ht
    have hle := hconv.le_max_of_mem_Icc ha hb ht
    rw [hJa, hJb] at hle
    simp only [SmoothMetrics.pairing_self_zero, max_self] at hle
    have hz : pairing g (q t).1 (J t) (J t) = 0 :=
      le_antisymm hle (SmoothMetrics.pairing_self_nonneg g (q t).1 (J t))
    by_contra hne
    exact (ne_of_gt (g.positive (q t).1 (J t) hne)) hz
  let c := (a + b) / 2
  have hac : a < c := by dsimp [c]; linarith
  have hcb : c < b := by dsimp [c]; linarith
  have hc : c ∈ I.carrier := I.ordConnected.out ha hb ⟨hac.le, hcb.le⟩
  have hzero : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) c 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq c hc).2 (0 : ℝ)
  have hd : HasCovariantDerivativeAt C (fun s => (q s).1) J c 0 := by
    apply ParallelTransport.derivative_field_congr C (mem_univ c) _ hzero
    simp only [nhdsWithin_univ]
    filter_upwards [Ioo_mem_nhds hac hcb] with t ht
    exact (hseg t ⟨ht.1.le, ht.2.le⟩).symm
  obtain ⟨K, hK, hKc, hKd, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq c hc 0 0
  have hJeq := huniq J hJ (hseg c ⟨hac.le, hcb.le⟩) hd
  have h0eq := huniq (fun _ => 0) (ExponentialJacobi.zero_jacobi C R I.carrier q hq) rfl hzero
  intro t ht
  exact (hJeq t ht).trans (h0eq t ht).symm

theorem no_conjugate : P202Specs.Geometry.NonpositiveJacobiGrowth.no_conjugateType.{u} := by
  intro n M _ S g C hC R hR hK I q hq a b hab
  rintro ⟨J, ⟨⟨K, hJac, heq⟩, hJa, hJb⟩, hne⟩
  have hz := two_zeros S g C hC R hR hK I q hq K hJac
    a.val a.property b.val b.property (fun h => hab (Subtype.ext h))
    ((heq a).trans hJa) ((heq b).trans hJb)
  apply hne
  funext t
  exact (heq t).symm.trans (hz t.val t.property)

theorem nonsingular_on_domain :
    P202Specs.Geometry.NonpositiveJacobiGrowth.nonsingular_on_domainType.{u} := by
  intro n M _ S g C hC R hR hK F hF p v hv
  have hn := no_conjugate S g C hC R hR hK (F.interval ⟨p, v⟩)
    (F.curve ⟨p, v⟩) (hF ⟨p, v⟩).2.2.1
    ⟨0, (hF ⟨p, v⟩).1⟩ ⟨1, hv⟩ (by intro h; have := congrArg Subtype.val h; norm_num at this)
  have he := ExponentialJacobi.conjugacy_singularity S g C hC R hR F hF p v 1 (by norm_num) hv
  rw [show (1 : ℝ) • v = v from one_smul ℝ v] at he
  exact not_not.mp (fun h => hn (he.mpr h))

/-- The origin derivative is already an upstream intrinsic identity. -/
theorem differential_zero : P202Specs.Geometry.NonpositiveJacobiGrowth.differential_zeroType.{u} :=
  ExponentialNormalCoordinates.derivative_zero
theorem nonsingular : P202Specs.Geometry.NonpositiveJacobiGrowth.nonsingularType.{u} := by
  intro n M _ _ S g C hC R hR hK hcomplete F hF p v
  have hgeo := MetricGeodesicCompleteness.metric_complete_geodesically_complete S g C hC hcomplete
  have hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F := by
    change 1 ∈ (F.interval ⟨p, v⟩).carrier
    rw [hgeo _ _ _ (hF ⟨p, v⟩)]
    exact mem_univ 1
  exact ⟨hv, nonsingular_on_domain S g C hC R hR hK F hF p v hv⟩

/-- Scalar form of the right derivative of the norm at an initial zero. -/
theorem sqrt_right_derivative {f f₁ : ℝ → ℝ} {c : ℝ}
    (hf : ∀ᶠ t in 𝓝 0, HasDerivAt f (f₁ t) t)
    (h₁ : HasDerivAt f₁ (2 * c) 0)
    (hf0 : f 0 = 0) (h₁0 : f₁ 0 = 0)
    (hn : ∀ᶠ t in 𝓝[>] 0, 0 ≤ f t) :
    HasDerivWithinAt (fun t => Real.sqrt (f t)) (Real.sqrt c) (Ici 0) 0 := by
  have hs : Tendsto (fun t => f₁ t / (2 * t)) (𝓝[>] 0) (𝓝 c) := by
    have h := (h₁.tendsto_slope_zero_right).div_const 2
    simpa [h₁0, smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  have hlim : Tendsto (fun t => f t / t ^ 2) (𝓝[>] 0) (𝓝 c) := by
    apply HasDerivAt.lhopital_zero_nhdsGT (g' := fun t : ℝ => 2 * t) (hf.filter_mono nhdsWithin_le_nhds)
      (Eventually.of_forall (fun t => by simpa [sq, two_mul] using! (hasDerivAt_id t).mul (hasDerivAt_id t)))
    · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
      exact ne_of_gt (mul_pos (by norm_num) ht)
    · simpa [hf0] using (hf.self_of_nhds.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
    · simpa [sq] using! ((continuousAt_id.mul continuousAt_id).tendsto.mono_left
        (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds))
    · exact hs
  apply HasDerivWithinAt.Ici_of_Ioi
  apply (hasDerivWithinAt_iff_tendsto_slope' (by simp)).mpr
  have heq : slope (fun t => Real.sqrt (f t)) 0 =ᶠ[𝓝[>] 0]
      (fun t => Real.sqrt (f t / t ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin, hn] with t (ht : 0 < t) hnt
    simp [slope_def_field, hf0, Real.sqrt_div hnt, Real.sqrt_sq ht.le]
  exact hlim.sqrt.congr' heq.symm

/-- Convexity of a square root from its two derivative formulas. -/
theorem sqrt_convex {D : Set ℝ} (hD : Convex ℝ D) {f f₁ f₂ : ℝ → ℝ}
    (hf : ContinuousOn f D)
    (hd : ∀ t ∈ interior D, HasDerivAt f (f₁ t) t)
    (hd₁ : ∀ t ∈ interior D, HasDerivAt f₁ (f₂ t) t)
    (hp : ∀ t ∈ interior D, 0 < f t)
    (hq : ∀ t ∈ interior D, f₁ t ^ 2 ≤ 2 * f t * f₂ t) :
    ConvexOn ℝ D (fun t => Real.sqrt (f t)) := by
  let N : ℝ → ℝ := fun t => Real.sqrt (f t)
  have hN : ∀ t ∈ interior D, HasDerivAt N (f₁ t / (2 * N t)) t := by
    intro t ht
    exact (hd t ht).sqrt (ne_of_gt (hp t ht))
  apply convexOn_of_hasDerivWithinAt2_nonneg hD (Real.continuous_sqrt.comp_continuousOn hf)
    (fun t ht => (hN t ht).hasDerivWithinAt)
    (f'' := fun t => (2 * f t * f₂ t - f₁ t ^ 2) / (4 * N t ^ 3))
  · intro t ht
    have hnt : N t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (hp t ht))
    have hsq : N t ^ 2 = f t := Real.sq_sqrt (hp t ht).le
    have h := (hd₁ t ht).div ((hN t ht).const_mul 2) (mul_ne_zero (by norm_num) hnt)
    convert h.hasDerivWithinAt using 1
    field_simp
    rw [← hsq]
    ring
  · intro t ht
    exact div_nonneg (sub_nonneg.mpr (hq t ht))
      (mul_nonneg (by norm_num) (pow_nonneg (Real.sqrt_nonneg _) _))
theorem bilinear_cauchy_schwarz {F : Type*} [AddCommGroup F] [Module ℝ F]
    (B : LinearMap.BilinForm ℝ F) (hs : ∀ x y, B x y = B y x)
    (hp : ∀ x, x ≠ 0 → 0 < B x x) (x y : F) : B x y ^ 2 ≤ B x x * B y y := by
  have hnon (v : F) : 0 ≤ B v v := by
    by_cases hv : v = 0
    · simp [hv]
    · exact (hp v hv).le
  by_cases hy : y = 0
  · simp [hy]
  have hpy := hp y hy
  have hn := hnon (x - (B x y / B y y) • y)
  have he : B y y * B (x - (B x y / B y y) • y)
      (x - (B x y / B y y) • y) = B x x * B y y - B x y ^ 2 := by
    simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sub_right,
      LinearMap.BilinForm.smul_left, LinearMap.BilinForm.smul_right]
    rw [hs y x]
    field_simp
    ring
  have h := mul_nonneg hpy.le hn
  rw [he] at h
  linarith

theorem pairing_cauchy_schwarz (g : RiemannianMetric S) (p : M)
    (x y : TangentSpace S p) :
    pairing g p x y ^ 2 ≤ pairing g p x x * pairing g p y y :=
  bilinear_cauchy_schwarz (pairing g p) (g.symmetric p) (g.positive p) x y
theorem zero_initial_field (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (hd : HasCovariantDerivativeAt C (fun t => (q t).1) J 0 0) :
    ∀ t ∈ I.carrier, J t = 0 := by
  obtain ⟨K, hK, hK0, hKd, huniq⟩ := JacobiIVP.exists_unique S g C hC R hR I q hq 0 h0 0 0
  have hzero : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq 0 h0).2 (0 : ℝ)
  have hJeq := huniq J hJ hJ0 hd
  have h0eq := huniq (fun _ => 0) (ExponentialJacobi.zero_jacobi C R I.carrier q hq) rfl hzero
  intro t ht
  exact (hJeq t ht).trans (h0eq t ht).symm

theorem no_positive_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (hK : NonpositiveSectionalCurvature g R)
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) (h0 : 0 ∈ I.carrier)
    (J : (t : ℝ) → TangentSpace S (q t).1)
    (hJ : IsJacobiField C R I.carrier q J) (hJ0 : J 0 = 0)
    (w : TangentSpace S (q 0).1)
    (hd : HasCovariantDerivativeAt C (fun t => (q t).1) J 0 w) (hw : w ≠ 0) :
    ∀ t ∈ I.carrier, 0 < t → J t ≠ 0 := by
  intro t ht hpos hzt
  have hz := two_zeros S g C hC R hR hK I q hq J hJ
    0 h0 t ht (ne_of_lt hpos) hJ0 hzt
  have hzero : HasCovariantDerivativeAt C (fun s => (q s).1) (fun _ => 0) 0 0 := by
    simpa only [zero_smul] using
      CurveCovariantDerivative.derivative_const_smul C (hq 0 h0).2 (0 : ℝ)
  have hd0 : HasCovariantDerivativeAt C (fun s => (q s).1) J 0 0 := by
    apply ParallelTransport.derivative_field_congr C (mem_univ 0) _ hzero
    simp only [nhdsWithin_univ]
    filter_upwards [I.isOpen.mem_nhds h0] with s hs
    exact (hz s hs).symm
  exact hw (CurveCovariantDerivative.covariantDerivative_unique C
    (mem_univ 0) uniqueDiffWithinAt_univ hd hd0)

theorem growth : P202Specs.Geometry.NonpositiveJacobiGrowth.growthType.{u} := by
  intro n M _ S g C hC R hR hK I q hq h0 J hJ hJ0 w hw
  obtain ⟨V, hV⟩ := hJ
  have hV0 : V 0 = w := CurveCovariantDerivative.covariantDerivative_unique C
    (mem_univ 0) uniqueDiffWithinAt_univ (hV 0 h0).1 hw
  let f : ℝ → ℝ := fun t => pairing g (q t).1 (J t) (J t)
  let f₁ : ℝ → ℝ := fun t => 2 * pairing g (q t).1 (V t) (J t)
  let f₂ : ℝ → ℝ := fun t => 2 * (pairing g (q t).1 (V t) (V t) -
    curvatureForm g R (q t).1 (J t) (q t).2 (q t).2 (J t))
  have hder : ∀ t ∈ I.carrier, HasDerivAt f (f₁ t) t ∧ HasDerivAt f₁ (f₂ t) t :=
    squared_norm_derivatives g C hC R hV
  have hf0 : f 0 = 0 := by simp [f, hJ0, pairing]
  have hf₁0 : f₁ 0 = 0 := by simp [f₁, hJ0, pairing]
  have hf₂0 : f₂ 0 = 2 * pairing g (q 0).1 w w := by
    simp [f₂, hJ0, hV0, curvatureForm, pairing]
  have hr : HasDerivWithinAt (fun t => tangentNorm g (q t).1 (J t))
      (tangentNorm g (q 0).1 w) (Ici 0) 0 := by
    apply sqrt_right_derivative
      (f₁ := f₁)
      (Filter.eventually_of_mem (I.isOpen.mem_nhds h0) (fun t ht => (hder t ht).1))
    · simpa only [hf₂0] using (hder 0 h0).2
    · exact hf0
    · exact hf₁0
    · exact Eventually.of_forall (fun t => SmoothMetrics.pairing_self_nonneg g (q t).1 (J t))
  have hz : w = 0 → ∀ t ∈ I.carrier, J t = 0 := by
    intro hw0
    apply zero_initial_field g C hC R hR I q hq h0 J ⟨V, hV⟩ hJ0
    simpa only [hw0] using hw
  have hn : w ≠ 0 → ∀ t ∈ I.carrier, 0 < t → J t ≠ 0 :=
    no_positive_zero g C hC R hR hK I q hq h0 J ⟨V, hV⟩ hJ0 w hw
  have hD : Convex ℝ (I.carrier ∩ Ici 0) := I.ordConnected.convex.inter (convex_Ici 0)
  have hconv : ConvexOn ℝ (I.carrier ∩ Ici 0)
      (fun t => tangentNorm g (q t).1 (J t)) := by
    by_cases hw0 : w = 0
    · apply (convexOn_const (0 : ℝ) hD).congr
      intro t ht
      simp only [hz hw0 t ht.1, SmoothMetrics.tangentNorm_zero]
    · have hint (t : ℝ) (ht : t ∈ interior (I.carrier ∩ Ici 0)) :
          t ∈ I.carrier ∧ 0 < t := by
        simpa only [interior_inter, I.isOpen.interior_eq, interior_Ici, mem_inter_iff, mem_Ioi] using ht
      apply sqrt_convex (f₁ := f₁) (f₂ := f₂) hD
        (fun t ht => (hder t ht.1).1.continuousAt.continuousWithinAt)
        (fun t ht => (hder t (hint t ht).1).1)
        (fun t ht => (hder t (hint t ht).1).2)
      · intro t ht
        exact g.positive (q t).1 (J t) (hn hw0 t (hint t ht).1 (hint t ht).2)
      · intro t ht
        have hcs := pairing_cauchy_schwarz g (q t).1 (V t) (J t)
        have hcur := curvature_nonpos g C hC R hR hK (q t).1 (J t) (q t).2
        have hnon := SmoothMetrics.pairing_self_nonneg g (q t).1 (J t)
        dsimp [f₁, f, f₂]
        nlinarith [mul_nonpos_of_nonneg_of_nonpos hnon hcur]
  refine ⟨?_, hconv, hr, hn, hz⟩
  intro t ht ht0
  rcases eq_or_lt_of_le ht0 with rfl | hpos
  · simp [hJ0]
  have hle := hconv.le_slope_of_hasDerivWithinAt_Ioi (x := 0) (y := t) ⟨h0, by simp⟩ ⟨ht, by exact ht0⟩ hpos hr.Ioi_of_Ici
  simp only [slope_def_field, hJ0, SmoothMetrics.tangentNorm_zero, sub_zero] at hle
  simpa only [mul_comm] using (le_div_iff₀ hpos).mp hle


end P202.Geometry.NonpositiveJacobiGrowth
