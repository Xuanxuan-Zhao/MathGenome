import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NoInteriorConjugate
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ParallelTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MinimizingIndexForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.JacobiIVP
import Mathlib.Analysis.Calculus.ContDiff.Deriv

/-! The no-interior-conjugate-point corollary, paper.tex 4145–4179.
The proof uses actual intrinsic Jacobi fields, their closed-segment regularity
and uniqueness, and the canonical index form of a truncated field. -/
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.NoInteriorConjugate
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  SmoothManifolds.TangentBundleData SmoothManifolds.BundleOperationsData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.FirstVariationData P202.SecondVariationData
  P202.CurvatureData P202.MinimizingIndexData P202.GeodesicData P202.JacobiData
  P202.NoInteriorConjugateData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A negative linear term dominates any quadratic term for arbitrarily
small positive parameters. This also covers a negative quadratic coefficient. -/
theorem exists_small_negative_quadratic {B D δ : ℝ}
    (hB : B < 0) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧ 2 * ε * B + ε ^ 2 * D < 0 := by
  have hden : 0 < |D| + 1 := by positivity
  let ε := min (δ / 2) (-B / (|D| + 1))
  have hε : 0 < ε := lt_min (by linarith) (div_pos (by linarith) hden)
  have hεδ : ε < δ := (min_le_left _ _).trans_lt (by linarith)
  have hbound : ε * (|D| + 1) ≤ -B :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  have hprod : ε * D ≤ ε * |D| := mul_le_mul_of_nonneg_left (le_abs_self D) hε.le
  have hlin : 2 * B + ε * D < 0 := by nlinarith
  refine ⟨ε, hε, hεδ, ?_⟩
  nlinarith [mul_neg_of_pos_of_neg hε hlin]

/-- A positive semidefinite quadratic polynomial with zero constant term
has zero linear coefficient; no strict positivity is assumed. -/
theorem linear_coefficient_eq_zero {B D : ℝ}
    (h : ∀ ε : ℝ, 0 ≤ 2 * ε * B + ε ^ 2 * D) : B = 0 := by
  rcases lt_trichotomy B 0 with hn | hz | hp
  · obtain ⟨ε, _, _, he⟩ := exists_small_negative_quadratic (D := D) hn (show (0 : ℝ) < 1 by norm_num)
    linarith [h ε]
  · exact hz
  · obtain ⟨ε, _, _, he⟩ := exists_small_negative_quadratic (D := D) (neg_neg_of_pos hp)
      (show (0 : ℝ) < 1 by norm_num)
    have hh := h (-ε)
    nlinarith

/-- Ordinary ambient Jacobi fields restrict to the closed-segment equation.
The tangent in that equation is proved to be the actual velocity, including
at the segment endpoints. -/
theorem segment_jacobi_of_open (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) {I : Set ℝ} {q : ℝ → Phase S}
    (hq : IsGeodesicOn S C I q) {a c : ℝ} (hac : a < c)
    (hsub : Icc a c ⊆ I)
    {J : (t : ℝ) → TangentSpace S (q t).1}
    (hJ : P202.JacobiData.IsJacobiField C R I q J) :
    IsSegmentJacobiField C R (fun t => (q t).1) a c J := by
  obtain ⟨D, hD⟩ := hJ
  refine ⟨D, ?_⟩
  intro t ht
  have hvel : HasVelocityWithinAt S (fun s => (q s).1) (Icc a c) t (q t).2 :=
    ParallelTransport.hasVelocityWithinAt_mono (hq t (hsub ht)).1 (subset_univ _)
  have htangent : segmentTangent S (fun s => (q s).1) a c t = (q t).2 := by
    classical
    have hex : ∃ v, HasVelocityWithinAt S (fun r => (q r).1) (Icc a c) t v := ⟨_, hvel⟩
    simp only [segmentTangent, segmentVelocity, dite_eq_left hex]
    exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hac t ht)
      (Classical.choose_spec hex) hvel
  constructor
  · exact SecondVariation.hasCovariantDerivativeWithinAt_mono C (hD t (hsub ht)).1
      (subset_univ _)
  · rw [htangent]
    exact SecondVariation.hasCovariantDerivativeWithinAt_mono C (hD t (hsub ht)).2
      (subset_univ _)

/-- Scalar multiplication preserves the original local-frame C¹ condition. -/
theorem c1FieldOn_const_smul {γ : ℝ → M} {K : Set ℝ}
    {J : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J K) (s : ℝ) :
    C1FieldOn (B := tangentBundle S) γ (fun t => s • J t) K := by
  intro t ht
  obtain ⟨U, hU, b, hp, x, hx, hxt, heq⟩ := hJ t ht
  have hs : ContDiffAt ℝ 1 (fun _ : ℝ => s) t := contDiffAt_const
  refine ⟨U, hU, b, hp, (fun r => s • x r), hs.smul hx, ?_, ?_⟩
  · rw [CurveCovariantDerivative.coefficients_smul]
    change s • coefficientsAlong b γ J t = s • x t
    rw [hxt]
  · rw [CurveCovariantDerivative.coefficients_smul]
    filter_upwards [heq] with r hr
    exact congrArg (fun v : Euclidean n => s • v) hr

/-- The canonical index form has the expected quadratic expansion on any
common finite partition. Integrability comes from the existing C¹ theorem. -/
theorem indexForm_quadratic (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (ha : node 0 = a) (hb : node (Fin.last (k+1)) = b)
    {W Z : (t : ℝ) → TangentSpace S (γ t)}
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)))
    (hZ : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ Z
      (Icc (node i.castSucc) (node i.succ))) (s : ℝ) :
    indexForm g C R γ a b (fun t => W t + s • Z t) (fun t => W t + s • Z t) =
      indexForm g C R γ a b W W + 2 * s * indexForm g C R γ a b W Z +
        s ^ 2 * indexForm g C R γ a b Z Z := by
  subst a
  subst b
  classical
  let N : Finset ℝ := Finset.univ.image node
  have hnodes {t : ℝ} (hne : t ∉ N) : ∀ i, t ≠ node i := by
    intro i heq
    exact hne (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, heq.symm⟩)
  have hmem {t : ℝ} (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1))))
      (hne : t ∉ N) : t ∈ Ioo (node 0) (node (Fin.last (k+1))) := by
    rw [uIoc_of_le hab.le] at ht
    exact ⟨ht.1, lt_of_le_of_ne ht.2 (hnodes hne _)⟩
  let f := indexIntegrand g C R γ (node 0) (node (Fin.last (k+1)))
  have hWW := SecondVariation.indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hW hW
  have hWZ := SecondVariation.indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hW hZ
  have hZW := SecondVariation.indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hZ hW
  have hZZ := SecondVariation.indexIntegrand_piecewise_intervalIntegrable g C R node hnode hγ hZ hZ
  have heq (t : ℝ)
      (ht : t ∈ uIoc (node 0) (node (Fin.last (k+1)))) (hne : t ∉ N) :
      f (fun t => W t + s • Z t) (fun t => W t + s • Z t) t =
        f W W t + s * f W Z t + s * f Z W t + s ^ 2 * f Z Z t := by
    have ht' := Ioo_subset_Icc_self (hmem ht hne)
    have hu := uniqueDiffOn_Icc hab t ht'
    obtain ⟨DW, hdW⟩ := SecondVariation.piecewise_exists_covariantDerivative C node hnode hγ hW (hmem ht hne) (hnodes hne)
    obtain ⟨DZ, hdZ⟩ := SecondVariation.piecewise_exists_covariantDerivative C node hnode hγ hZ (hmem ht hne) (hnodes hne)
    have hsZ := CurveCovariantDerivative.derivative_const_smul C hdZ s
    have hadd := CurveCovariantDerivative.covariantDerivativeWithin_add C ht' hu hdW hsZ
    have hsmul := CurveCovariantDerivative.covariantDerivativeWithin_smul C ht' hu hdZ
      (hasDerivWithinAt_const t _ s)
    simp only [zero_smul, zero_add] at hsmul
    dsimp only [f]
    simp only [indexIntegrand, hadd, hsmul, map_add, LinearMap.add_apply,
      map_smul, LinearMap.smul_apply, smul_eq_mul]
    ring
  change (∫ t in node 0..node (Fin.last (k+1)),
    f (fun t => W t + s • Z t) (fun t => W t + s • Z t) t) = _
  rw [PiecewiseCurves.integral_eq_of_eqOn_off_finite N heq]
  rw [intervalIntegral.integral_add ((hWW.add (hWZ.const_mul s)).add (hZW.const_mul s)) (hZZ.const_mul (s^2)),
    intervalIntegral.integral_add (hWW.add (hWZ.const_mul s)) (hZW.const_mul s),
    intervalIntegral.integral_add hWW (hWZ.const_mul s)]
  simp only [intervalIntegral.integral_const_mul]
  change indexForm g C R γ _ _ W W + s * indexForm g C R γ _ _ W Z +
    s * indexForm g C R γ _ _ Z W + s ^ 2 * indexForm g C R γ _ _ Z Z = _
  have hsym : indexForm g C R γ (node 0) (node (Fin.last (k+1))) Z W =
      indexForm g C R γ (node 0) (node (Fin.last (k+1))) W Z :=
    SecondVariation.indexForm_symmetric g C hC R hR γ _ _ Z W
  rw [hsym]
  ring

/-- Green's formula for a genuine Jacobi field on a closed segment. The
geometric product rule, its endpoint continuity, and the integrability of
the actual index integrand are all proved, rather than assumed identities. -/
theorem jacobi_index_boundary (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {J D Z : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J (Icc a c))
    (hZ : C1FieldOn (B := tangentBundle S) γ Z (Icc a c))
    (hD : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) t
        (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t)))) :
    indexForm g C R γ a c J Z =
      pairing g (γ c) (D c) (Z c) - pairing g (γ a) (D a) (Z a) := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ h0
  have hcc := FirstVariation.variation_continuousOn_slice hγ h0
  have hpair (t : ℝ) (ht : t ∈ Icc a c) :
      HasDerivWithinAt (fun r => pairing g (γ r) (D r) (Z r))
        (indexIntegrand g C R γ a c J Z t) (Icc a c) t := by
    have hdZ := CurveCovariantDerivative.segment_derivative C hac hc1 hcc hZ ht
    have hprod := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2
      ht (uniqueDiffOn_Icc hac t ht) (hD t ht).2
      (CurveCovariantDerivative.covariantDerivativeWithin_spec C ⟨_, hdZ.1⟩)
    have hdJ := CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
      (uniqueDiffOn_Icc hac t ht) (hD t ht).1
    change HasDerivWithinAt (fun r => pairing g (γ r) (D r) (Z r))
      (pairing g (γ t) (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
        (segmentTangent S γ a c t))) (Z t) +
        pairing g (γ t) (D t) (covariantDerivativeWithin C γ Z (Icc a c) t))
      (Icc a c) t at hprod
    have heq : indexIntegrand g C R γ a c J Z t =
        pairing g (γ t) (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t))) (Z t) +
          pairing g (γ t) (D t) (covariantDerivativeWithin C γ Z (Icc a c) t) := by
      let K : TangentSpace S (γ t) := R.val (γ t) (J t)
        (segmentTangent S γ a c t) (segmentTangent S γ a c t)
      have hn : pairing g (γ t) (-K) (Z t) = -pairing g (γ t) K (Z t) := by
        exact congrArg (fun L : TangentSpace S (γ t) →ₗ[ℝ] ℝ => L (Z t))
          ((pairing g (γ t)).map_neg K)
      unfold indexIntegrand
      rw [hdJ]
      change pairing g (γ t) (D t) (covariantDerivativeWithin C γ Z (Icc a c) t) -
        pairing g (γ t) K (Z t) = pairing g (γ t) (-K) (Z t) +
          pairing g (γ t) (D t) (covariantDerivativeWithin C γ Z (Icc a c) t)
      rw [hn]
      ring
    rw [← heq] at hprod
    exact hprod
  have hcont : ContinuousOn (fun r => pairing g (γ r) (D r) (Z r)) (Icc a c) :=
    fun t ht => (hpair t ht).continuousWithinAt
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hac.le hcont
    (fun t ht => (hpair t (Ioo_subset_Icc_self ht)).hasDerivAt (Icc_mem_nhds ht.1 ht.2))
    (SecondVariation.indexIntegrand_intervalIntegrable g C R hac hγ hJ hZ)

/-- A doubly vanishing Jacobi field has zero self-index on its own segment;
this is not a strict-positivity assertion. -/
theorem jacobi_index_self_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {J : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J (Icc a c))
    (hJac : IsSegmentJacobiField C R γ a c J) (ha : J a = 0) (hc : J c = 0) :
    indexForm g C R γ a c J J = 0 := by
  obtain ⟨D, hD⟩ := hJac
  rw [jacobi_index_boundary g C hC R hac hγ hJ hJ hD, ha, hc]
  simp only [pairing, map_zero, sub_self]


/-- The scalar closed-interval mean value theorem, in a form retaining
one-sided endpoint derivatives. -/
theorem constant_on_segment {a c : ℝ} (hac : a < c) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Icc a c, HasDerivWithinAt f 0 (Icc a c) t) :
    ∀ t ∈ Icc a c, f t = f a := by
  exact constant_of_derivWithin_zero
    (fun t ht => (hd t ht).differentiableWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hac t ⟨ht.1, ht.2.le⟩))

/-- The same mean value argument for a fixed nonzero derivative. -/
theorem affine_on_segment {a c k : ℝ} (hac : a < c) {f : ℝ → ℝ}
    (hd : ∀ t ∈ Icc a c, HasDerivWithinAt f k (Icc a c) t) :
    ∀ t ∈ Icc a c, f t - f a = (t - a) * k := by
  intro t ht
  by_cases hta : t = a
  · subst t
    simp only [sub_self, zero_mul]
  have hat : a < t := lt_of_le_of_ne ht.1 (Ne.symm hta)
  have hsub : Icc a t ⊆ Icc a c := Icc_subset_Icc le_rfl ht.2
  have hcont : ContinuousOn f (Icc a t) :=
    fun r hr => ((hd r (hsub hr)).continuousWithinAt).mono hsub
  have hdiff : DifferentiableOn ℝ f (Ioo a t) := by
    intro r hr
    exact ((hd r (hsub (Ioo_subset_Icc_self hr))).hasDerivAt
      (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))).differentiableAt.differentiableWithinAt
  obtain ⟨r, hr, heq⟩ := exists_deriv_eq_slope f hat hcont hdiff
  have hk := ((hd r (hsub (Ioo_subset_Icc_self hr))).hasDerivAt
    (Icc_mem_nhds hr.1 (hr.2.trans_le ht.2))).deriv
  rw [hk] at heq
  have hh := (eq_div_iff (sub_ne_zero.mpr hat.ne')).mp heq
  nlinarith

/-- Zero-velocity geodesics have no nonzero doubly vanishing Jacobi fields.
This uses the genuine within equations, including the endpoint values; it
requires no smoothness upgrade and no division by the speed. -/
theorem not_segmentConjugate_of_zero_tangent (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hT : ∀ t ∈ Icc a c, segmentTangent S γ a c t = 0) :
    ¬ SegmentConjugate C R γ a c := by
  rintro ⟨J, ⟨D, hD⟩, hJa, hJc, t, ht, hJt⟩
  have hDzero (r : ℝ) (hr : r ∈ Icc a c) :
      HasCovariantDerivativeWithinAt C γ D (Icc a c) r 0 := by
    have h := (hD r hr).2
    have hz : -(R.val (γ r) (J r) (0 : TangentSpace S (γ r)) 0) =
        (0 : TangentSpace S (γ r)) := by
      simp only [map_zero, LinearMap.zero_apply]
      exact @neg_zero (TangentSpace S (γ r)) _
    rw [hT r hr, hz] at h
    exact h
  have hnormD (r : ℝ) (hr : r ∈ Icc a c) :
      HasDerivWithinAt (fun s => pairing g (γ s) (D s) (D s)) 0 (Icc a c) r := by
    simpa only [pairing, map_zero, LinearMap.zero_apply, zero_add] using
      TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2 hr
        (uniqueDiffOn_Icc hac r hr) (hDzero r hr) (hDzero r hr)
  have hnormDconst := constant_on_segment hac hnormD
  have hJD (r : ℝ) (hr : r ∈ Icc a c) :
      HasDerivWithinAt (fun s => pairing g (γ s) (J s) (D s))
        (pairing g (γ a) (D a) (D a)) (Icc a c) r := by
    have h := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2 hr
      (uniqueDiffOn_Icc hac r hr) (hD r hr).1 (hDzero r hr)
    have hh : HasDerivWithinAt (fun s => pairing g (γ s) (J s) (D s))
        (pairing g (γ r) (D r) (D r)) (Icc a c) r := by
      simpa only [pairing, map_zero, add_zero] using h
    rwa [hnormDconst r hr] at hh
  have hnormDa := affine_on_segment hac hJD c ⟨hac.le, le_rfl⟩
  simp only [hJa, hJc, pairing, map_zero, LinearMap.zero_apply, sub_self] at hnormDa
  have hDall : ∀ r ∈ Icc a c, D r = 0 := by
    intro r hr
    by_contra hn
    have hp := g.positive (γ r) (D r) hn
    change 0 < pairing g (γ r) (D r) (D r) at hp
    rw [hnormDconst r hr] at hp
    have hpos := mul_pos (sub_pos.mpr hac) hp
    change 0 = (c - a) * pairing g (γ a) (D a) (D a) at hnormDa
    linarith
  have hnormJ (r : ℝ) (hr : r ∈ Icc a c) :
      HasDerivWithinAt (fun s => pairing g (γ s) (J s) (J s)) 0 (Icc a c) r := by
    have h := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2 hr
      (uniqueDiffOn_Icc hac r hr) (hD r hr).1 (hD r hr).1
    simpa only [hDall r hr, pairing, map_zero, LinearMap.zero_apply, zero_add] using h
  have hh := constant_on_segment hac hnormJ t ht
  simp only [hJa, pairing, map_zero, LinearMap.zero_apply] at hh
  exact (ne_of_gt (g.positive (γ t) (J t) hJt)) hh

/-- Constant segments satisfy the theorem, without a minimizing hypothesis. -/
theorem constant_not_segmentConjugate (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (p : M) {a c : ℝ} (hac : a < c) :
    ¬ SegmentConjugate C R (fun _ => p) a c := by
  apply not_segmentConjugate_of_zero_tangent g C hC R hac
  intro t ht
  have hv : HasVelocityWithinAt S (fun _ : ℝ => p) (Icc a c) t 0 :=
    ParallelTransport.hasVelocityWithinAt_mono
      ((GeodesicIVP.constant_is_geodesic C p) t (mem_univ t)).1 (subset_univ _)
  classical
  have hex : ∃ v, HasVelocityWithinAt S (fun _ : ℝ => p) (Icc a c) t v := ⟨0, hv⟩
  simp only [segmentTangent, segmentVelocity, dite_eq_left hex]
  exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hac t ht)
    (Classical.choose_spec hex) hv
/-- Once the Jacobi construction has supplied a null field and a negative
mixed pairing, actual finite-piece fields give arbitrarily small negative
index directions. No positivity premise is used. -/
theorem exists_negative_index (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (ha : node 0 = a) (hb : node (Fin.last (k+1)) = b)
    {W Z : (t : ℝ) → TangentSpace S (γ t)}
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)))
    (hZ : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ Z
      (Icc (node i.castSucc) (node i.succ)))
    (hWW : indexForm g C R γ a b W W = 0)
    (hWZ : indexForm g C R γ a b W Z < 0) {δ : ℝ} (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < δ ∧
      indexForm g C R γ a b (fun t => W t + ε • Z t) (fun t => W t + ε • Z t) < 0 := by
  obtain ⟨ε, hε, hεδ, hnegative⟩ := exists_small_negative_quadratic
    (D := indexForm g C R γ a b Z Z) hWZ hδ
  refine ⟨ε, hε, hεδ, ?_⟩
  rw [indexForm_quadratic g C hC R hR hab hγ node hnode ha hb hW hZ ε, hWW, zero_add]
  exact hnegative

/-- A null direction of the nonnegative index of a length-minimizing
segment is orthogonal to every admissible test direction. The regularity
premise concerns actual fields, not index values or a conjugacy certificate. -/
theorem minimizing_null_orthogonal (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {a b : ℝ} (γ : PiecewiseC1Curve S a b) (hab : a < b)
    (hγ : IsAffineGeodesicSegment C γ a b) (hmin : IsLengthMinimizing g γ)
    {k : ℕ} (node : Fin (k+2) → ℝ) (hnode : StrictMono node)
    (ha : node 0 = a) (hb : node (Fin.last (k+1)) = b)
    {W Z : (t : ℝ) → TangentSpace S (γ t)}
    (hW : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)))
    (hZ : ∀ i : Fin (k+1), C1FieldOn (B := tangentBundle S) γ Z
      (Icc (node i.castSucc) (node i.succ)))
    (hfields : ∀ s : ℝ, PiecewiseSmoothFieldOn γ (fun t => W t + s • Z t) node)
    (hWa : W a = 0) (hWb : W b = 0) (hZa : Z a = 0) (hZb : Z b = 0)
    (hWW : indexForm g C R γ a b W W = 0) :
    indexForm g C R γ a b W Z = 0 := by
  apply linear_coefficient_eq_zero (D := indexForm g C R γ a b Z Z)
  intro s
  have hh := MinimizingIndexForm.indexForm_nonneg g C hC R hR γ hab hγ hmin
    node hnode ha hb (fun t => W t + s • Z t) (hfields s)
    (by simp only [hWa, hZa, smul_zero, add_zero])
    (by simp only [hWb, hZb, smul_zero, add_zero])
  rw [indexForm_quadratic g C hC R hR hab hγ.1 node hnode ha hb hW hZ s,
    hWW, zero_add] at hh
  exact hh

/-- The zero field has ambient constant coefficient extensions in every frame. -/
theorem c1FieldOn_zero (γ : ℝ → M) (K : Set ℝ) :
    C1FieldOn (B := tangentBundle S) γ (fun _ => 0) K := by
  intro t ht
  obtain ⟨U, hU, hp, ⟨b⟩⟩ :=
    SmoothManifolds.ConstantRankBundles.exists_localFrame (tangentBundle S) (γ t)
  have hz : coefficientsAlong b γ (fun _ => 0) = (fun _ => (0 : Euclidean n)) := by
    funext r
    simp only [coefficientsAlong]
    split <;> simp only [map_zero]
  refine ⟨U, hU, b, hp, (fun _ => 0), contDiffAt_const, ?_, ?_⟩
  · rw [hz]
  · rw [hz]

/-- Bilinear index values depend only on the fields on the segment. -/
theorem indexForm_congr_fields (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    {V W Z T : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ t ∈ Icc a b, V t = W t) (hZ : ∀ t ∈ Icc a b, Z t = T t) :
    indexForm g C R γ a b V Z = indexForm g C R γ a b W T := by
  apply intervalIntegral.integral_congr
  rw [uIcc_of_le hab.le]
  intro t ht
  have hDV := MinimizingIndexForm.covariantDerivativeWithin_congr_field C ht
    (uniqueDiffOn_Icc hab t ht) hV
  have hDZ := MinimizingIndexForm.covariantDerivativeWithin_congr_field C ht
    (uniqueDiffOn_Icc hab t ht) hZ
  simp only [indexIntegrand, hDV, hDZ, hV t ht, hZ t ht]

/-- The zero field has zero mixed index on a smooth interval. -/
theorem indexForm_zero_left (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {Z : (t : ℝ) → TangentSpace S (γ t)}
    (hZ : C1FieldOn (B := tangentBundle S) γ Z (Icc a b)) :
    indexForm g C R γ a b (fun _ => 0) Z = 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ h0
  have hcc := FirstVariation.variation_continuousOn_slice hγ h0
  have hzero (t : ℝ) (ht : t ∈ Icc a b) :
      covariantDerivativeWithin C γ (fun _ => 0) (Icc a b) t = 0 := by
    have hDZ := (CurveCovariantDerivative.segment_derivative C hab hc1 hcc hZ ht).1
    have hz := CurveCovariantDerivative.derivative_const_smul C hDZ 0
    simp only [zero_smul] at hz
    exact CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
      (uniqueDiffOn_Icc hab t ht) hz
  change (∫ t in a..b, indexIntegrand g C R γ a b (fun _ => 0) Z t) = 0
  rw [show (∫ t in a..b, indexIntegrand g C R γ a b (fun _ => 0) Z t) =
      ∫ t in a..b, (0 : ℝ) from
    intervalIntegral.integral_congr_Ioo_of_le hab.le (fun t ht => by
      simp only [indexIntegrand, hzero t (Ioo_subset_Icc_self ht),
        pairing, map_zero, LinearMap.zero_apply, sub_zero])]
  simp only [intervalIntegral.integral_zero]

/-- Truncation at a zero endpoint gives the actual corner pairing in the
source proof. The regularity assumptions here are C¹, not positivity or an
assumed integration-by-parts identity. -/
theorem truncated_jacobi_index_boundary (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {γ : ℝ → M} {a b c : ℝ}
    (hac : a < c) (hcb : c < b)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {J D Z : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J (Icc a c))
    (hZleft : C1FieldOn (B := tangentBundle S) γ Z (Icc a c))
    (hZright : C1FieldOn (B := tangentBundle S) γ Z (Icc c b))
    (hD : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) t
        (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t))))
    (hJc : J c = 0) (hZa : Z a = 0) :
    indexForm g C R γ a b (ParallelTransport.fieldGlue J (fun _ => 0) c) Z =
      pairing g (γ c) (D c) (Z c) := by
  let W := ParallelTransport.fieldGlue J (fun _ => 0) c
  let node : Fin 3 → ℝ := ![a,c,b]
  have hnode : StrictMono node := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · simpa [node] using hac
    · simpa [node] using hcb
  have hγleft := SecondVariation.smoothVariationOn_mono_interval hγ le_rfl hcb.le
  have hγright := SecondVariation.smoothVariationOn_mono_interval hγ hac.le le_rfl
  have hWleft : C1FieldOn (B := tangentBundle S) γ W (Icc a c) :=
    ParallelTransport.c1FieldOn_congr hJ (fun t ht =>
      ParallelTransport.fieldGlue_left J (fun _ => 0) ht.2)
  have hWright : C1FieldOn (B := tangentBundle S) γ W (Icc c b) := by
    have hz := c1FieldOn_zero (S := S) γ (Icc c b)
    exact ParallelTransport.c1FieldOn_congr hz (fun t ht =>
      ParallelTransport.fieldGlue_right J (fun _ => 0) hJc ht.1)
  have hWpieces : ∀ i : Fin 2, C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    · exact hWleft
    · exact hWright
  have hZpieces : ∀ i : Fin 2, C1FieldOn (B := tangentBundle S) γ Z
      (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    · exact hZleft
    · exact hZright
  have hsplit := SecondVariation.indexForm_subdivision_of_integrable g C R node hnode
    hγ hWpieces hZpieces (fun i => SecondVariation.indexIntegrand_intervalIntegrable
      g C R (hnode (Fin.castSucc_lt_succ (i := i)))
      (SecondVariation.smoothVariationOn_mono_interval hγ
        (hnode.monotone (Fin.zero_le i.castSucc)) (hnode.monotone (Fin.le_last i.succ)))
      (hWpieces i) (hZpieces i))
  change indexForm g C R γ a b W Z = _
  have heq : indexForm g C R γ a b W Z =
      indexForm g C R γ a c W Z + indexForm g C R γ c b W Z := by
    simpa [node, Fin.sum_univ_two] using hsplit
  rw [heq,
    indexForm_congr_fields g C R hac (fun t ht => ParallelTransport.fieldGlue_left J (fun _ => 0) ht.2) (fun _ _ => rfl),
    indexForm_congr_fields g C R hcb (fun t ht => ParallelTransport.fieldGlue_right J (fun _ => 0) hJc ht.1) (fun _ _ => rfl),
    indexForm_zero_left g C R hcb hγright hZright, add_zero,
    jacobi_index_boundary g C hC R hac hγleft hJ hZleft hD, hZa]
  simp only [pairing, map_zero, sub_zero]
/-- The zero extension has zero self-index on the whole segment, even
though its derivative can jump at the interior zero. -/
theorem truncated_jacobi_self_index_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) {γ : ℝ → M} {a b c : ℝ}
    (hac : a < c) (hcb : c < b)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {J : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J (Icc a c))
    (hJac : IsSegmentJacobiField C R γ a c J) (hJa : J a = 0) (hJc : J c = 0) :
    let W := ParallelTransport.fieldGlue J (fun _ => 0) c
    indexForm g C R γ a b W W = 0 := by
  obtain ⟨D, hD⟩ := hJac
  let W := ParallelTransport.fieldGlue J (fun _ => 0) c
  have hWleft : C1FieldOn (B := tangentBundle S) γ W (Icc a c) :=
    ParallelTransport.c1FieldOn_congr hJ (fun t ht =>
      ParallelTransport.fieldGlue_left J (fun _ => 0) ht.2)
  have hWright : C1FieldOn (B := tangentBundle S) γ W (Icc c b) :=
    ParallelTransport.c1FieldOn_congr (c1FieldOn_zero γ (Icc c b)) (fun t ht =>
      ParallelTransport.fieldGlue_right J (fun _ => 0) hJc ht.1)
  have hWa : W a = 0 :=
    (ParallelTransport.fieldGlue_left J (fun _ => 0) hac.le).trans hJa
  have hWc : W c = 0 :=
    (ParallelTransport.fieldGlue_left J (fun _ => 0) le_rfl).trans hJc
  change indexForm g C R γ a b W W = 0
  rw [truncated_jacobi_index_boundary g C hC R hac hcb hγ hJ hWleft hWright hD hJc hWa, hWc]
  simp only [pairing, map_zero]

/-- Smooth tangent-chart extensions give the local-frame C¹ extensions
used by the intrinsic index calculus. -/
theorem field_continuousWithinAt_to_phase {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {K : Set ℝ} {t : ℝ}
    (hV : ContinuousWithinAt (fun r => (⟨γ r, V r⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t) :
    ContinuousWithinAt (fun r => (⟨γ r,V r⟩ : Phase S)) K t := by
  exact ((tangentRealization S).smooth_to_original _).1.comp_continuousWithinAt hV

theorem field_continuousWithinAt_of_phase {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {K : Set ℝ} {t : ℝ}
    (hV : ContinuousWithinAt (fun r => (⟨γ r,V r⟩ : Phase S)) K t) :
    ContinuousWithinAt (fun r => (⟨γ r, V r⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t := by
  exact ((tangentRealization S).smooth_from_original _).1.comp_continuousWithinAt hV

theorem field_continuousOn_to_phase {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {K : Set ℝ}
    (hV : ContinuousOn (fun r => (⟨γ r, V r⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K) :
    ContinuousOn (fun r => (⟨γ r,V r⟩ : Phase S)) K :=
  fun _ ht => field_continuousWithinAt_to_phase (hV _ ht)

theorem field_continuousOn_of_phase {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {K : Set ℝ}
    (hV : ContinuousOn (fun r => (⟨γ r,V r⟩ : Phase S)) K) :
    ContinuousOn (fun r => (⟨γ r, V r⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K :=
  fun _ ht => field_continuousWithinAt_of_phase (hV _ ht)

theorem smoothFieldOn_c1FieldOn {γ : ℝ → M} {K : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (γ t)} (hγ : ContinuousOn γ K)
    (hV : SmoothFieldOn γ V K) : C1FieldOn (B := tangentBundle S) γ V K := by
  intro t ht
  obtain ⟨e, he, hp, x, hx, hxt, heq⟩ := hV t ht
  let B := tangentStructure S
  let i : TangentIndex S := ⟨e, he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  have hU : (tangentBundle S).baseSet i = e.source := (tangentRealization S).baseSet i
  have hopen : IsOpen ((tangentBundle S).baseSet i) := hU ▸ e.open_source
  let y : ℝ → Euclidean n := fun r => (B.productCoordinates.linearEquiv.symm (x r)).2
  have hy : ContDiffAt ℝ 1 y t :=
    ((B.productCoordinates.linearEquiv.symm.contDiff.contDiffAt.comp t hx).snd).of_le (by simp)
  have hcoeff (r : ℝ) (hr : γ r ∈ e.source) :
      coefficientsAlong b γ V r =
        (B.productCoordinates.linearEquiv.symm
          ((B.chart e he) (⟨γ r,V r⟩ : Phase S)).val).2 := by
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b γ V r (hU ▸ hr),
      FirstVariation.tangentFrame_coordinates e he (γ r) hr,
      B.chart_apply e he (⟨γ r,V r⟩ : Phase S) hr, ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨_, hopen, b, hU ▸ hp, y, hy, ?_, ?_⟩
  · rw [hcoeff t hp, hxt]
  · filter_upwards [heq, (hγ t ht).eventually (e.open_source.mem_nhds hp)] with r hr hp'
    rw [hcoeff r hp', hr]

/-- Actual total-space continuity follows from the smooth chart germs and
continuity of the base, including at closed endpoints. -/
theorem smoothFieldOn_continuousOn {γ : ℝ → M} {K : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (γ t)} (hγ : ContinuousOn γ K)
    (hV : SmoothFieldOn γ V K) :
    ContinuousOn (fun t => (⟨γ t,V t⟩ : Phase S)) K := by
  have hc1 := smoothFieldOn_c1FieldOn hγ hV
  intro t ht
  obtain ⟨U, hU, b, hp, x, hx, hxt, heq⟩ := hc1 t ht
  exact field_continuousWithinAt_to_phase
    (ParallelTransport.field_continuousWithinAt_of_coefficients b hp (hγ t ht)
      (hx.continuousAt.continuousWithinAt.congr_of_eventuallyEq heq hxt))

/-- A smooth field's germ can be expressed in any canonical tangent chart
containing its base point. This is a chart-transition argument. -/
theorem smoothFieldOn_chart {γ : ℝ → M} {K : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (γ t)} (hγ : ContinuousOn γ K)
    (hV : SmoothFieldOn γ V K) {t : ℝ} (ht : t ∈ K)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : γ t ∈ e.source) :
    ∃ x : ℝ → Euclidean (n+n), ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      (((tangentStructure S).chart e he) (⟨γ t,V t⟩ : Phase S)).val = x t ∧
      (fun r => (((tangentStructure S).chart e he) (⟨γ r,V r⟩ : Phase S)).val)
        =ᶠ[𝓝[K] t] x := by
  obtain ⟨d, hd, hpd, x, hx, hxt, heqx⟩ := hV t ht
  let B := tangentStructure S
  let c := B.chart d hd
  let f := B.chart e he
  have hpc : (⟨γ t,V t⟩ : Phase S) ∈ c.source := by
    simpa only [c, B.chart_source, projection, mem_preimage] using hpd
  have hpf : (⟨γ t,V t⟩ : Phase S) ∈ f.source := by
    simpa only [f, B.chart_source, projection, mem_preimage] using hp
  obtain ⟨U, hU, hpU, F, hF, heqF⟩ :=
    SmoothManifolds.chartContDiffAt_of_compatible
      (B.manifold.smoothStructure.property.1.2 c
        (SmoothManifolds.TangentBundle.chart_mem S B d hd) f
        (SmoothManifolds.TangentBundle.chart_mem S B e he)) hpc hpf
  have hxU : x t ∈ U := hxt ▸ hpU
  refine ⟨F ∘ x, (hF.contDiffAt (hU.mem_nhds hxU)).comp t hx, ?_, ?_⟩
  · change (f (⟨γ t,V t⟩ : Phase S)).val = F (x t)
    rw [← hxt]
    exact heqF.eq_of_nhds.symm
  · have hc := smoothFieldOn_continuousOn hγ hV t ht
    filter_upwards [heqx, heqF.comp_tendsto hc] with r hr hFr
    exact hFr.symm.trans (congrArg F hr)

/-- Restriction and equality on the parameter domain preserve the chart-germ
notion of smoothness; representatives outside that domain are irrelevant. -/
theorem smoothFieldOn_mono {γ : ℝ → M} {K L : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (γ t)} (hV : SmoothFieldOn γ V K)
    (hLK : L ⊆ K) : SmoothFieldOn γ V L := by
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hV t (hLK ht)
  exact ⟨e,he,hp,x,hx,hxt,heq.filter_mono (nhdsWithin_mono t hLK)⟩

theorem smoothFieldOn_congr {γ : ℝ → M} {K : Set ℝ}
    {V W : (t : ℝ) → TangentSpace S (γ t)} (hV : SmoothFieldOn γ V K)
    (heq : ∀ t ∈ K, W t = V t) : SmoothFieldOn γ W K := by
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,hg⟩ := hV t ht
  refine ⟨e,he,hp,x,hx,?_,?_⟩
  · rw [heq t ht]
    exact hxt
  · filter_upwards [hg, self_mem_nhdsWithin] with r hr hrK
    rw [heq r hrK]
    exact hr

/-- Restrict an actual global smooth section along a coordinate-smooth
segment. The field is not supplied as a smoothness certificate. -/
theorem smoothFieldOn_section {γ : ℝ → M} {a b : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b) (X : Field S) :
    SmoothFieldOn γ (fun t => X.val (γ t)) (Icc a b) := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hγ.2 (0,t) ⟨h0,ht⟩
  let B := tangentStructure S
  let d := B.chart e he
  let f : M → Phase S := fun p => ⟨p,X.val p⟩
  have hfp : f (γ t) ∈ d.source := by
    simpa only [d, f, B.chart_source, projection, mem_preimage] using hp
  have hf := (originalField S X).smooth (γ t)
  obtain ⟨U,hU,hpU,F,hF,heqF⟩ := hf.2 e he d
    (SmoothManifolds.TangentBundle.chart_mem S B e he) hp hfp
  let y : ℝ → Euclidean n := fun r => x (0,r)
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have htend : Tendsto (fun r : ℝ => ((0 : ℝ),r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-1 : ℝ) 1 ×ˢ Icc a b] (0,t)) :=
    (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have hg := heqx.comp_tendsto htend
  have hyU : y t ∈ U := by
    dsimp only [y]
    rw [hxt]
    exact hpU
  refine ⟨e,he,hp,F ∘ y,(hF.contDiffAt (hU.mem_nhds hyU)).comp t hy,?_,?_⟩
  · change (d (f (γ t))).val = F (x (0,t))
    rw [hxt]
    exact heqF.eq_of_nhds.symm
  · filter_upwards [hg, heqF.comp_tendsto (hc t ht)] with r hr hFr
    exact hFr.symm.trans (congrArg F hr)


theorem smoothFieldOn_smul {γ : ℝ → M} {K : Set ℝ}
    {V : (t : ℝ) → TangentSpace S (γ t)} (hγ : ContinuousOn γ K)
    (hV : SmoothFieldOn γ V K) {α : ℝ → ℝ} (hα : ContDiff ℝ (⊤ : ℕ∞) α) :
    SmoothFieldOn γ (fun t => α t • V t) K := by
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hV t ht
  let B := tangentStructure S
  let y : ℝ → Euclidean (n+n) := fun r => B.productCoordinates.linearEquiv
    ((B.productCoordinates.linearEquiv.symm (x r)).1,
      α r • (B.productCoordinates.linearEquiv.symm (x r)).2)
  have hx' := B.productCoordinates.linearEquiv.symm.contDiff.contDiffAt.comp t hx
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y t :=
    B.productCoordinates.linearEquiv.contDiff.contDiffAt.comp t
      (hx'.fst.prodMk (hα.contDiffAt.smul hx'.snd))
  refine ⟨e,he,hp,y,hy,?_,?_⟩
  · dsimp only [y]
    rw [← hxt]
    exact MinimizingIndexForm.tangentScale_chart e he ⟨γ t,V t⟩ hp (α t)
  · filter_upwards [heqx, (hγ t ht).eventually (e.open_source.mem_nhds hp)] with r hr hpr
    change ((B.chart e he) (MinimizingIndexForm.tangentScale
      (α r, (⟨γ r,V r⟩ : Phase S)))).val = y r
    rw [MinimizingIndexForm.tangentScale_chart e he (⟨γ r,V r⟩ : Phase S) hpr, hr]

/-- Smooth fields form a vector space along the fixed base. Both witnesses
are first put into a common actual tangent chart. -/
theorem smoothFieldOn_add {γ : ℝ → M} {K : Set ℝ}
    {V W : (t : ℝ) → TangentSpace S (γ t)} (hγ : ContinuousOn γ K)
    (hV : SmoothFieldOn γ V K) (hW : SmoothFieldOn γ W K) :
    SmoothFieldOn γ (fun t => V t + W t) K := by
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hV t ht
  obtain ⟨z,hz,hzt,heqz⟩ := smoothFieldOn_chart hγ hW ht e he hp
  let B := tangentStructure S
  let y : ℝ → Euclidean (n+n) := fun r => B.productCoordinates.linearEquiv
    ((B.productCoordinates.linearEquiv.symm (x r)).1,
      (B.productCoordinates.linearEquiv.symm (x r)).2 +
        (B.productCoordinates.linearEquiv.symm (z r)).2)
  have hx' := B.productCoordinates.linearEquiv.symm.contDiff.contDiffAt.comp t hx
  have hz' := B.productCoordinates.linearEquiv.symm.contDiff.contDiffAt.comp t hz
  have hy : ContDiffAt ℝ (⊤ : ℕ∞) y t :=
    B.productCoordinates.linearEquiv.contDiff.contDiffAt.comp t
      (hx'.fst.prodMk (hx'.snd.add hz'.snd))
  have hchart (r : ℝ) (hr : γ r ∈ e.source) :
      ((B.chart e he) (⟨γ r,V r + W r⟩ : Phase S)).val =
        B.productCoordinates.linearEquiv
          ((B.productCoordinates.linearEquiv.symm
            ((B.chart e he) (⟨γ r,V r⟩ : Phase S)).val).1,
           (B.productCoordinates.linearEquiv.symm
            ((B.chart e he) (⟨γ r,V r⟩ : Phase S)).val).2 +
           (B.productCoordinates.linearEquiv.symm
            ((B.chart e he) (⟨γ r,W r⟩ : Phase S)).val).2) := by
    simp only [B.chart_apply e he (⟨γ r,V r+W r⟩ : Phase S) hr,
      B.chart_apply e he (⟨γ r,V r⟩ : Phase S) hr,
      B.chart_apply e he (⟨γ r,W r⟩ : Phase S) hr, map_add,
      ContinuousLinearEquiv.symm_apply_apply]
  refine ⟨e,he,hp,y,hy,?_,?_⟩
  · dsimp only [y]
    rw [← hxt, ← hzt]
    exact hchart t hp
  · filter_upwards [heqx,heqz,(hγ t ht).eventually (e.open_source.mem_nhds hp)]
      with r hr hzr hpr
    dsimp only [y]
    rw [← hr, ← hzr]
    exact hchart r hpr

/-- The zero section supplies smooth zero fields on any smooth segment. -/
theorem smoothFieldOn_zero {γ : ℝ → M} {a b : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b) :
    SmoothFieldOn (S := S) γ (fun _ => 0) (Icc a b) :=
  smoothFieldOn_section hγ (0 : Field S)

/-- A global section through the prescribed interior vector, multiplied by
an explicit polynomial, gives a smooth field with the two required endpoint
zeros. No parallel-frame or cutoff existence is assumed. -/
theorem exists_smooth_test_field {γ : ℝ → M} {a b c : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    (hac : a < c) (hcb : c < b) (v : TangentSpace S (γ c)) :
    ∃ Z : (t : ℝ) → TangentSpace S (γ t),
      SmoothFieldOn γ Z (Icc a b) ∧
      C1FieldOn (B := tangentBundle S) γ Z (Icc a b) ∧
      Z a = 0 ∧ Z b = 0 ∧ Z c = v := by
  obtain ⟨X,hX⟩ := ConnectionForms.section_evaluation_surjective (tangentBundle S) (γ c) v
  let α : ℝ → ℝ := fun t => (t-a)*(b-t)/((c-a)*(b-c))
  let Z : (t : ℝ) → TangentSpace S (γ t) := fun t => α t • X.val (γ t)
  have hα : ContDiff ℝ (⊤ : ℕ∞) α :=
    ((contDiff_id.sub contDiff_const).mul (contDiff_const.sub contDiff_id)).div_const _
  have hc : ContinuousOn γ (Icc a b) :=
    FirstVariation.variation_continuousOn_slice (s := 0) hγ (by constructor <;> norm_num)
  have hs : SmoothFieldOn γ Z (Icc a b) :=
    smoothFieldOn_smul hc (smoothFieldOn_section hγ X) hα
  refine ⟨Z,hs,smoothFieldOn_c1FieldOn hc hs,?_,?_,?_⟩
  · simp only [Z,α,sub_self,zero_mul,zero_div,zero_smul]
  · simp only [Z,α,sub_self,mul_zero,zero_div,zero_smul]
  · have hne : (c-a)*(b-c) ≠ 0 := mul_ne_zero (sub_ne_zero.mpr hac.ne')
      (sub_ne_zero.mpr hcb.ne')
    simp only [Z,α,div_self hne,one_smul,hX]

/-- The zero extension at a zero of J and all its smooth test perturbations
are actual continuous piecewise smooth fields on the two-piece partition. -/
theorem truncated_smooth_perturbation {γ : ℝ → M} {a b c : ℝ}
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a b)
    (hac : a < c) (hcb : c < b)
    {J Z : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : SmoothFieldOn γ J (Icc a c)) (hJc : J c = 0)
    (hZ : SmoothFieldOn γ Z (Icc a b)) (s : ℝ) :
    PiecewiseSmoothFieldOn γ
      (fun t => ParallelTransport.fieldGlue J (fun _ => 0) c t + s • Z t) ![a,c,b] := by
  let W := ParallelTransport.fieldGlue J (fun _ => 0) c
  have hc : ContinuousOn γ (Icc a b) :=
    FirstVariation.variation_continuousOn_slice (s := 0) hγ (by constructor <;> norm_num)
  have hleft : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb.le
  have hright : Icc c b ⊆ Icc a b := Icc_subset_Icc hac.le le_rfl
  have hγright := SecondVariation.smoothVariationOn_mono_interval hγ hac.le le_rfl
  have hWleft : SmoothFieldOn γ W (Icc a c) :=
    smoothFieldOn_congr hJ (fun t ht => ParallelTransport.fieldGlue_left J (fun _ => 0) ht.2)
  have hWright : SmoothFieldOn γ W (Icc c b) :=
    smoothFieldOn_congr (smoothFieldOn_zero hγright)
      (fun t ht => ParallelTransport.fieldGlue_right J (fun _ => 0) hJc ht.1)
  have hWcont : ContinuousOn (fun t => (⟨γ t,W t⟩ : Phase S)) (Icc a b) := by
    apply field_continuousOn_to_phase
    apply ParallelTransport.fieldGlue_continuousOn J (fun _ => 0) hac.le hcb.le
    · exact hJc
    · exact field_continuousOn_of_phase (smoothFieldOn_continuousOn (hc.mono hleft) hJ)
    · exact field_continuousOn_of_phase
        (smoothFieldOn_continuousOn (hc.mono hright) (smoothFieldOn_zero hγright))
  have hsZ : SmoothFieldOn γ (fun t => s • Z t) (Icc a b) :=
    smoothFieldOn_smul hc hZ contDiff_const
  constructor
  · exact field_continuousOn_to_phase
      (ParallelTransport.continuousOn_field_add (B := tangentBundle S) hc
        (field_continuousOn_of_phase hWcont)
        (field_continuousOn_of_phase (smoothFieldOn_continuousOn hc hsZ)))
  · intro i
    fin_cases i
    · exact smoothFieldOn_add (hc.mono hleft) hWleft (smoothFieldOn_mono hsZ hleft)
    · exact smoothFieldOn_add (hc.mono hright) hWright (smoothFieldOn_mono hsZ hright)



/-- The complete index-form contradiction for an actual truncated Jacobi
field and an actual test field. Only constructing these fields with the
stated regularity and proving the nonzero terminal derivative remain when
applying this lemma to conjugacy. All index identities are conclusions of
the preceding proved lemmas. -/
theorem not_minimizing_of_jacobi_test (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {a b : ℝ} (γ : PiecewiseC1Curve S a b)
    (hγ : IsAffineGeodesicSegment C γ a b) {c : ℝ} (hac : a < c) (hcb : c < b)
    {J D Z : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : C1FieldOn (B := tangentBundle S) γ J (Icc a c))
    (hZleft : C1FieldOn (B := tangentBundle S) γ Z (Icc a c))
    (hZright : C1FieldOn (B := tangentBundle S) γ Z (Icc c b))
    (hD : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) t
        (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t))))
    (hJa : J a = 0) (hJc : J c = 0) (hDc : D c ≠ 0)
    (hZa : Z a = 0) (hZb : Z b = 0) (hZc : Z c = -D c)
    (hfields : ∀ s : ℝ, PiecewiseSmoothFieldOn γ
      (fun t => ParallelTransport.fieldGlue J (fun _ => 0) c t + s • Z t) ![a,c,b]) :
    ¬ IsLengthMinimizing g γ := by
  intro hmin
  let W := ParallelTransport.fieldGlue J (fun _ => 0) c
  let node : Fin 3 → ℝ := ![a,c,b]
  have hnode : StrictMono node := by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · simpa [node] using hac
    · simpa [node] using hcb
  have hWleft : C1FieldOn (B := tangentBundle S) γ W (Icc a c) :=
    ParallelTransport.c1FieldOn_congr hJ (fun t ht =>
      ParallelTransport.fieldGlue_left J (fun _ => 0) ht.2)
  have hWright : C1FieldOn (B := tangentBundle S) γ W (Icc c b) :=
    ParallelTransport.c1FieldOn_congr (c1FieldOn_zero (S := S) γ (Icc c b)) (fun t ht =>
      ParallelTransport.fieldGlue_right J (fun _ => 0) hJc ht.1)
  have hWpieces : ∀ i : Fin 2, C1FieldOn (B := tangentBundle S) γ W
      (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    · exact hWleft
    · exact hWright
  have hZpieces : ∀ i : Fin 2, C1FieldOn (B := tangentBundle S) γ Z
      (Icc (node i.castSucc) (node i.succ)) := by
    intro i
    fin_cases i
    · exact hZleft
    · exact hZright
  have hWa : W a = 0 :=
    (ParallelTransport.fieldGlue_left J (fun _ => 0) hac.le).trans hJa
  have hWb : W b = 0 := ParallelTransport.fieldGlue_right J (fun _ => 0) hJc hcb.le
  have hWW : indexForm g C R γ a b W W = 0 :=
    truncated_jacobi_self_index_zero g C hC R hac hcb hγ.1 hJ ⟨D, hD⟩ hJa hJc
  have horth := minimizing_null_orthogonal g C hC R hR γ (hac.trans hcb) hγ hmin
    node hnode rfl rfl hWpieces hZpieces hfields hWa hWb hZa hZb hWW
  have hcross : indexForm g C R γ a b W Z = -pairing g (γ c) (D c) (D c) := by
    rw [truncated_jacobi_index_boundary g C hC R hac hcb hγ.1 hJ hZleft hZright hD hJc hZa,
      hZc]
    exact (pairing g (γ c) (D c)).map_neg (D c)
  have hp : 0 < pairing g (γ c) (D c) (D c) := g.positive _ _ hDc
  linarith

/-- With closed-segment Jacobi regularity and terminal uniqueness in hand,
the remaining field construction and contradiction are unconditional. -/
theorem not_minimizing_of_smooth_jacobi (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {a b : ℝ} (γ : PiecewiseC1Curve S a b)
    (hγ : IsAffineGeodesicSegment C γ a b) {c : ℝ} (hac : a < c) (hcb : c < b)
    {J D : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : SmoothFieldOn γ J (Icc a c))
    (hD : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) t
        (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t))))
    (hJa : J a = 0) (hJc : J c = 0) (hDc : D c ≠ 0) :
    ¬ IsLengthMinimizing g γ := by
  obtain ⟨Z,hZ,hZc1,hZa,hZb,hZc⟩ := exists_smooth_test_field hγ.1 hac hcb (-D c)
  have hc : ContinuousOn (γ : ℝ → M) (Icc a b) :=
    FirstVariation.variation_continuousOn_slice (s := 0) hγ.1 (by constructor <;> norm_num)
  have hleft : Icc a c ⊆ Icc a b := Icc_subset_Icc le_rfl hcb.le
  have hright : Icc c b ⊆ Icc a b := Icc_subset_Icc hac.le le_rfl
  exact not_minimizing_of_jacobi_test g C hC R hR γ hγ hac hcb
    (smoothFieldOn_c1FieldOn (hc.mono hleft) hJ)
    (smoothFieldOn_c1FieldOn (hc.mono hleft) (smoothFieldOn_mono hZ hleft))
    (smoothFieldOn_c1FieldOn (hc.mono hright) (smoothFieldOn_mono hZ hright))
    hD hJa hJc hDc hZa hZb hZc (truncated_smooth_perturbation hγ.1 hac hcb hJ hJc hZ)


theorem covariantDerivative_continuousWithinAt
    (C : Connection (tangentBundle S)) {γ : ℝ → M} {K : Set ℝ} {t : ℝ}
    {J : (t : ℝ) → TangentSpace S (γ t)} {v : TangentSpace S (γ t)}
    (hJ : HasCovariantDerivativeWithinAt C γ J K t v) :
    ContinuousWithinAt (fun r => (⟨γ r,J r⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t := by
  obtain ⟨T,hT,U,hU,b,hp,x,hx,_⟩ := hJ
  exact ParallelTransport.field_continuousWithinAt_of_coefficients b hp hT.1
    hx.continuousWithinAt

section LinearSmoothExtension
variable {F : Type u} [NormedAddCommGroup F] [NormedSpace ℝ F]
theorem smoothAt_of_linear_ode {A : ℝ → F →L[ℝ] F} {Y : ℝ → F} {t : ℝ}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A t) (hY : ContDiff ℝ 1 Y)
    (hd : ∀ᶠ r in 𝓝 t, HasDerivAt Y (A r (Y r)) r) :
    ContDiffAt ℝ (⊤ : ℕ∞) Y t := by
  apply contDiffAt_infty.mpr
  intro k
  induction k with
  | zero => exact hY.contDiffAt.of_le (by simp)
  | succ k ih =>
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun r => ContinuousLinearMap.toSpanSingleton ℝ (A r (Y r)), ?_, ?_⟩
    · exact ⟨{r | HasDerivAt Y (A r (Y r)) r}, hd, fun r hr => hr.hasFDerivAt⟩
    · exact (ContinuousLinearMap.toSpanSingletonLIE ℝ F).toContinuousLinearEquiv.contDiff.contDiffAt.comp t
        ((hA.of_le (by simp)).clm_apply ih)

variable [CompleteSpace F]
/-- A solution of a locally smooth linear equation on a closed segment has
an ambient smooth representative near every point, including its endpoints. -/
theorem linear_ode_smooth_extension {a c t : ℝ} (hac : a < c)
    (ht : t ∈ Icc a c) {A : ℝ → F →L[ℝ] F} {f : ℝ → F}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A t)
    (hd : ∀ᶠ r in 𝓝[Icc a c] t,
      HasDerivWithinAt f (A r (f r)) (Icc a c) r) :
    ∃ Y : ℝ → F, ContDiffAt ℝ (⊤ : ℕ∞) Y t ∧ Y t = f t ∧
      f =ᶠ[𝓝[Icc a c] t] Y := by
  obtain ⟨U,hUt,hAU⟩ := hA.contDiffOn (m := 0) (by simp) (by simp)
  obtain ⟨e,d,⟨het,htd⟩,hedu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hUt
  let l : ℝ := (e+t)/2
  let q : ℝ := (t+d)/2
  have hlt : l < t := by dsimp [l]; linarith
  have htq : t < q := by dsimp [q]; linarith
  have heqU : Icc l q ⊆ U := by
    intro r hr
    apply hedu
    constructor <;> dsimp [l,q] at hr <;> linarith [hr.1,hr.2]
  have hAc : ContinuousOn A (Icc l q) := hAU.continuousOn.mono heqU
  let Aext : ℝ → F →L[ℝ] F := IccExtend (hlt.trans htq).le
    (fun r : Icc l q => A r)
  have hAe : Continuous Aext := hAc.domRestrict.Icc_extend'
  have hAe_eq (r : ℝ) (hr : r ∈ Icc l q) : Aext r = A r :=
    IccExtend_of_mem (hlt.trans htq).le _ hr
  let I : D13Unified.TimeInterval := ⟨univ,univ_nonempty,ordConnected_univ⟩
  obtain ⟨Y,hYc,hYt,hYd,_,hY1,_⟩ :=
    D13Unified.Ch07.LinearSystemExistence.existence I Aext t (f t)
      (mem_univ _) hAe.continuousOn
  have hYdiff (r : ℝ) (hr : r ∈ Ioo l q) : HasDerivAt Y (A r (Y r)) r := by
    have h := hYd r (mem_univ r)
    change HasDerivWithinAt Y (Aext r (Y r)) univ r at h
    rw [hasDerivWithinAt_univ, hAe_eq r (Ioo_subset_Icc_self hr)] at h
    exact h
  have hYsm : ContDiffAt ℝ (⊤ : ℕ∞) Y t :=
    smoothAt_of_linear_ode hA (contDiffOn_univ.mp hY1)
      (Filter.mem_of_superset (Ioo_mem_nhds hlt htq) hYdiff)
  obtain ⟨l',q',hlq',htK,hKJ,hKeq,hKn⟩ :=
    ParallelTransport.exists_compact_subinterval hac ht
      (Filter.inter_mem hd (mem_nhdsWithin_of_mem_nhds (Ioo_mem_nhds hlt htq)))
  have hKouter : Icc l' q' ⊆ Icc l q :=
    fun r hr => Ioo_subset_Icc_self (hKeq hr).2
  have hfc : ContinuousOn f (Icc l' q') :=
    fun r hr => ((hKeq hr).1.continuousWithinAt).mono hKJ
  have hfd : ∀ r ∈ Icc l' q',
      HasDerivWithinAt f (A r (f r)) (Icc l' q') r :=
    fun r hr => (hKeq hr).1.mono hKJ
  have hYdc : ∀ r ∈ Icc l' q',
      HasDerivWithinAt Y (A r (Y r)) (Icc l' q') r :=
    fun r hr => (hYdiff r (hKeq hr).2).hasDerivWithinAt
  obtain ⟨Z,hZc,hZt,hZd,_,hu⟩ := ParallelTransport.linear_ode_on_compact hlq'.le
    A (hAc.mono hKouter) htK (f t)
  have heq : EqOn f Y (Icc l' q') := by
    intro r hr
    exact (hu f hfc rfl hfd hr).trans
      (hu Y (hYc.mono (subset_univ _)) hYt hYdc hr).symm
  refine ⟨Y,hYsm,hYt,?_⟩
  exact Filter.mem_of_superset hKn heq

end LinearSmoothExtension

/-- Smooth germs of the position coordinates and of the canonical frame
coefficients give the actual smooth tangent-chart germ. -/
theorem tangent_chart_germ_of_coefficients {γ : ℝ → M} {K : Set ℝ}
    (hγ : ContinuousOn γ K) {J : (t : ℝ) → TangentSpace S (γ t)}
    {t : ℝ} (ht : t ∈ K) (e : ModelChart n .euclidean M)
    (he : e ∈ S.smoothStructure.val) (hp : γ t ∈ e.source)
    (z j : ℝ → Euclidean n) (hz : ContDiffAt ℝ (⊤ : ℕ∞) z t)
    (hj : ContDiffAt ℝ (⊤ : ℕ∞) j t)
    (hzt : z t = (e (γ t)).val)
    (heqz : (fun r => (e (γ r)).val) =ᶠ[𝓝[K] t] z)
    (hjt : j t = coefficientsAlong
      (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) ⟨e,he⟩) γ J t)
    (heqj : coefficientsAlong
      (SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) ⟨e,he⟩) γ J
      =ᶠ[𝓝[K] t] j) :
    ∃ x : ℝ → Euclidean (n+n), ContDiffAt ℝ (⊤ : ℕ∞) x t ∧
      (((tangentStructure S).chart e he) (⟨γ t,J t⟩ : Phase S)).val = x t ∧
      (fun r => (((tangentStructure S).chart e he) (⟨γ r,J r⟩ : Phase S)).val)
        =ᶠ[𝓝[K] t] x := by
  let B := tangentStructure S
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  let x : ℝ → Euclidean (n+n) := fun r => B.productCoordinates.linearEquiv (z r,j r)
  have hchart (r : ℝ) (hr : γ r ∈ e.source) :
      ((B.chart e he) (⟨γ r,J r⟩ : Phase S)).val =
        B.productCoordinates.linearEquiv ((e (γ r)).val,coefficientsAlong b γ J r) := by
    have hU : (tangentBundle S).baseSet i = e.source := (tangentRealization S).baseSet i
    rw [B.chart_apply e he _ hr,
      CurveCovariantDerivative.coefficientsAlong_of_mem b γ J r (hU ▸ hr),
      FirstVariation.tangentFrame_coordinates e he (γ r) hr]
  refine ⟨x,B.productCoordinates.linearEquiv.contDiff.contDiffAt.comp t (hz.prodMk hj),?_,?_⟩
  · dsimp only [x]
    rw [hzt,hjt]
    exact hchart t hp
  · filter_upwards [heqz,heqj,(hγ t ht).eventually (e.open_source.mem_nhds hp)] with r hzr hjr hpr
    dsimp only [x]
    rw [← hzr,← hjr]
    exact hchart r hpr


open scoped Matrix.Norms.Operator

theorem curvature_coordinates_continuousWithinAt (R : CurvatureTensor S)
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {c : ℝ → M} {f g h : (t : ℝ) → TangentSpace S (c t)} {K : Set ℝ} {t : ℝ}
    (hp : c t ∈ (tangentBundle S).baseSet i) (hc : ContinuousWithinAt c K t)
    (hf : ContinuousWithinAt (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t)
    (hg : ContinuousWithinAt (fun t => (⟨c t, g t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t)
    (hh : ContinuousWithinAt (fun t => (⟨c t, h t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t) :
    ContinuousWithinAt (fun s => ((tangentBundle S).trivialization i
      ⟨c s, R.val (c s) (f s) (g s) (h s)⟩).2) K t := by
  classical
  let B := tangentBundle S
  let cf : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, f s⟩).2
  let cg : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, g s⟩).2
  let ch : ℝ → Euclidean n := fun s => ((B.trivialization i) ⟨c s, h s⟩).2
  have hcf : ContinuousWithinAt cf K t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, f t⟩ hp).1.comp_continuousWithinAt (f := fun s : ℝ => (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hf
  have hcg : ContinuousWithinAt cg K t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, g t⟩ hp).1.comp_continuousWithinAt (f := fun s : ℝ => (⟨c s, g s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hg
  have hch : ContinuousWithinAt ch K t :=
    (SmoothManifolds.Frames.trivializationCoordinates_smoothAt B i ⟨c t, h t⟩ hp).1.comp_continuousWithinAt (f := fun s : ℝ => (⟨c s, h s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) hh
  let a : Fin n → Fin n → Fin n → M → Euclidean n := fun j k l q =>
    ((B.trivialization i) ⟨q, R.val q
      ((B.trivialization i).symm q (Pi.single j 1))
      ((B.trivialization i).symm q (Pi.single k 1))
      ((B.trivialization i).symm q (Pi.single l 1))⟩).2
  have ha (j k l : Fin n) : ContinuousWithinAt (fun s => a j k l (c s)) K t :=
    (CurvatureAlgebra.tensor_coordinates_smooth R i j k l (c t) hp).1.comp_continuousWithinAt hc
  have hsum : ContinuousWithinAt
      (fun s => ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
        (cf s j * (cg s k * ch s l)) • a j k l (c s)) K t := by
    apply tendsto_finsetSum
    intro j _
    apply tendsto_finsetSum
    intro k _
    apply tendsto_finsetSum
    intro l _
    exact (((continuous_apply j).continuousAt.comp_continuousWithinAt hcf).mul (((continuous_apply k).continuousAt.comp_continuousWithinAt hcg).mul ((continuous_apply l).continuousAt.comp_continuousWithinAt hch))).smul (ha j k l)
  have heq (s : ℝ) (hs : c s ∈ B.baseSet i) :
      ((B.trivialization i) ⟨c s, R.val (c s) (f s) (g s) (h s)⟩).2 =
        ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          (cf s j * (cg s k * ch s l)) • a j k l (c s) := by
    have hq := congrArg (B.fiberCoordinates i (c s) hs)
      (JacobiIVP.trilinear_coordinates (B.fiberCoordinates i (c s) hs)
        (R.val (c s)) (f s) (g s) (h s))
    simpa only [map_sum, map_smul,
      SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_apply,
      SmoothManifolds.BundleData.SmoothVectorBundle.fiberCoordinates_symm_apply,
      cf, cg, ch, a] using hq
  apply hsum.congr_of_eventuallyEq _ (heq t hp)
  have ho : IsOpen (B.baseSet i) :=
    B.trivialization_baseSet i ▸ (B.trivialization i).open_baseSet
  filter_upwards [hc.eventually (ho.mem_nhds hp)] with s hs
  exact heq s hs

/-- A continuous coordinate formula and base curve determine actual
continuity in the original tangent total space. -/
theorem tangent_continuousWithinAt_of_coordinates
    (i : SmoothManifolds.BundleOperationsData.TangentIndex S)
    {c : ℝ → M} {f : (t : ℝ) → TangentSpace S (c t)} {K : Set ℝ} {t : ℝ}
    (hp : c t ∈ (tangentBundle S).baseSet i) (hc : ContinuousWithinAt c K t)
    (hf : ContinuousWithinAt (fun s => ((tangentBundle S).trivialization i
      ⟨c s, f s⟩).2) K t) :
    ContinuousWithinAt (fun s => (⟨c s, f s⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t := by
  let B := tangentBundle S
  let e := B.trivialization i
  let a : ℝ → Euclidean n := fun s => (e ⟨c s, f s⟩).2
  have hp' : c t ∈ e.baseSet := (B.trivialization_baseSet i).symm ▸ hp
  have hecont : ContinuousAt e.toOpenPartialHomeomorph.symm (c t, a t) :=
    e.toOpenPartialHomeomorph.continuousAt_symm (e.mem_target.mpr hp')
  have heq (s : ℝ) (hs : c s ∈ e.baseSet) :
      (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)) =
        e.toOpenPartialHomeomorph.symm (c s, a s) := by
    have hse : (⟨c s, f s⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S)) ∈ e.source :=
      e.mem_source.mpr hs
    have heq' : (c s, a s) = e ⟨c s, f s⟩ := by
      apply Prod.ext
      · exact (e.coe_fst hse).symm
      · rfl
    rw [heq']
    exact (e.toOpenPartialHomeomorph.left_inv hse).symm
  apply (hecont.comp_continuousWithinAt (f := fun s => (c s, a s))
    (s := K) (x := t) (hc.prodMk hf)).congr_of_eventuallyEq _ (heq t hp')
  filter_upwards [hc.eventually (e.open_baseSet.mem_nhds hp')] with s hs
  exact heq s hs

/-- Curvature evaluation preserves total-space continuity along curves. -/
theorem curvature_continuousWithinAt (R : CurvatureTensor S)
    {c : ℝ → M} {f g h : (t : ℝ) → TangentSpace S (c t)} {K : Set ℝ} {t : ℝ}
    (hc : ContinuousWithinAt c K t)
    (hf : ContinuousWithinAt (fun t => (⟨c t, f t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t)
    (hg : ContinuousWithinAt (fun t => (⟨c t, g t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t)
    (hh : ContinuousWithinAt (fun t => (⟨c t, h t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t) :
    ContinuousWithinAt (fun s => (⟨c s, R.val (c s) (f s) (g s) (h s)⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K t := by
  obtain ⟨i, hi⟩ := (tangentBundle S).covers (c t)
  exact tangent_continuousWithinAt_of_coordinates i hi hc
    (curvature_coordinates_continuousWithinAt R i hi hc hf hg hh)



/-- The actual first derivative in any local frame. -/
theorem covariant_coefficients_derivative (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {γ : ℝ → M} {K : Set ℝ} (hγ : CoordinateC1On S γ K)
    (hc : ContinuousOn γ K) (hK : UniqueDiffOn ℝ K)
    {J : (t : ℝ) → TangentSpace S (γ t)} {t : ℝ} (ht : t ∈ K)
    (hp : γ t ∈ U) {D : TangentSpace S (γ t)}
    (hJ : HasCovariantDerivativeWithinAt C γ J K t D) :
    HasDerivWithinAt (coefficientsAlong b γ J)
      ((b.basis ⟨γ t,hp⟩).equivFun D -
        (ParallelTransport.matrixAlong C b γ K t).mulVec (coefficientsAlong b γ J t)) K t := by
  classical
  obtain ⟨v,hv⟩ := CurveCovariantDerivative.exists_coefficients_deriv C ht hJ b hp
  have heq := CurveCovariantDerivative.local_formula C ht (hK t ht) hJ b hp
    (PiecewiseCurves.withinVelocity_spec hγ hc ht) hv
  have heq' := congrArg (b.basis ⟨γ t,hp⟩).equivFun heq
  simp only [frameDerivative, LinearEquiv.apply_symm_apply] at heq'
  have hvval : v = (b.basis ⟨γ t,hp⟩).equivFun D -
      (ParallelTransport.matrixAlong C b γ K t).mulVec (coefficientsAlong b γ J t) := by
    rw [ParallelTransport.matrixAlong, dite_eq_left hp]
    exact eq_sub_iff_add_eq.mpr heq'.symm
  exact hvval ▸ hv

noncomputable def jacobiBlockOperator (G A : Euclidean n →L[ℝ] Euclidean n) :
    (Euclidean n × Euclidean n) →L[ℝ] (Euclidean n × Euclidean n) :=
  (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n) -
    G.comp (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n))).prod
    (-(A.comp (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n))) -
      G.comp (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n)))

@[simp] theorem jacobiBlockOperator_apply (G A : Euclidean n →L[ℝ] Euclidean n)
    (x : Euclidean n × Euclidean n) :
    jacobiBlockOperator G A x = (x.2 - G x.1, -(A x.1) - G x.2) := rfl

theorem jacobiBlockOperator_continuousOn {K : Set ℝ}
    {G A : ℝ → Euclidean n →L[ℝ] Euclidean n}
    (hG : ContinuousOn G K) (hA : ContinuousOn A K) :
    ContinuousOn (fun t => jacobiBlockOperator (G t) (A t)) K := by
  exact (ContinuousLinearMap.prodₗᵢ ℝ).continuous.comp_continuousOn
    ((continuousOn_const.sub (hG.clm_comp continuousOn_const)).prodMk
      ((hA.clm_comp continuousOn_const).neg.sub (hG.clm_comp continuousOn_const)))

noncomputable def frameRadialOperator (R : CurvatureTensor S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    (γ : ℝ → M) (T : (t : ℝ) → TangentSpace S (γ t)) (t : ℝ) :
    Euclidean n →L[ℝ] Euclidean n :=
  JacobiIVP.columnOperator (fun i => coefficientsAlong b γ
    (fun s => R.val (γ s) (frameFieldAlong b γ (fun _ => Pi.single i 1) s)
      (T s) (T s)) t)

theorem frameRadialOperator_apply (R : CurvatureTensor S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {γ : ℝ → M} {T J : (t : ℝ) → TangentSpace S (γ t)}
    {t : ℝ} (hp : γ t ∈ U) :
    frameRadialOperator R b γ T t (coefficientsAlong b γ J t) =
      coefficientsAlong b γ (fun s => R.val (γ s) (J s) (T s) (T s)) t := by
  classical
  simp only [frameRadialOperator, JacobiIVP.columnOperator_apply,
    CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ t hp,
    frameFieldAlong, dite_eq_left hp]
  let e := (b.basis ⟨γ t,hp⟩).equivFun
  have hx : J t = ∑ i : Fin n, e (J t) i • e.symm (Pi.single i 1) := by
    simpa only [map_sum,map_smul,LinearEquiv.symm_apply_apply,
      Pi.basisFun_apply,Pi.basisFun_equivFun,LinearEquiv.refl_apply] using
      (congrArg e.symm ((Pi.basisFun ℝ (Fin n)).sum_equivFun (e (J t)))).symm
  apply Eq.symm
  calc
    _ = e (∑ i : Fin n, e (J t) i •
          R.val (γ t) (e.symm (Pi.single i 1)) (T t) (T t)) := by
      apply congrArg e
      calc
        _ = R.val (γ t) (∑ i : Fin n, e (J t) i • e.symm (Pi.single i 1))
            (T t) (T t) := congrArg (fun v => R.val (γ t) v (T t) (T t)) hx
        _ = _ := by simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
    _ = _ := by simp only [e,map_sum,map_smul]


theorem frameRadialOperator_continuousOn (R : CurvatureTensor S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {γ : ℝ → M} {T : (t : ℝ) → TangentSpace S (γ t)} {K : Set ℝ}
    (hc : ContinuousOn γ K) (hUcurve : MapsTo γ K U)
    (hT : ContinuousOn (fun t => (⟨γ t,T t⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) K) :
    ContinuousOn (frameRadialOperator R b γ T) K := by
  intro t ht
  change ContinuousWithinAt (fun s => ∑ i : Fin n, (ContinuousLinearMap.proj i).smulRight
    (coefficientsAlong b γ (fun r => R.val (γ r)
      (frameFieldAlong b γ (fun _ => Pi.single i 1) r) (T r) (T r)) s)) K t
  apply tendsto_finsetSum
  intro i _
  apply (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
    (ContinuousLinearMap.proj i)).continuous.continuousAt.comp_continuousWithinAt
  apply ParallelTransport.coefficients_continuousWithinAt b (hUcurve ht)
  exact curvature_continuousWithinAt R (hc t ht)
    ((ParallelTransport.frameField_continuousOn b hc continuousOn_const hUcurve) t ht)
    (hT t ht) (hT t ht)

/-- Uniqueness of the genuine first-order Jacobi system in one frame, including
its one-sided endpoint equations. -/
theorem frame_jacobi_system_unique (C : Connection (tangentBundle S))
    (R : CurvatureTensor S)
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {γ : ℝ → M} {l q s : ℝ} (hlq : l < q)
    (hc1 : CoordinateC1On S γ (Icc l q)) (hc : ContinuousOn γ (Icc l q))
    (hUcurve : MapsTo γ (Icc l q) U)
    {T J D K E : (t : ℝ) → TangentSpace S (γ t)}
    (hT : ContinuousOn (fun t => (⟨γ t,T t⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) (Icc l q))
    (hJ : ∀ t ∈ Icc l q,
      HasCovariantDerivativeWithinAt C γ J (Icc l q) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc l q) t
        (-(R.val (γ t) (J t) (T t) (T t))))
    (hK : ∀ t ∈ Icc l q,
      HasCovariantDerivativeWithinAt C γ K (Icc l q) t (E t) ∧
      HasCovariantDerivativeWithinAt C γ E (Icc l q) t
        (-(R.val (γ t) (K t) (T t) (T t))))
    (hs : s ∈ Icc l q) (hinit : J s = K s ∧ D s = E s) :
    ∀ t ∈ Icc l q, J t = K t ∧ D t = E t := by
  let G : ℝ → Euclidean n →L[ℝ] Euclidean n := fun t =>
    D13Unified.Ch07.LinearSystemExistence.vectorAction
      (ParallelTransport.matrixAlong C b γ (Icc l q) t)
  let A := frameRadialOperator R b γ T
  have hG : ContinuousOn G (Icc l q) :=
    D13Unified.Ch07.LinearSystemExistence.continuous_vectorAction.comp_continuousOn
      (ParallelTransport.matrixAlong_continuousOn C b hc1 hc (uniqueDiffOn_Icc hlq) hUcurve)
  have hA : ContinuousOn A (Icc l q) := frameRadialOperator_continuousOn R b hc hUcurve hT
  let L := fun t => jacobiBlockOperator (G t) (A t)
  have hL : ContinuousOn L (Icc l q) := jacobiBlockOperator_continuousOn hG hA
  have hsys (F V : (t : ℝ) → TangentSpace S (γ t))
      (hFV : ∀ t ∈ Icc l q,
        HasCovariantDerivativeWithinAt C γ F (Icc l q) t (V t) ∧
        HasCovariantDerivativeWithinAt C γ V (Icc l q) t
          (-(R.val (γ t) (F t) (T t) (T t)))) :
      ∀ t ∈ Icc l q,
        HasDerivWithinAt (fun t => (coefficientsAlong b γ F t,coefficientsAlong b γ V t))
          (L t (coefficientsAlong b γ F t,coefficientsAlong b γ V t)) (Icc l q) t := by
    intro t ht
    have hF := covariant_coefficients_derivative C b hc1 hc (uniqueDiffOn_Icc hlq)
      ht (hUcurve ht) (hFV t ht).1
    have hV := covariant_coefficients_derivative C b hc1 hc (uniqueDiffOn_Icc hlq)
      ht (hUcurve ht) (hFV t ht).2
    have hRad := frameRadialOperator_apply R b (J := F) (T := T) (hUcurve ht)
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b γ F t (hUcurve ht)] at hRad
    have hRad' : A t (coefficientsAlong b γ F t) =
        (b.basis ⟨γ t,hUcurve ht⟩).equivFun (R.val (γ t) (F t) (T t) (T t)) := by
      simpa only [A,CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ t (hUcurve ht)] using hRad
    have hneg : (b.basis ⟨γ t,hUcurve ht⟩).equivFun
        (-(R.val (γ t) (F t) (T t) (T t))) =
        -((b.basis ⟨γ t,hUcurve ht⟩).equivFun (R.val (γ t) (F t) (T t) (T t))) := by
      apply eq_neg_iff_add_eq_zero.mpr
      rw [← map_add]
      have hn : -(R.val (γ t) (F t) (T t) (T t)) +
          R.val (γ t) (F t) (T t) (T t) = 0 := @neg_add_cancel (TangentSpace S (γ t)) _ _
      rw [hn,map_zero]
    simpa only [L,jacobiBlockOperator_apply,G,
      D13Unified.Ch07.LinearSystemExistence.vectorAction_apply,
      CurveCovariantDerivative.coefficientsAlong_of_mem b γ V t (hUcurve ht),
      hneg,hRad'] using hF.prodMk hV
  let Y := fun t => (coefficientsAlong b γ J t,coefficientsAlong b γ D t)
  let Z := fun t => (coefficientsAlong b γ K t,coefficientsAlong b γ E t)
  have hYd := hsys J D hJ
  have hZd := hsys K E hK
  obtain ⟨W,hW,hWs,hWd,_,huniq⟩ := ParallelTransport.linear_ode_on_compact
    hlq.le L hL hs (Y s)
  have hYs : Y s = Y s := rfl
  have hZs : Z s = Y s := by
    dsimp only [Z,Y]
    rw [ParallelTransport.coefficientsAlong_congr b hinit.1,
      ParallelTransport.coefficientsAlong_congr b hinit.2]
  have hYc : ContinuousOn Y (Icc l q) := fun t ht => (hYd t ht).continuousWithinAt
  have hZc : ContinuousOn Z (Icc l q) := fun t ht => (hZd t ht).continuousWithinAt
  intro t ht
  have heq := (huniq Y hYc hYs hYd ht).trans (huniq Z hZc hZs hZd ht).symm
  constructor
  · apply (b.basis ⟨γ t,hUcurve ht⟩).equivFun.injective
    simpa only [Y,Z,CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ t (hUcurve ht)]
      using congrArg Prod.fst heq
  · apply (b.basis ⟨γ t,hUcurve ht⟩).equivFun.injective
    simpa only [Y,Z,CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ t (hUcurve ht)]
      using congrArg Prod.snd heq

/-- Uniqueness holds on a compact segment even if its image requires many
frames. Every initial time, including a terminal endpoint, is allowed. -/
theorem jacobi_system_unique_on_piece (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) {γ : ℝ → M} {l q s : ℝ} (hlq : l ≤ q)
    (hc1 : CoordinateC1On S γ (Icc l q)) (hc : ContinuousOn γ (Icc l q))
    {T J D K E : (t : ℝ) → TangentSpace S (γ t)}
    (hT : ContinuousOn (fun t => (⟨γ t,T t⟩ : Bundle.TotalSpace (Euclidean n) (TangentSpace S))) (Icc l q))
    (hJ : ∀ t ∈ Icc l q,
      HasCovariantDerivativeWithinAt C γ J (Icc l q) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc l q) t
        (-(R.val (γ t) (J t) (T t) (T t))))
    (hK : ∀ t ∈ Icc l q,
      HasCovariantDerivativeWithinAt C γ K (Icc l q) t (E t) ∧
      HasCovariantDerivativeWithinAt C γ E (Icc l q) t
        (-(R.val (γ t) (K t) (T t) (T t))))
    (hs : s ∈ Icc l q) (hinit : J s = K s ∧ D s = E s) :
    ∀ t ∈ Icc l q, J t = K t ∧ D t = E t := by
  obtain ⟨m,node,hmono,hfirst,hlast,hframe⟩ :=
    ParallelTransport.exists_frame_subdivision (tangentBundle S) hlq hc
  have hsub (i : Fin m) : Icc (node i.castSucc) (node i.succ) ⊆ Icc l q := by
    intro t ht
    have hleft := hmono (Fin.zero_le i.castSucc)
    have hright := hmono (Fin.le_last i.succ)
    rw [hfirst] at hleft
    rw [hlast] at hright
    exact ⟨hleft.trans ht.1,ht.2.trans hright⟩
  have hprop : ∀ i : Fin m, ∀ s ∈ Icc (node i.castSucc) (node i.succ),
      (J s = K s ∧ D s = E s) →
      ∀ t ∈ Icc (node i.castSucc) (node i.succ), J t = K t ∧ D t = E t := by
    intro i s hs hinit t ht
    rcases lt_or_eq_of_le (hmono (Fin.castSucc_le_succ i)) with hpos | heq
    · obtain ⟨U,hU,b,hUcurve⟩ := hframe i
      exact frame_jacobi_system_unique C R b hpos
        (PiecewiseCurves.CoordinateC1On.mono hc1 (hsub i)) (hc.mono (hsub i)) hUcurve
        (hT.mono (hsub i))
        (fun x hx => ⟨ParallelTransport.covariantDerivative_mono (hJ x (hsub i hx)).1 (hsub i),
          ParallelTransport.covariantDerivative_mono (hJ x (hsub i hx)).2 (hsub i)⟩)
        (fun x hx => ⟨ParallelTransport.covariantDerivative_mono (hK x (hsub i hx)).1 (hsub i),
          ParallelTransport.covariantDerivative_mono (hK x (hsub i hx)).2 (hsub i)⟩)
        hs hinit t ht
    · have hts : t = s := by
        rw [heq,Icc_self] at hs ht
        exact ht.trans hs.symm
      exact hts.symm ▸ hinit
  simpa only [hfirst,hlast] using
    ParallelTransport.propagate_on_partition node hmono (fun t => J t = K t ∧ D t = E t)
      hprop (show s ∈ Icc (node 0) (node (Fin.last m)) by simpa only [hfirst,hlast] using hs)
      hinit


theorem jacobi_terminal_derivative_ne_zero (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : IsAffineGeodesicSegment C γ a c)
    {J D : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) t (D t) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) t
        (-(R.val (γ t) (J t) (segmentTangent S γ a c t)
          (segmentTangent S γ a c t))))
    (hJc : J c = 0) (hne : ∃ t ∈ Icc a c, J t ≠ 0) : D c ≠ 0 := by
  intro hDc
  have h0 : (0 : ℝ) ∈ Ioo (-(1:ℝ)) 1 := by norm_num
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ.1 h0
  have hc := FirstVariation.variation_continuousOn_slice hγ.1 h0
  have hT : ContinuousOn (fun t => (⟨γ t,segmentTangent S γ a c t⟩ :
      Bundle.TotalSpace (Euclidean n) (TangentSpace S))) (Icc a c) := by
    intro t ht
    exact covariantDerivative_continuousWithinAt C (hγ.2 t ht)
  have hzero : ∀ t ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ (fun _ => 0) (Icc a c) t 0 ∧
      HasCovariantDerivativeWithinAt C γ (fun _ => 0) (Icc a c) t
        (-(R.val (γ t) 0 (segmentTangent S γ a c t) (segmentTangent S γ a c t))) := by
    intro t ht
    have hz := CurveCovariantDerivative.derivative_const_smul C (hJ t ht).1 (0:ℝ)
    constructor
    · simpa only [zero_smul] using hz
    · have hzval : -(R.val (γ t) (0 : TangentSpace S (γ t))
          (segmentTangent S γ a c t) (segmentTangent S γ a c t)) = 0 := by
        simp only [map_zero,LinearMap.zero_apply]
        exact @neg_zero (TangentSpace S (γ t)) _
      rw [hzval]
      simpa only [zero_smul] using hz
  have heq := jacobi_system_unique_on_piece C R hac.le hc1 hc hT hJ hzero
    (show c ∈ Icc a c from ⟨hac.le,le_rfl⟩) ⟨hJc,hDc⟩
  obtain ⟨t,ht,hne⟩ := hne
  exact hne (heq t ht).1



/-- Pull back smooth vector-valued functions along an actual smooth closed
segment without imposing conditions outside its domain. -/
theorem vectorSmoothAt_curve_germ {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {γ : ℝ → M} {a b : ℝ}
    (hγ : P202.FirstVariationData.SmoothVariationOn S (fun z => γ z.2) 1 a b)
    {t : ℝ} (ht : t ∈ Icc a b) (f : M → F)
    (hf : VectorSmoothAt S.smoothStructure.val f (γ t)) :
    ∃ y : ℝ → F, ContDiffAt ℝ (⊤ : ℕ∞) y t ∧ f (γ t) = y t ∧
      (fun r => f (γ r)) =ᶠ[𝓝[Icc a b] t] y := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hγ.2 (0,t) ⟨h0,ht⟩
  obtain ⟨W,hW,hpW,G,hG,hrep⟩ := hf.2 e he hp
  let z : ℝ → Euclidean n := fun r => x (0,r)
  have hz : ContDiffAt ℝ (⊤ : ℕ∞) z t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have htend : Tendsto (fun r : ℝ => ((0 : ℝ),r)) (𝓝[Icc a b] t)
      (𝓝[Ioo (-1 : ℝ) 1 ×ˢ Icc a b] (0,t)) :=
    (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have hg := heqx.comp_tendsto htend
  have hzW : z t ∈ W := by
    change x (0,t) ∈ W
    rw [hxt]
    exact hpW
  refine ⟨G ∘ z,(hG.contDiffAt (hW.mem_nhds hzW)).comp t hz,?_,?_⟩
  · change f (γ t) = G (x (0,t))
    rw [hxt]
    exact hrep.eq_of_nhds.symm
  · filter_upwards [hg,hrep.comp_tendsto (hc t ht)] with r hr hFr
    exact hFr.symm.trans (congrArg G hr)

/-- A smooth closed base segment gives smooth ambient germs for the matrix
of any smooth tangent connection in a local frame. -/
theorem matrixAlong_smooth_germ (C : Connection (tangentBundle S))
    {U : Set M} {hU : IsOpen U} (b : LocalFrame (tangentBundle S) U hU)
    {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : P202.FirstVariationData.SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {t : ℝ} (ht : t ∈ Icc a c) (hpU : γ t ∈ U) :
    ∃ G : ℝ → Euclidean n →L[ℝ] Euclidean n,
      ContDiffAt ℝ (⊤ : ℕ∞) G t ∧
      D13Unified.Ch07.LinearSystemExistence.vectorAction
        (ParallelTransport.matrixAlong C b γ (Icc a c) t) = G t ∧
      (fun r => D13Unified.Ch07.LinearSystemExistence.vectorAction
        (ParallelTransport.matrixAlong C b γ (Icc a c) r)) =ᶠ[𝓝[Icc a c] t] G := by
  classical
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ h0
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hγ.2 (0,t) ⟨h0,ht⟩
  let k : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  have hk : γ t ∈ (tangentBundle S).baseSet k := by
    rw [(tangentRealization S).baseSet]
    exact hp
  let z : ℝ → Euclidean n := fun r => x (0,r)
  have hz : ContDiffAt ℝ (⊤ : ℕ∞) z t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have htend : Tendsto (fun r : ℝ => ((0 : ℝ),r)) (𝓝[Icc a c] t)
      (𝓝[Ioo (-1 : ℝ) 1 ×ˢ Icc a c] (0,t)) :=
    (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have hg : (fun r => (e (γ r)).val) =ᶠ[𝓝[Icc a c] t] z :=
    heqx.comp_tendsto htend
  let ω (i j : Fin n) : (p : M) → Module.Dual ℝ (TangentSpace S p) :=
    SmoothManifolds.SectionExtension.totalSection
      (fun p : U => connectionForm C b p i j)
  let coeff (i j : Fin n) (p : M) : Euclidean n :=
    (((cotangentBundle S).trivialization k) ⟨p,ω i j p⟩).2
  have hcoeff (i j : Fin n) : VectorSmoothAt S.smoothStructure.val (coeff i j) (γ t) :=
    SmoothManifolds.SectionExtension.coordinates_smoothAt (cotangentBundle S) k
      (by rw [(cotangentDual S).baseSet]; exact hk)
      (ConnectionForms.connectionForm_smooth (tangentBundle S) C hU b i j (γ t) hpU)
  choose y hy hyt heqy using fun i j => vectorSmoothAt_curve_germ hγ ht (coeff i j) (hcoeff i j)
  let A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun r i j =>
    ∑ l : Fin n, y i j r l * deriv z r l
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) (deriv z) t := hz.derivWithin (by simp)
  let G : ℝ → Euclidean n →L[ℝ] Euclidean n := fun r =>
    JacobiIVP.columnOperator (fun j i => A r i j)
  have hG : ContDiffAt ℝ (⊤ : ℕ∞) G t := by
    apply ContDiffAt.sum
    intro j _
    apply (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
      (ContinuousLinearMap.proj j)).contDiff.contDiffAt.comp t
    apply contDiffAt_pi.mpr
    intro i
    apply ContDiffAt.sum
    intro l _
    exact ((ContinuousLinearMap.proj (R := ℝ) l).contDiff.contDiffAt.comp t (hy i j)).mul ((ContinuousLinearMap.proj (R := ℝ) l).contDiff.contDiffAt.comp t hd)
  have hGval (r : ℝ) : D13Unified.Ch07.LinearSystemExistence.vectorAction (A r) = G r := by
    ext v i
    simp only [D13Unified.Ch07.LinearSystemExistence.vectorAction_apply,G,
      JacobiIVP.columnOperator_apply,Finset.sum_apply,Pi.smul_apply,smul_eq_mul,
      Matrix.mulVec, dotProduct,mul_comm]
  have hdeq : derivWithin (fun r => (e (γ r)).val) (Icc a c)
      =ᶠ[𝓝[Icc a c] t] deriv z := by
    apply hg.derivWithin.trans
    filter_upwards [self_mem_nhdsWithin,
      ((hz.of_le (m := 1) (by simp)).eventually (by norm_num)).filter_mono nhdsWithin_le_nhds] with r hr hzr
    exact (hzr.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin (uniqueDiffOn_Icc hac r hr)
  have hdeqt : derivWithin (fun r => (e (γ r)).val) (Icc a c) t = deriv z t := by
    rw [hg.derivWithin_eq hxt.symm]
    exact (hz.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hac t ht)
  have hformula (r : ℝ) (hr : r ∈ Icc a c) (hre : γ r ∈ e.source) (hrU : γ r ∈ U) :
      ParallelTransport.matrixAlong C b γ (Icc a c) r =
        fun i j => ∑ l : Fin n, coeff i j (γ r) l *
          derivWithin (fun r => (e (γ r)).val) (Icc a c) r l := by
    have hrk : γ r ∈ (tangentBundle S).baseSet k := by
      rw [(tangentRealization S).baseSet]
      exact hre
    have hv := PiecewiseCurves.withinVelocity_coordinates hc1 hc
      (uniqueDiffOn_Icc hac) hr e he hre
    funext i j
    rw [ParallelTransport.matrixAlong, dite_eq_left hrU]
    change connectionForm C b ⟨γ r,hrU⟩ i j
      (PiecewiseCurves.withinVelocity S γ (Icc a c) r) = _
    rw [ParallelTransport.linear_coordinates ((tangentBundle S).fiberCoordinates k (γ r) hrk)]
    apply Finset.sum_congr rfl
    intro l _
    congr 1
    · dsimp only [coeff]
      rw [(cotangentDual S).coordinates k (γ r) hrk (ω i j (γ r)) l]
      dsimp only [ω]
      rw [SmoothManifolds.SectionExtension.totalSection_of_mem _ _ hrU,
        SmoothVectorBundle.fiberCoordinates_symm_apply]
    · rw [SmoothVectorBundle.fiberCoordinates_apply,
        (tangentRealization S).coordinates k (γ r) hre]
      exact congrFun hv l
  have hagree (r : ℝ) (hr : r ∈ Icc a c) (hre : γ r ∈ e.source) (hrU : γ r ∈ U)
      (hdr : derivWithin (fun r => (e (γ r)).val) (Icc a c) r = deriv z r)
      (hyr : ∀ i j, coeff i j (γ r) = y i j r) :
      ParallelTransport.matrixAlong C b γ (Icc a c) r = A r := by
    rw [hformula r hr hre hrU,hdr]
    funext i j
    change (∑ l, coeff i j (γ r) l * deriv z r l) = _
    rw [hyr i j]
  refine ⟨G,hG,?_,?_⟩
  · rw [hagree t ht hp hpU hdeqt hyt]
    exact hGval t
  · filter_upwards [self_mem_nhdsWithin,
      (hc t ht).eventually (e.open_source.mem_nhds hp),
      (hc t ht).eventually (hU.mem_nhds hpU),hdeq,
      Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (heqy i))] with r hr hre hrU hdr hyr
    rw [hagree r hr hre hrU hdr hyr]
    exact hGval r



/-- In canonical tangent coordinates the radial curvature coefficient has a
smooth ambient germ along a smooth closed base segment. -/
theorem frameRadialOperator_canonical_smooth_germ (R : CurvatureTensor S)
    {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {t : ℝ} (ht : t ∈ Icc a c)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : γ t ∈ e.source) (z : ℝ → Euclidean n)
    (hz : ContDiffAt ℝ (⊤ : ℕ∞) z t)
    (hzt : z t = (e (γ t)).val)
    (heqz : (fun r => (e (γ r)).val) =ᶠ[𝓝[Icc a c] t] z) :
    let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
    ∃ A : ℝ → Euclidean n →L[ℝ] Euclidean n,
      ContDiffAt ℝ (⊤ : ℕ∞) A t ∧
      frameRadialOperator R b γ (segmentTangent S γ a c) t = A t ∧
      frameRadialOperator R b γ (segmentTangent S γ a c) =ᶠ[𝓝[Icc a c] t] A := by
  classical
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  let B := tangentBundle S
  have hi : γ t ∈ B.baseSet i := by
    rw [(tangentRealization S).baseSet]
    exact hp
  let f (j k l : Fin n) (p : M) : Euclidean n :=
    ((B.trivialization i) ⟨p,R.val p
      ((B.trivialization i).symm p (Pi.single j 1))
      ((B.trivialization i).symm p (Pi.single k 1))
      ((B.trivialization i).symm p (Pi.single l 1))⟩).2
  choose y hy hyt heqy using fun j k l => vectorSmoothAt_curve_germ hγ ht
    (f j k l) (CurvatureAlgebra.tensor_coordinates_smooth R i j k l (γ t) hi)
  let col (r : ℝ) (o : Fin n) : Euclidean n :=
    ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
      ((Pi.single o (1 : ℝ) : Euclidean n) j * (deriv z r k * deriv z r l)) • y j k l r
  let A : ℝ → Euclidean n →L[ℝ] Euclidean n := fun r => JacobiIVP.columnOperator (col r)
  have hd : ContDiffAt ℝ (⊤ : ℕ∞) (deriv z) t := hz.derivWithin (by simp)
  have hcol (o : Fin n) : ContDiffAt ℝ (⊤ : ℕ∞) (fun r => col r o) t := by
    apply ContDiffAt.sum
    intro j _
    apply ContDiffAt.sum
    intro k _
    apply ContDiffAt.sum
    intro l _
    exact (contDiffAt_const.mul (((ContinuousLinearMap.proj (R := ℝ) k).contDiff.contDiffAt.comp t hd).mul
      ((ContinuousLinearMap.proj (R := ℝ) l).contDiff.contDiffAt.comp t hd))).smul (hy j k l)
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A t := by
    apply ContDiffAt.sum
    intro o _
    exact (ContinuousLinearMap.smulRightL ℝ (Euclidean n) (Euclidean n)
      (ContinuousLinearMap.proj o)).contDiff.contDiffAt.comp t (hcol o)
  have hdeq : derivWithin (fun r => (e (γ r)).val) (Icc a c)
      =ᶠ[𝓝[Icc a c] t] deriv z := by
    apply heqz.derivWithin.trans
    filter_upwards [self_mem_nhdsWithin,
      ((hz.of_le (m := 1) (by simp)).eventually (by norm_num)).filter_mono
        nhdsWithin_le_nhds] with r hr hzr
    exact (hzr.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hac r hr)
  have hdeqt : derivWithin (fun r => (e (γ r)).val) (Icc a c) t = deriv z t := by
    rw [heqz.derivWithin_eq hzt.symm]
    exact (hz.differentiableAt (by simp)).hasDerivAt.hasDerivWithinAt.derivWithin
      (uniqueDiffOn_Icc hac t ht)
  have hformula (r : ℝ) (hr : r ∈ Icc a c) (hre : γ r ∈ e.source) :
      frameRadialOperator R b γ (segmentTangent S γ a c) r =
      JacobiIVP.columnOperator (fun o =>
        ∑ j : Fin n, ∑ k : Fin n, ∑ l : Fin n,
          ((Pi.single o (1 : ℝ) : Euclidean n) j *
            (derivWithin (fun r => (e (γ r)).val) (Icc a c) r k *
              derivWithin (fun r => (e (γ r)).val) (Icc a c) r l)) • f j k l (γ r)) := by
    have hri : γ r ∈ B.baseSet i := (tangentRealization S).baseSet i ▸ hre
    have hT : (B.fiberCoordinates i (γ r) hri) (segmentTangent S γ a c r) =
        derivWithin (fun r => (e (γ r)).val) (Icc a c) r := by
      rw [SmoothVectorBundle.fiberCoordinates_apply,
        (tangentRealization S).coordinates i (γ r) hre]
      exact FirstVariation.segmentVelocity_coordinates hγ (by norm_num) hac hr e he hre
    apply congrArg JacobiIVP.columnOperator
    funext o
    have hex := congrArg (B.fiberCoordinates i (γ r) hri)
      (JacobiIVP.trilinear_coordinates (B.fiberCoordinates i (γ r) hri)
        (R.val (γ r)) (frameFieldAlong b γ (fun _ => Pi.single o 1) r)
        (segmentTangent S γ a c r) (segmentTangent S γ a c r))
    have hF : B.fiberCoordinates i (γ r) hri
        (frameFieldAlong b γ (fun _ => Pi.single o 1) r) = Pi.single o 1 := by
      change (b.basis ⟨γ r,hri⟩).equivFun
        (frameFieldAlong b γ (fun _ => Pi.single o 1) r) = _
      rw [frameFieldAlong,dite_eq_left hri,LinearEquiv.apply_symm_apply]
    have hb (v : TangentSpace S (γ r)) : (b.basis ⟨γ r,hri⟩).equivFun v =
        (B.fiberCoordinates i (γ r) hri) v := by
      rw [FirstVariation.tangentFrame_coordinates e he (γ r) hre,
        SmoothVectorBundle.fiberCoordinates_apply,
        (tangentRealization S).coordinates i (γ r) hre]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ r hri,hb]
    simpa only [map_sum,map_smul,hF,hT,SmoothVectorBundle.fiberCoordinates_apply,
      SmoothVectorBundle.fiberCoordinates_symm_apply,f] using hex
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  refine ⟨A,hA,?_,?_⟩
  · rw [hformula t ht hp,hdeqt]
    apply congrArg JacobiIVP.columnOperator
    funext o
    dsimp only [A,col]
    congr 1
    funext j
    congr 1
    funext k
    congr 1
    funext l
    rw [hyt j k l]
  · filter_upwards [self_mem_nhdsWithin,(hc t ht).eventually (e.open_source.mem_nhds hp),
      hdeq,Filter.eventually_all.mpr (fun j => Filter.eventually_all.mpr (fun k =>
        Filter.eventually_all.mpr (heqy j k)))] with r hr hre hdr hyr
    rw [hformula r hr hre,hdr]
    apply congrArg JacobiIVP.columnOperator
    funext o
    dsimp only [A,col]
    congr 1
    funext j
    congr 1
    funext k
    congr 1
    funext l
    rw [hyr j k l]

/-- Local smooth coefficient extensions are constructed from the Jacobi
system itself; no regularity is required of off-segment representatives. -/
theorem segment_jacobi_coefficient_germ (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {J D : (t : ℝ) → TangentSpace S (γ t)}
    (hJD : ∀ r ∈ Icc a c,
      HasCovariantDerivativeWithinAt C γ J (Icc a c) r (D r) ∧
      HasCovariantDerivativeWithinAt C γ D (Icc a c) r
        (-(R.val (γ r) (J r) (segmentTangent S γ a c r)
          (segmentTangent S γ a c r))))
    {t : ℝ} (ht : t ∈ Icc a c)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : γ t ∈ e.source) (z : ℝ → Euclidean n)
    (hz : ContDiffAt ℝ (⊤ : ℕ∞) z t)
    (hzt : z t = (e (γ t)).val)
    (heqz : (fun r => (e (γ r)).val) =ᶠ[𝓝[Icc a c] t] z) :
    let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
    let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
    ∃ j : ℝ → Euclidean n, ContDiffAt ℝ (⊤ : ℕ∞) j t ∧
      j t = coefficientsAlong b γ J t ∧
      coefficientsAlong b γ J =ᶠ[𝓝[Icc a c] t] j := by
  classical
  let i : SmoothManifolds.BundleOperationsData.TangentIndex S := ⟨e,he⟩
  let b := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) i
  have hi : γ t ∈ (tangentBundle S).baseSet i :=
    (tangentRealization S).baseSet i ▸ hp
  obtain ⟨G,hG,hGt,heqG⟩ := matrixAlong_smooth_germ C b hac hγ ht hi
  obtain ⟨A,hA,hAt,heqA⟩ := frameRadialOperator_canonical_smooth_germ R hac hγ
    ht e he hp z hz hzt heqz
  let L := fun r => jacobiBlockOperator (G r) (A r)
  have hGfst : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun r => (G r).comp (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n))) t :=
    hG.clm_comp contDiffAt_const
  have hGsnd : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun r => (G r).comp (ContinuousLinearMap.snd ℝ (Euclidean n) (Euclidean n))) t :=
    hG.clm_comp contDiffAt_const
  have hAfst : ContDiffAt ℝ (⊤ : ℕ∞)
      (fun r => (A r).comp (ContinuousLinearMap.fst ℝ (Euclidean n) (Euclidean n))) t :=
    hA.clm_comp contDiffAt_const
  have hL : ContDiffAt ℝ (⊤ : ℕ∞) L t := by
    exact (ContinuousLinearMap.prodₗᵢ (𝕜 := ℝ) (E := Euclidean n × Euclidean n)
      (F := Euclidean n) (G := Euclidean n) ℝ).contDiff.contDiffAt.comp t
        ((contDiffAt_const.sub hGfst).prodMk (hAfst.neg.sub hGsnd))
  let Y := fun r => (coefficientsAlong b γ J r,coefficientsAlong b γ D r)
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  have hc1 := FirstVariation.variation_coordinateC1On_slice hγ h0
  have hODE : ∀ᶠ r in 𝓝[Icc a c] t,
      HasDerivWithinAt Y (L r (Y r)) (Icc a c) r := by
    filter_upwards [self_mem_nhdsWithin,(hc t ht).eventually (e.open_source.mem_nhds hp),
      heqG,heqA] with r hr hre hrG hrA
    have hri : γ r ∈ (tangentBundle S).baseSet i :=
      (tangentRealization S).baseSet i ▸ hre
    have hJ := covariant_coefficients_derivative C b hc1 hc (uniqueDiffOn_Icc hac)
      hr hri (hJD r hr).1
    have hD := covariant_coefficients_derivative C b hc1 hc (uniqueDiffOn_Icc hac)
      hr hri (hJD r hr).2
    have hRad := frameRadialOperator_apply R b (J := J)
      (T := segmentTangent S γ a c) hri
    have hRad' : A r (coefficientsAlong b γ J r) =
        (b.basis ⟨γ r,hri⟩).equivFun
          (R.val (γ r) (J r) (segmentTangent S γ a c r) (segmentTangent S γ a c r)) := by
      rw [← hrA]
      simpa only [CurveCovariantDerivative.coefficientsAlong_of_mem b γ _ r hri] using hRad
    have hneg : (b.basis ⟨γ r,hri⟩).equivFun
        (-(R.val (γ r) (J r) (segmentTangent S γ a c r) (segmentTangent S γ a c r))) =
        -((b.basis ⟨γ r,hri⟩).equivFun
          (R.val (γ r) (J r) (segmentTangent S γ a c r) (segmentTangent S γ a c r))) := by
      apply eq_neg_iff_add_eq_zero.mpr
      rw [← map_add]
      have hn : -(R.val (γ r) (J r) (segmentTangent S γ a c r) (segmentTangent S γ a c r)) +
          R.val (γ r) (J r) (segmentTangent S γ a c r) (segmentTangent S γ a c r) = 0 :=
        @neg_add_cancel (TangentSpace S (γ r)) _ _
      rw [hn,map_zero]
    simpa only [Y,L,jacobiBlockOperator_apply,← hrG,
      D13Unified.Ch07.LinearSystemExistence.vectorAction_apply,
      CurveCovariantDerivative.coefficientsAlong_of_mem b γ D r hri,
      hneg,hRad'] using hJ.prodMk hD
  obtain ⟨W,hW,hWt,heqW⟩ := linear_ode_smooth_extension hac ht hL hODE
  exact ⟨fun r => (W r).1,hW.fst,congrArg Prod.fst hWt,
    heqW.fun_comp Prod.fst⟩

/-- Every actual closed-segment Jacobi field is smooth up to both endpoints.
Its representatives outside the closed segment are unrestricted. -/
theorem segment_jacobi_smooth (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) {γ : ℝ → M} {a c : ℝ} (hac : a < c)
    (hγ : SmoothVariationOn S (fun z => γ z.2) 1 a c)
    {J : (t : ℝ) → TangentSpace S (γ t)}
    (hJ : IsSegmentJacobiField C R γ a c J) : SmoothFieldOn γ J (Icc a c) := by
  obtain ⟨D,hD⟩ := hJ
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
  have hc := FirstVariation.variation_continuousOn_slice hγ h0
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heqx⟩ := hγ.2 (0,t) ⟨h0,ht⟩
  let z : ℝ → Euclidean n := fun r => x (0,r)
  have hz : ContDiffAt ℝ (⊤ : ℕ∞) z t :=
    hx.comp t (contDiffAt_const.prodMk contDiffAt_id)
  have htend : Tendsto (fun r : ℝ => ((0 : ℝ),r)) (𝓝[Icc a c] t)
      (𝓝[Ioo (-1 : ℝ) 1 ×ˢ Icc a c] (0,t)) :=
    (continuous_const.prodMk continuous_id).continuousAt.continuousWithinAt.tendsto_nhdsWithin
      (fun _ hr => ⟨h0,hr⟩)
  have heqz : (fun r => (e (γ r)).val) =ᶠ[𝓝[Icc a c] t] z :=
    heqx.comp_tendsto htend
  obtain ⟨j,hj,hjt,heqj⟩ := segment_jacobi_coefficient_germ C R hac hγ hD ht
    e he hp z hz hxt heqz
  obtain ⟨w,hw,hwt,heqw⟩ := tangent_chart_germ_of_coefficients hc ht e he hp z j
    hz hj hxt heqz hjt heqj
  exact ⟨e,he,hp,w,hw,hwt,heqw⟩

/-- A length-minimizing affine geodesic segment has no conjugate point
strictly between its endpoints. The terminal endpoint is deliberately excluded.
The proof includes constant segments and zero-dimensional manifolds. -/
theorem no_interior_conjugate :
    P202Specs.Geometry.NoInteriorConjugate.no_interior_conjugateType.{u} := by
  intro n M _ S g C hC R hR a b γ hab hγ hmin c hac hcb
  rintro ⟨J,hJac,hJa,hJc,hne⟩
  obtain ⟨D,hD⟩ := hJac
  have hsmall : IsAffineGeodesicSegment C γ a c :=
    SecondVariation.affineGeodesicSegment_restrict C hγ le_rfl hcb.le hac
  have hJs : SmoothFieldOn γ J (Icc a c) :=
    segment_jacobi_smooth C R hac hsmall.1 ⟨D,hD⟩
  have hDc : D c ≠ 0 :=
    jacobi_terminal_derivative_ne_zero C R hac hsmall hD hJc hne
  exact not_minimizing_of_smooth_jacobi g C hC R hR γ hγ hac hcb hJs
    hD hJa hJc hDc hmin

end P202.Geometry.NoInteriorConjugate
