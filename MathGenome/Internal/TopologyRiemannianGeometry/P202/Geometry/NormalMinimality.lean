import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.NormalMinimality
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.GaussLemma
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.LengthDistance
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.Algebra.Module.FiniteDimensionBilinear
import Mathlib.MeasureTheory.Integral.DivergenceTheorem

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 100000

namespace P202.Geometry.NormalMinimality
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.MaximalFlowData
  P202.MetricData P202.ConnectionData P202.CurveData P202.CurveConnectionData
  P202.GeodesicData P202.LeviCivitaData P202.ExponentialData P202.DistanceData
  P202.NormalMinimalityData
open Set Filter MeasureTheory
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

abbrev RadialParametrization := @P202.NormalMinimalityData.RadialParametrization

/-- Cauchy–Schwarz in the original metric fiber. No auxiliary norm or
inner-product instance is imposed on its abstract tangent-space type. -/
theorem pairing_sq_le (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) :
    pairing g p v w ^ 2 ≤ pairing g p v v * pairing g p w w := by
  have h : ∀ t : ℝ, 0 ≤ pairing g p v v * (t * t) +
      (2 * pairing g p v w) * t + pairing g p w w := by
    intro t
    have hh := SmoothMetrics.pairing_self_nonneg g p (t • v + w)
    simp only [pairing, map_add, LinearMap.add_apply, map_smul,
      LinearMap.smul_apply, smul_eq_mul] at hh ⊢
    rw [g.symmetric p w v] at hh
    nlinarith only [hh]
  have hd := discrim_le_zero h
  dsimp [discrim] at hd
  nlinarith only [hd]

/-- The absolute metric pairing is bounded by the two metric norms. -/
theorem abs_pairing_le (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) :
    |pairing g p v w| ≤ tangentNorm g p v * tangentNorm g p w := by
  have hs := pairing_sq_le g p v w
  rw [← SmoothMetrics.tangentNorm_sq g p v,
    ← SmoothMetrics.tangentNorm_sq g p w] at hs
  have hn := mul_nonneg (SmoothMetrics.tangentNorm_nonneg g p v)
    (SmoothMetrics.tangentNorm_nonneg g p w)
  nlinarith [sq_abs (pairing g p v w)]

/-- Equality in the signed radial Cauchy–Schwarz bound forces a
nonnegative multiple of the radial vector, allowing zero speed. -/
theorem eq_smul_of_pairing_eq_norm_mul (g : RiemannianMetric S) (p : M)
    (v w : TangentSpace S p) (hv : v ≠ 0)
    (heq : pairing g p v w = tangentNorm g p v * tangentNorm g p w) :
    w = (tangentNorm g p w / tangentNorm g p v) • v := by
  let r := tangentNorm g p v
  let s := tangentNorm g p w
  have hr : r ≠ 0 := fun h => hv ((SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp h)
  let B : LinearMap.BilinForm ℝ (TangentSpace S p) := g.form p
  have hzero : pairing g p (r • w + (-s) • v) (r • w + (-s) • v) = 0 := by
    change B (r • w + (-s) • v) (r • w + (-s) • v) = 0
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
    rw [show B w v = B v w from g.symmetric p w v]
    change r * (r * pairing g p w w + -s * pairing g p v w) +
      -s * (r * pairing g p v w + -s * pairing g p v v) = 0
    rw [heq, ← SmoothMetrics.tangentNorm_sq g p v,
      ← SmoothMetrics.tangentNorm_sq g p w]
    dsimp only [r, s]
    ring
  have hz : r • w + (-s) • v = 0 := by
    by_contra hne
    exact (ne_of_gt (g.positive p _ hne)) hzero
  have hscale : r • w = s • v := by
    have hh := congrArg (fun z : TangentSpace S p => z + s • v) hz
    simpa only [add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero, zero_add] using hh
  have h := congrArg (fun z : TangentSpace S p => r⁻¹ • z) hscale
  simpa only [smul_smul, inv_mul_cancel₀ hr, one_smul, div_eq_inv_mul] using h


/-- A nonsmooth nonnegative radius can be controlled by differentiating its
square and regularizing with a positive constant. Zeros are not exceptions. -/
theorem radius_displacement_le_integral {a b : ℝ} (hab : a ≤ b)
    (r h s : ℝ → ℝ) (K : Finset ℝ)
    (hc : ContinuousOn r (Icc a b))
    (hr : ∀ t ∈ Icc a b, 0 ≤ r t)
    (hs : ∀ t ∈ Icc a b, 0 ≤ s t)
    (hsi : IntervalIntegrable s volume a b)
    (hd : ∀ t ∈ Icc a b, t ∉ K →
      HasDerivAt (fun u => r u ^ 2) (2 * h t) t ∧ |h t| ≤ r t * s t) :
    |r b - r a| ≤ ∫ t in a..b, s t := by
  have hε (ε : ℝ) (hε : 0 < ε) :
      |Real.sqrt (r b ^ 2 + ε) - Real.sqrt (r a ^ 2 + ε)| ≤ ∫ t in a..b, s t := by
    let f : ℝ → ℝ := fun t => Real.sqrt (r t ^ 2 + ε)
    have hfc : ContinuousOn f (Icc a b) := Real.continuous_sqrt.comp_continuousOn
      ((hc.pow 2).add continuousOn_const)
    have hfd (t : ℝ) (ht : t ∈ Icc a b) (htK : t ∉ K) :
        HasDerivAt f ((2 * h t) / (2 * f t)) t := by
      exact ((hd t ht htK).1.add_const ε).sqrt (by positivity)
    have hbound (t : ℝ) (ht : t ∈ Icc a b) (htK : t ∉ K) :
        ‖deriv f t‖ ≤ s t := by
      rw [(hfd t ht htK).deriv, Real.norm_eq_abs, abs_div, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
        abs_of_nonneg (mul_nonneg (by norm_num) (Real.sqrt_nonneg _))]
      have hpos : 0 < f t := Real.sqrt_pos.2 (by positivity)
      have hrf : r t ≤ f t := by
        have he := Real.sq_sqrt (show 0 ≤ r t ^ 2 + ε by positivity)
        have hfnonneg : 0 ≤ f t := Real.sqrt_nonneg _
        dsimp only [f] at hfnonneg ⊢
        nlinarith
      apply (div_le_iff₀ (mul_pos (by norm_num) hpos)).mpr
      nlinarith [mul_le_mul_of_nonneg_right hrf (hs t ht), (hd t ht htK).2]
    have hae : ∀ᵐ t ∂volume, t ∈ Ioc a b → ‖deriv f t‖ ≤ s t := by
      filter_upwards [K.finite_toSet.countable.ae_notMem volume] with t ht hI
      exact hbound t (Ioc_subset_Icc_self hI) ht
    have hfi : IntervalIntegrable (deriv f) volume a b := by
      apply hsi.mono_fun' (aestronglyMeasurable_deriv f _)
      rw [uIoc_of_le hab, Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
      exact hae
    have hFTC : (∫ t in a..b, deriv f t) = f b - f a := by
      apply integral_eq_of_hasDerivAt_off_countable_of_le f (deriv f) hab
        K.finite_toSet.countable hfc
      · intro t ht
        exact (hfd t (Ioo_subset_Icc_self ht.1) ht.2).differentiableAt.hasDerivAt
      · exact hfi
    calc
      _ = ‖∫ t in a..b, deriv f t‖ := by rw [hFTC]; rfl
      _ ≤ _ := intervalIntegral.norm_integral_le_of_norm_le hab hae hsi
  have hlim : Tendsto
      (fun ε : ℝ => |Real.sqrt (r b ^ 2 + ε) - Real.sqrt (r a ^ 2 + ε)|)
      (𝓝[>] 0) (𝓝 |r b - r a|) := by
    have H : Continuous (fun ε : ℝ =>
        |Real.sqrt (r b ^ 2 + ε) - Real.sqrt (r a ^ 2 + ε)|) := by fun_prop
    convert H.continuousAt.tendsto.mono_left nhdsWithin_le_nhds using 1;
      simp only [add_zero, Real.sqrt_sq (hr a ⟨le_rfl, hab⟩),
        Real.sqrt_sq (hr b ⟨hab, le_rfl⟩)]
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin] with ε hpos
  exact hε ε hpos

/-- Choose a strictly smaller positive radius, retaining the larger normal
chart around its entire closed fiber ball. -/
theorem normal_radius_exists :
    P202Specs.Geometry.NormalMinimality.normal_radius_existsType.{u} := by
  intro n M _ S g C F hF p
  obtain ⟨E, hE⟩ := ExponentialNormalCoordinates.orthonormal_coordinates_exist g p
  obtain ⟨R, d, hd⟩ :=
    ExponentialNormalCoordinates.normal_chart_exists_at C F hF g p E hE
  exact ⟨E, R / 2, R, d, hE, by linarith [hd.1], by linarith [hd.1], hd⟩

/-- Every vector in the normal ball is in the actual exponential domain,
and its image has the specified chart coordinates. -/
theorem normal_chart_exp (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n)
    (R : ℝ) (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R) :
    (⟨p, v⟩ : Phase S) ∈ exponentialDomain F ∧
      fiberExponential F p v ∈ d.source ∧ (d (fiberExponential F p v)).val = E v := by
  let x : ModelSpace n .euclidean := ⟨E v, mem_univ _⟩
  have hxnorm : tangentNorm g p (E.symm x.val) < R := by
    simpa only [x, LinearEquiv.symm_apply_apply] using hv
  have hx : x ∈ d.target := by rw [hd.2.2.2.2.1]; exact hxnorm
  have heq : fiberExponential F p v = d.symm x := by
    simpa only [x, LinearEquiv.symm_apply_apply] using (hd.2.2.2.2.2 x hxnorm).2
  refine ⟨by simpa only [x, LinearEquiv.symm_apply_apply] using
    (hd.2.2.2.2.2 x hxnorm).1, ?_, ?_⟩
  · rw [heq]; exact d.map_target hx
  · rw [heq, d.right_inv hx]

/-- The chart is injective on the original tangent ball, in particular at 0. -/
theorem normal_chart_exp_injective (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    {v w : TangentSpace S p} (hv : tangentNorm g p v < R)
    (hw : tangentNorm g p w < R)
    (heq : fiberExponential F p v = fiberExponential F p w) : v = w := by
  apply E.injective
  rw [← (normal_chart_exp g F p E R d hd v hv).2.2,
    ← (normal_chart_exp g F p E R d hd w hw).2.2, heq]

/-- The fixed fiber metric in arbitrary linear coordinates is a continuous
bilinear map. This does not install a norm on the abstract tangent fiber. -/
noncomputable def coordinatePairing (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Euclidean n →L[ℝ] Euclidean n →L[ℝ] ℝ :=
  let B : LinearMap.BilinForm ℝ (TangentSpace S p) := g.form p
  (B.compl₁₂ E.symm.toLinearMap E.symm.toLinearMap).toContinuousBilinearMap

@[simp] theorem coordinatePairing_apply (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (x y : Euclidean n) :
    coordinatePairing g p E x y = pairing g p (E.symm x) (E.symm y) := rfl

/-- Continuity of the fiber norm holds in every linear coordinate system,
without the orthonormality restriction needed for its sum-of-squares formula. -/
theorem coordinateNorm_continuous (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    Continuous (fun x : Euclidean n => tangentNorm g p (E.symm x)) := by
  change Continuous (fun x => Real.sqrt (coordinatePairing g p E x x))
  exact Real.continuous_sqrt.comp ((coordinatePairing g p E).continuous.clm_apply continuous_id)

/-- Differentiating the squared radial coordinate requires no division by
radius, and is consequently valid at the center as well. -/
theorem coordinateNorm_sq_hasDerivAt (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) {x : ℝ → Euclidean n}
    {t : ℝ} {z : Euclidean n} (hx : HasDerivAt x z t) :
    HasDerivAt (fun u => tangentNorm g p (E.symm (x u)) ^ 2)
      (2 * pairing g p (E.symm (x t)) (E.symm z)) t := by
  simp_rw [SmoothMetrics.tangentNorm_sq]
  have h := ContinuousLinearMap.hasDerivAt_of_bilinear
    (B := coordinatePairing g p E) (fun _ => hx) (fun _ => hx)
  simp only [coordinatePairing_apply] at h
  rw [show pairing g p (E.symm z) (E.symm (x t)) =
    pairing g p (E.symm (x t)) (E.symm z) from g.symmetric p _ _, ← two_mul] at h
  exact h

/-- In normal coordinates the actual fiber differential has coordinate
matrix E. This follows by differentiating the inverse law on an open ball. -/
theorem normal_chart_fiberDifferential (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    (e : ModelChart n .euclidean M) (he : e ∈ S.smoothStructure.val)
    (hp : p ∈ e.source) (w : TangentSpace S p) :
    (tangentStructure S).fiberCoordinates.equiv d hd.2.1
      (fiberExponential F p v) (normal_chart_exp g F p E R d hd v hv).2.1
      (P202.GaussData.fiberDifferential F p v e he hp d hd.2.1
        (normal_chart_exp g F p E R d hd v hv).2.1 w) = E w := by
  let K := (tangentStructure S).fiberCoordinates.equiv e he p hp
  let D := (tangentStructure S).fiberCoordinates.equiv d hd.2.1
    (fiberExponential F p v) (normal_chart_exp g F p E R d hd v hv).2.1
  let A := (K.symm.trans E).toContinuousLinearEquiv
  let f : Euclidean n → Euclidean n := fun x =>
    (d (fiberExponential F p (K.symm x))).val
  have hnear : ∀ᶠ x in 𝓝 (K v), tangentNorm g p (K.symm x) < R := by
    apply (coordinateNorm_continuous g p K).continuousAt.eventually_lt_const
    simpa only [LinearEquiv.symm_apply_apply] using hv
  have heq : f =ᶠ[𝓝 (K v)] A := by
    filter_upwards [hnear] with x hx
    exact (normal_chart_exp g F p E R d hd (K.symm x) hx).2.2
  have hf : HasFDerivAt f A.toContinuousLinearMap (K v) :=
    A.hasFDerivAt.congr_of_eventuallyEq heq
  change D (D.symm (fderiv ℝ f (K v) (K w))) = E w
  rw [LinearEquiv.apply_symm_apply, hf.fderiv]
  exact congrArg E (K.symm_apply_apply w)

/-- The radial pairing of a coordinate velocity is bounded by the speed
of the actual tangent vector. This is the pointwise Gauss comparison. -/
theorem normal_chart_radial_pairing_le (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    (u : TangentSpace S (fiberExponential F p v)) :
    |pairing g p v (E.symm ((tangentStructure S).fiberCoordinates.equiv
      d hd.2.1 (fiberExponential F p v)
        (normal_chart_exp g F p E R d hd v hv).2.1 u))| ≤
      tangentNorm g p v * tangentNorm g (fiberExponential F p v) u := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let hq := (normal_chart_exp g F p E R d hd v hv).2.1
  let D := (tangentStructure S).fiberCoordinates.equiv d hd.2.1
    (fiberExponential F p v) hq
  let L := P202.GaussData.fiberDifferential F p v e he hp d hd.2.1 hq
  let w := E.symm (D u)
  have hLu : L w = u := by
    apply D.injective
    rw [normal_chart_fiberDifferential g F p E R d hd v hv e he hp w]
    exact E.apply_symm_apply _
  have hgauss := GaussLemma.gauss_lemma S g C hC F hF p v
    (normal_chart_exp g F p E R d hd v hv).1 e he hp d hd.2.1 hq w
  have hrad := GaussLemma.radial_length S g C hC F hF p v
    (normal_chart_exp g F p E R d hd v hv).1 e he hp d hd.2.1 hq
  have hbound := abs_pairing_le g (fiberExponential F p v) (L v) (L w)
  rw [hgauss, hrad, hLu] at hbound
  exact hbound

/-- The inverse normal coordinate belongs to the actual fiber ball and
exponentiates back to the original point. -/
theorem normal_chart_inverse (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (q : M) (hq : q ∈ d.source) :
    tangentNorm g p (E.symm (d q).val) < R ∧
      fiberExponential F p (E.symm (d q).val) = q := by
  have hx := d.map_source hq
  have hv : tangentNorm g p (E.symm (d q).val) < R := by
    rwa [hd.2.2.2.2.1] at hx
  exact ⟨hv, ((hd.2.2.2.2.2 (d q) hv).2).trans (d.left_inv hq)⟩

/-- The Gauss bound at an arbitrary point in the normal chart, expressed
using the original point's tangent fiber. -/
theorem normal_chart_radial_pairing_at (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (q : M) (hq : q ∈ d.source) (u : TangentSpace S q) :
    |pairing g p (E.symm (d q).val)
      (E.symm ((tangentStructure S).fiberCoordinates.equiv d hd.2.1 q hq u))| ≤
      tangentNorm g p (E.symm (d q).val) * tangentNorm g q u := by
  obtain ⟨hv, hexp⟩ := normal_chart_inverse g F p E R d hd q hq
  generalize hw : E.symm (d q).val = w at hv hexp ⊢
  subst q
  exact normal_chart_radial_pairing_le g C hC F hF p E R d hd w hv u

/-- Local radial comparison on the entire compact curve interval. The proof
uses squared radius at all non-corner times, including visits to the center. -/
theorem normal_chart_radius_displacement_le_length (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (hsource : ∀ t ∈ Icc a b, c t ∈ d.source) :
    |tangentNorm g p (E.symm (d (c b)).val) -
      tangentNorm g p (E.symm (d (c a)).val)| ≤ length g c := by
  classical
  let x : ℝ → Euclidean n := fun t => (d (c t)).val
  let r : ℝ → ℝ := fun t => tangentNorm g p (E.symm (x t))
  let h : ℝ → ℝ := fun t => if hq : c t ∈ d.source then
    pairing g p (E.symm (x t)) (E.symm
      ((tangentStructure S).fiberCoordinates.equiv d hd.2.1 (c t) hq (velocity S c t)))
    else 0
  have hxc : ContinuousOn x (Icc a b) :=
    (continuous_subtype_val.comp_continuousOn d.continuousOn).comp c.continuousOn hsource
  have hrc : ContinuousOn r (Icc a b) :=
    (coordinateNorm_continuous g p E).comp_continuousOn hxc
  apply radius_displacement_le_integral c.ordered r h (speed g c) (breakpoints c)
    hrc (fun t _ => SmoothMetrics.tangentNorm_nonneg g p _)
    (fun t _ => SmoothMetrics.tangentNorm_nonneg g (c t) _)
    (PiecewiseCurves.speed_integrable g c)
  intro t ht htK
  have hxt := PiecewiseCurves.hasVelocityAt_coordinates
    (PiecewiseCurves.hasVelocityAt_off_breakpoints c ht htK) d hd.2.1 (hsource t ht)
  have hsq := coordinateNorm_sq_hasDerivAt g p E hxt
  refine ⟨?_, ?_⟩
  · simpa only [h, dite_eq_left (hsource t ht)] using hsq
  · simpa only [h, x, r, speed, dite_eq_left (hsource t ht)] using
      normal_chart_radial_pairing_at g C hC F hF p E R d hd (c t) (hsource t ht)
        (velocity S c t)

/-- A curve from the center which stays in the chart has length at least
the terminal radius. No nonzero-speed hypothesis is used. -/
theorem normal_chart_comparison (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (h0 : c a = p) (h1 : c b = fiberExponential F p v)
    (hsource : ∀ t ∈ Icc a b, c t ∈ d.source) :
    tangentNorm g p v ≤ length g c := by
  have h := normal_chart_radius_displacement_le_length g C hC F hF p E R d hd c hsource
  rw [h0, h1, hd.2.2.2.1, (normal_chart_exp g F p E R d hd v hv).2.2,
    map_zero, LinearEquiv.symm_apply_apply, SmoothMetrics.tangentNorm_zero,
    sub_zero, abs_of_nonneg (SmoothMetrics.tangentNorm_nonneg g p v)] at h
  exact h

/-- The whole unit time interval lies in the original maximal lifespan. -/
theorem radial_interval (C : Connection (tangentBundle S))
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : TangentSpace S p)
    (hv : (⟨p, v⟩ : Phase S) ∈ exponentialDomain F) :
    Icc (0 : ℝ) 1 ⊆ (F.interval ⟨p, v⟩).carrier :=
  (F.interval ⟨p, v⟩).ordConnected.out (hF ⟨p, v⟩).1 hv

/-- Radial contraction does not leave the normal fiber ball. -/
theorem radial_norm_lt (g : RiemannianMetric S) (p : M)
    (v : TangentSpace S p) {R t : ℝ} (hv : tangentNorm g p v < R)
    (ht : t ∈ Icc (0 : ℝ) 1) : tangentNorm g p (t • v) < R := by
  rw [SmoothMetrics.tangentNorm_smul, abs_of_nonneg ht.1]
  exact (mul_le_of_le_one_left (SmoothMetrics.tangentNorm_nonneg g p v) ht.2).trans_lt hv

/-- The maximal geodesic position is a genuine member of the accepted compact
piecewise C¹ curve class. A single piece suffices, using its normal chart. -/
noncomputable def radialCurve (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R) : PiecewiseC1Curve S 0 1 where
  ordered := zero_le_one
  toFun := fun t => (F.curve ⟨p, v⟩ t).1
  continuousOn := by
    intro t ht
    have hvel := ((hF ⟨p, v⟩).2.2.1 t
      (radial_interval C F hF p v (normal_chart_exp g F p E R d hd v hv).1 ht)).1
    exact hvel.1.mono (subset_univ _)
  pieces := 1
  node := fun i => (i.val : ℝ)
  monotone_node := fun i j hij => by
    exact Nat.cast_le.mpr (show i.val ≤ j.val from hij)
  first_node := by norm_num
  last_node := by norm_num
  regular := by
    intro i t ht
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Fin.val_castSucc, Fin.val_zero, Fin.val_succ, zero_add, Nat.cast_zero, Nat.cast_one] at ht ⊢
    have hrad (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        fiberExponential F p (s • v) = (F.curve ⟨p, v⟩ s).1 :=
      (ExponentialNormalCoordinates.radial_identity_at C F hF p v s
        (radial_interval C F hF p v (normal_chart_exp g F p E R d hd v hv).1 hs)).2
    have hcoords (s : ℝ) (hs : s ∈ Icc (0 : ℝ) 1) :
        (F.curve ⟨p, v⟩ s).1 ∈ d.source ∧
        (d (F.curve ⟨p, v⟩ s).1).val = s • E v := by
      have h := (normal_chart_exp g F p E R d hd (s • v) (radial_norm_lt g p v hv hs)).2
      rw [hrad s hs, E.map_smul] at h
      exact h
    refine ⟨d, hd.2.1, (hcoords t ht).1, fun s => s • E v,
      ((contDiff_id.smul contDiff_const).contDiffAt), (hcoords t ht).2.symm, ?_⟩
    exact Filter.mem_of_superset self_mem_nhdsWithin (fun s hs => (hcoords s hs).2)

/-- Constant speed is evaluated using the actual tangent lift, with velocity
uniqueness providing the bridge to the curve class's intrinsic velocity. -/
theorem radialCurve_speed (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    speed g (radialCurve g C F hF p E R d hd v hv) t = tangentNorm g p v := by
  have htI := radial_interval C F hF p v (normal_chart_exp g F p E R d hd v hv).1 ht
  have hvel := ((hF ⟨p, v⟩).2.2.1 t htI).1
  have hvel' : HasVelocityAt S (fun s => (F.curve ⟨p, v⟩ s).1) t
      (F.curve ⟨p, v⟩ t).2 := by
    simpa only [HasVelocityAt, HasVelocityWithinAt, continuousWithinAt_univ,
      hasDerivWithinAt_univ] using hvel
  change tangentNorm g (F.curve ⟨p, v⟩ t).1
    (velocity S (fun s => (F.curve ⟨p, v⟩ s).1) t) = _
  rw [PiecewiseCurves.velocity_eq hvel']
  have h := GeodesicIVP.speed_is_constant g C hC (F.interval ⟨p, v⟩)
    (F.curve ⟨p, v⟩) (hF ⟨p, v⟩).2.2.1 htI (hF ⟨p, v⟩).1
  rwa [(hF ⟨p, v⟩).2.1] at h

theorem radial_segment_exists :
    P202Specs.Geometry.NormalMinimality.radial_segment_existsType.{u} := by
  intro n M _ S g C hC F hF p E R d hd v hv
  let γ := radialCurve g C F hF p E R d hd v hv
  have hI := radial_interval C F hF p v (normal_chart_exp g F p E R d hd v hv).1
  refine ⟨γ, congrArg Sigma.fst (hF ⟨p, v⟩).2.1, rfl, ?_, fun _ _ => rfl,
    fun t ht => (hF ⟨p, v⟩).2.2.1 t (hI ht), ?_⟩
  · intro t ht
    exact (ExponentialNormalCoordinates.radial_identity_at C F hF p v t (hI ht)).2.symm
  · change (∫ t in (0 : ℝ)..1, speed g γ t) = _
    calc
      _ = ∫ _t in (0 : ℝ)..1, tangentNorm g p v := by
        apply intervalIntegral.integral_congr
        intro t ht
        exact radialCurve_speed g C hC F hF p E R d hd v hv t (by simpa using ht)
      _ = _ := by simp

/-- The continuous radius parameter gives exactly the radial image, including
when v = 0 or the original parameter interval degenerates. -/
theorem radialParametrization_image (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (v : TangentSpace S p)
    {a b : ℝ} (hab : a ≤ b) {γ : ℝ → M}
    (hγ : RadialParametrization g F p v a b γ) :
    γ '' Icc a b = (fun t : ℝ => fiberExponential F p (t • v)) '' Icc 0 1 := by
  obtain ⟨ρ, hρ, hmono, h0, h1, heq⟩ := hγ
  by_cases hv : v = 0
  · subst v
    have hconst (t : ℝ) (ht : t ∈ Icc a b) : γ t = fiberExponential F p 0 := by
      simpa only [smul_zero] using heq t ht
    apply Set.ext
    intro q
    constructor
    · rintro ⟨t, ht, rfl⟩
      exact ⟨0, ⟨le_rfl, zero_le_one⟩, by simpa only [smul_zero] using (hconst t ht).symm⟩
    · rintro ⟨t, ht, rfl⟩
      exact ⟨a, ⟨le_rfl, hab⟩, by simpa only [smul_zero] using hconst a ⟨le_rfl, hab⟩⟩
  · have hn : 0 < tangentNorm g p v :=
      lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p v)
        (fun h => hv ((SmoothMetrics.tangentNorm_eq_zero_iff g p v).mp h.symm))
    apply Set.ext
    intro q
    constructor
    · rintro ⟨t, ht, rfl⟩
      have hlow : 0 ≤ ρ t := by rw [← h0]; exact hmono ⟨le_rfl, hab⟩ ht ht.1
      have hhigh : ρ t ≤ tangentNorm g p v := by
        rw [← h1]; exact hmono ht ⟨hab, le_rfl⟩ ht.2
      exact ⟨ρ t / tangentNorm g p v,
        ⟨div_nonneg hlow hn.le, (div_le_one hn).mpr hhigh⟩, (heq t ht).symm⟩
    · rintro ⟨s, hs, rfl⟩
      have hval : s * tangentNorm g p v ∈ Icc (ρ a) (ρ b) := by
        rw [h0, h1]
        exact ⟨mul_nonneg hs.1 hn.le, mul_le_of_le_one_left hn.le hs.2⟩
      obtain ⟨t, ht, hrt⟩ := intermediate_value_Icc hab hρ hval
      refine ⟨t, ht, ?_⟩
      rw [heq t ht, hrt, mul_div_cancel_right₀ s hn.ne']

/-- A zero endpoint in the injective normal ball forces the constant curve.
No positive-dimension or nondegenerate-interval assumption occurs. -/
theorem radialParametrization_constant (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (F : CurveFamily (Phase S))
    (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    {a b : ℝ} {γ : ℝ → M} (hγ : RadialParametrization g F p v a b γ)
    (hend : fiberExponential F p v = p) : ∀ t ∈ Icc a b, γ t = p := by
  have hz := (ExponentialNormalCoordinates.zero_section_at C F hF p).2
  have hv0 : v = 0 := normal_chart_exp_injective g F p E R d hd hv
    (by simpa only [SmoothMetrics.tangentNorm_zero] using hd.1) (hend.trans hz.symm)
  subst v
  obtain ⟨ρ, _, _, _, _, heq⟩ := hγ
  intro t ht
  simpa only [smul_zero, hz] using heq t ht

/-- The infimum argument has no local-chart restriction on competitors. -/
theorem componentDistance_eq_of_radial_comparison (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (v : TangentSpace S p)
    (γ : PiecewiseC1Curve S 0 1) (h0 : γ 0 = p)
    (h1 : γ 1 = fiberExponential F p v) (hL : length g γ = tangentNorm g p v)
    (hcomp : ∀ {a b : ℝ} (c : PiecewiseC1Curve S a b),
      c a = p → c b = fiberExponential F p v → tangentNorm g p v ≤ length g c) :
    ∃ hq : fiberExponential F p v ∈ connectedComponent p,
      componentDistance g p ⟨p, mem_connectedComponent⟩
        ⟨fiberExponential F p v, hq⟩ = tangentNorm g p v := by
  have hq := LengthDistance.path_mem_component ⟨0, 1, γ, h0, h1⟩
  refine ⟨hq, le_antisymm ?_ ?_⟩
  · exact (LengthDistance.componentDistance_le_length g p
      ⟨p, mem_connectedComponent⟩ ⟨fiberExponential F p v, hq⟩ γ h0 h1).trans_eq hL
  · change tangentNorm g p v ≤ sInf (P202.DistanceData.pathLengths g p (fiberExponential F p v))
    have hne : (P202.DistanceData.pathLengths g p (fiberExponential F p v)).Nonempty :=
      ⟨length g γ, 0, 1, γ, h0, h1, rfl⟩
    apply le_csInf hne
    rintro L ⟨a, b, c, hc0, hc1, rfl⟩
    exact hcomp c hc0 hc1

/-- Once the two analytic obligations are proved, all original conclusions
follow, including distance, escape control, pauses, and the center case.
This conditional assembly is not a proof of either analytic obligation. -/
theorem normal_minimality_of_comparison_and_rigidity :
    P202Specs.Geometry.NormalMinimality.normal_minimality_of_comparison_and_rigidityType.{u} := by
  intro hcomp hrig n M _ S g C hC F hF p
  obtain ⟨E, r₀, R, d, hE, hr₀, hrR, hd⟩ := normal_radius_exists S g C F hF p
  refine ⟨E, r₀, R, d, hE, hr₀, hrR, hd, ?_⟩
  intro v hv
  have hvR := hv.trans hrR
  obtain ⟨γ, hγ0, hγ1, hγrad, _, hγgeo, hγL⟩ :=
    radial_segment_exists S g C hC F hF p E R d hd v hvR
  have hcomparison {a b : ℝ} (c : PiecewiseC1Curve S a b)
      (hc0 : c a = p) (hc1 : c b = fiberExponential F p v) :=
    hcomp S g C hC F hF p E r₀ R d hr₀ hrR hd v hv c hc0 hc1
  refine ⟨⟨γ, hγ0, hγ1, hγrad, hγgeo, hγL⟩,
    componentDistance_eq_of_radial_comparison g F p v γ hγ0 hγ1 hγL
      (fun c hc0 hc1 => (hcomparison c hc0 hc1).1), ?_⟩
  intro a b c hc0 hc1
  have hc := hcomparison c hc0 hc1
  refine ⟨hc.1, ?_⟩
  intro hL
  have hstay := hc.2 (hL.trans_lt hv)
  have hparam := hrig S g C hC F hF p E R d hd v hvR c hc0 hc1 hstay hL
  exact ⟨hparam, radialParametrization_image g F p v c.ordered hparam,
    radialParametrization_constant g C F hF p E R d hd v hvR hparam⟩


theorem length_restrict_le (g : RiemannianMetric S) {a b l r : ℝ}
    (c : PiecewiseC1Curve S a b) (hal : a ≤ l) (hlr : l ≤ r) (hrb : r ≤ b) :
    length g (PiecewiseCurves.restrict c l r hal hlr hrb) ≤ length g c := by
  exact intervalIntegral.integral_mono_interval hal hlr hrb
    (.of_forall (fun t => SmoothMetrics.tangentNorm_nonneg g (c t) _))
    (PiecewiseCurves.speed_integrable g c)

/-- Equality in the radial comparison fixes the accumulated length at every
parameter, even at centers and at corners. -/
theorem normal_chart_minimizing_prefix (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (h0 : c a = p) (h1 : c b = fiberExponential F p v)
    (hsource : ∀ t ∈ Icc a b, c t ∈ d.source)
    (hL : length g c = tangentNorm g p v) :
    (∀ t ∈ Icc a b, (∫ u in a..t, speed g c u) =
      tangentNorm g p (E.symm (d (c t)).val)) ∧
    MonotoneOn (fun t => tangentNorm g p (E.symm (d (c t)).val)) (Icc a b) := by
  have hpre (t : ℝ) (ht : t ∈ Icc a b) :
      (∫ u in a..t, speed g c u) = tangentNorm g p (E.symm (d (c t)).val) := by
    let cp := PiecewiseCurves.restrict c a t le_rfl ht.1 ht.2
    let cs := PiecewiseCurves.restrict c t b ht.1 ht.2 le_rfl
    have hp := normal_chart_radius_displacement_le_length g C hC F hF p E R d hd cp
      (fun s hs => hsource s ⟨hs.1, hs.2.trans ht.2⟩)
    have hs := normal_chart_radius_displacement_le_length g C hC F hF p E R d hd cs
      (fun s hs => hsource s ⟨ht.1.trans hs.1, hs.2⟩)
    change |tangentNorm g p (E.symm (d (c t)).val) -
      tangentNorm g p (E.symm (d (c a)).val)| ≤ ∫ u in a..t, speed g c u at hp
    change |tangentNorm g p (E.symm (d (c b)).val) -
      tangentNorm g p (E.symm (d (c t)).val)| ≤ ∫ u in t..b, speed g c u at hs
    rw [h0, hd.2.2.2.1, map_zero, SmoothMetrics.tangentNorm_zero,
      sub_zero, abs_of_nonneg (SmoothMetrics.tangentNorm_nonneg g p _)] at hp
    rw [h1, (normal_chart_exp g F p E R d hd v hv).2.2,
      LinearEquiv.symm_apply_apply] at hs
    have hsi := PiecewiseCurves.speed_integrable g c
    have hi := intervalIntegral.integral_add_adjacent_intervals
      (hsi.mono_set (by rw [uIcc_of_le ht.1, uIcc_of_le c.ordered]; exact Icc_subset_Icc_right ht.2))
      (hsi.mono_set (by rw [uIcc_of_le ht.2, uIcc_of_le c.ordered]; exact Icc_subset_Icc_left ht.1))
    change (∫ u in a..b, speed g c u) = tangentNorm g p v at hL
    have hh := le_abs_self (tangentNorm g p v - tangentNorm g p (E.symm (d (c t)).val))
    linarith
  refine ⟨hpre, ?_⟩
  intro s hs t ht hst
  dsimp only
  rw [← hpre s hs, ← hpre t ht]
  exact intervalIntegral.integral_mono_interval le_rfl hs.1 hst
    (.of_forall (fun u => SmoothMetrics.tangentNorm_nonneg g (c u) _))
    ((PiecewiseCurves.speed_integrable g c).mono_set (by
      rw [uIcc_of_le ht.1, uIcc_of_le c.ordered]; exact Icc_subset_Icc_right ht.2))


/-- The positive definite fiber norm controls any fixed coordinate norm. -/
theorem coordinateNorm_lower_bound (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x : Euclidean n,
      δ * ‖x‖ ≤ tangentNorm g p (E.symm x) := by
  let K : Set (Euclidean n) := Metric.sphere 0 1
  have hK : IsCompact K := isCompact_sphere _ _
  have hpos (x : Euclidean n) (hx : x ≠ 0) :
      0 < tangentNorm g p (E.symm x) := by
    apply lt_of_le_of_ne (SmoothMetrics.tangentNorm_nonneg g p _)
    intro heq
    have hz := (SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp heq.symm
    exact hx (by simpa using congrArg E hz)
  have hunit (x : Euclidean n) (hx : x ≠ 0) : ‖x‖⁻¹ • x ∈ K := by
    simp [K, norm_smul, ne_of_gt (norm_pos_iff.mpr hx)]
  by_cases hne : K.Nonempty
  · obtain ⟨w, hw, hmin⟩ := hK.exists_isMinOn hne
      (coordinateNorm_continuous g p E).continuousOn
    have hwne : w ≠ 0 := by
      intro h
      simp [h, K] at hw
    refine ⟨tangentNorm g p (E.symm w), hpos w hwne, ?_⟩
    intro x
    by_cases hx : x = 0
    · simp [hx, SmoothMetrics.tangentNorm_zero]
    have hn : 0 < ‖x‖ := norm_pos_iff.mpr hx
    have hb := hmin (hunit x hx)
    change tangentNorm g p (E.symm w) ≤ tangentNorm g p (E.symm (‖x‖⁻¹ • x)) at hb
    rw [map_smul, SmoothMetrics.tangentNorm_smul,
      abs_of_pos (inv_pos.mpr hn)] at hb
    exact (le_div_iff₀ hn).mp (by simpa only [div_eq_inv_mul] using hb)
  · refine ⟨1, zero_lt_one, ?_⟩
    intro x
    have hx : x = 0 := by
      by_contra h
      exact hne ⟨_, hunit x h⟩
    simp [hx, SmoothMetrics.tangentNorm_zero]

/-- Closed coordinate fiber balls are compact, including dimension zero. -/
theorem isCompact_coordinateNorm_le (g : RiemannianMetric S) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r : ℝ) :
    IsCompact {x : Euclidean n | tangentNorm g p (E.symm x) ≤ r} := by
  obtain ⟨δ, hδ, hb⟩ := coordinateNorm_lower_bound g p E
  apply (isCompact_closedBall (0 : Euclidean n) (r / δ)).of_isClosed_subset
    (isClosed_Iic.preimage (coordinateNorm_continuous g p E))
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (le_div_iff₀ hδ).mpr (by simpa only [mul_comm] using (hb x).trans hx)

/-- The image of a closed, strictly smaller normal ball is closed in M. -/
theorem isClosed_normal_closed_ball (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (hrR : r < R) :
    IsClosed {q : M | q ∈ d.source ∧ tangentNorm g p (E.symm (d q).val) ≤ r} := by
  let : T2Space M := S.topologicalManifold.hausdorff
  let K : Set (Euclidean n) := {x | tangentNorm g p (E.symm x) ≤ r}
  let j : Euclidean n → ModelSpace n .euclidean := fun x => ⟨x, mem_univ _⟩
  have hj : Continuous j := continuous_id.subtype_mk _
  have htarget : ∀ x ∈ K, j x ∈ d.target := by
    intro x hx
    rw [hd.2.2.2.2.1]
    exact hx.trans_lt hrR
  have hcomp : ContinuousOn (fun x => d.symm (j x)) K :=
    d.symm.continuousOn.comp hj.continuousOn htarget
  have hcompact := (isCompact_coordinateNorm_le g p E r).image_of_continuousOn hcomp
  have hset : (fun x => d.symm (j x)) '' K =
      {q : M | q ∈ d.source ∧ tangentNorm g p (E.symm (d q).val) ≤ r} := by
    ext q
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨d.map_target (htarget x hx), ?_⟩
      rw [d.right_inv (htarget x hx)]
      exact hx
    · intro hq
      refine ⟨(d q).val, hq.2, ?_⟩
      have hjq : j (d q).val = d q := Subtype.ext rfl
      change d.symm (j (d q).val) = q
      rw [hjq, d.left_inv hq.1]
  rw [← hset]
  exact hcompact.isClosed

/-- A curve of length less than an inner normal radius stays in the chart.
This proves the escape estimate without assuming the original curve stays
in the chart or that its radius is differentiable at visits to the center. -/
theorem normal_chart_short_curve_stays (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (r R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (hr : 0 < r) (hrR : r < R)
    {a b : ℝ} (c : PiecewiseC1Curve S a b) (h0 : c a = p)
    (hL : length g c < r) : ∀ t ∈ Icc a b, c t ∈ d.source := by
  let K : Set M := {q | q ∈ d.source ∧ tangentNorm g p (E.symm (d q).val) ≤ r}
  have hKclosed : IsClosed K := isClosed_normal_closed_ball g F p E r R d hd hrR
  let A : Set ℝ := c ⁻¹' K
  have hAclosed : IsClosed (A ∩ Icc a b) := by
    simpa [A, inter_comm] using c.continuousOn.preimage_isClosed_of_isClosed
      isClosed_Icc hKclosed
  have haA : a ∈ A := by
    change c a ∈ K
    rw [h0]
    refine ⟨hd.2.2.1, ?_⟩
    rw [hd.2.2.2.1, map_zero, SmoothMetrics.tangentNorm_zero]
    exact hr.le
  have hstay : Icc a b ⊆ A := by
    apply hAclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset haA
    intro t ht hprefix
    have hsource : ∀ s ∈ Icc a t, c s ∈ d.source := fun s hs => (hprefix hs).1
    let c' := PiecewiseCurves.restrict c a t le_rfl ht.1 ht.2.le
    have hdisp := normal_chart_radius_displacement_le_length g C hC F hF p E R d hd c' hsource
    change |tangentNorm g p (E.symm (d (c t)).val) -
      tangentNorm g p (E.symm (d (c a)).val)| ≤ length g c' at hdisp
    rw [h0, hd.2.2.2.1, map_zero, SmoothMetrics.tangentNorm_zero, sub_zero,
      abs_of_nonneg (SmoothMetrics.tangentNorm_nonneg g p _)] at hdisp
    have hrad : tangentNorm g p (E.symm (d (c t)).val) < r :=
      (hdisp.trans (length_restrict_le g c le_rfl ht.1 ht.2.le)).trans_lt hL
    have hctsource : c t ∈ d.source := hsource t ⟨ht.1, le_rfl⟩
    have hrc : ContinuousAt (fun q : M => tangentNorm g p (E.symm (d q).val)) (c t) :=
      (coordinateNorm_continuous g p E).continuousAt.comp
        (continuous_subtype_val.continuousAt.comp (d.continuousAt hctsource))
    have hsmall : ∀ᶠ q in 𝓝 (c t), q ∈ K := by
      filter_upwards [d.open_source.mem_nhds hctsource,
        hrc.eventually_lt_const hrad] with q hqs hqr
      exact ⟨hqs, hqr.le⟩
    have hct : ContinuousWithinAt c (Ioi t) t :=
      (c.continuousOn t ⟨ht.1, ht.2.le⟩).mono_of_mem_nhdsWithin
        (Icc_mem_nhdsGT_of_mem ht)
    exact hct.preimage_mem_nhdsWithin hsmall
  exact fun t ht => (hstay ht).1

/-- The global comparison includes competitors which leave the chart. -/
theorem global_comparison :
    P202Specs.Geometry.NormalMinimality.global_comparisonType.{u} := by
  intro n M _ S g C hC F hF p E r R d hr hrR hd v hv a b c h0 h1
  have hstay : length g c < r → ∀ t ∈ Icc a b, c t ∈ d.source :=
    normal_chart_short_curve_stays g C hC F hF p E r R d hd hr hrR c h0
  refine ⟨?_, hstay⟩
  by_cases hL : length g c < r
  · exact normal_chart_comparison g C hC F hF p E R d hd v (hv.trans hrR)
      c h0 h1 (hstay hL)
  · exact hv.le.trans (le_of_not_gt hL)


open PiecewiseCurves (exists_piece_off_breakpoints node_mem withinNorm_continuousOn
  withinVelocity_eq_velocity velocity_on_piece)

theorem speed_continuousAt_off_breakpoints (g : RiemannianMetric S) {a b : ℝ}
    (c : PiecewiseC1Curve S a b) {t : ℝ} (ht : t ∈ Icc a b)
    (hcorner : t ∉ breakpoints c) : ContinuousAt (speed g c) t := by
  obtain ⟨i, hi⟩ := exists_piece_off_breakpoints c ht hcorner
  have hlt : c.node i.castSucc < c.node i.succ := hi.1.trans hi.2
  have hc : ContinuousOn c (Icc (c.node i.castSucc) (c.node i.succ)) :=
    c.continuousOn.mono (fun _ hs =>
      ⟨(node_mem c i.castSucc).1.trans hs.1, hs.2.trans (node_mem c i.succ).2⟩)
  have hcont := (withinNorm_continuousOn g (c.regular i) hc
    (uniqueDiffOn_Icc hlt)).continuousAt (Icc_mem_nhds hi.1 hi.2)
  refine hcont.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hi.1 hi.2] with s hs
  dsimp only [speed]
  rw [withinVelocity_eq_velocity (c.regular i) hc (uniqueDiffOn_Icc hlt)
    (Ioo_subset_Icc_self hs) (velocity_on_piece c i hs)]

theorem prefix_hasDerivAt {f r : ℝ → ℝ} {a b t : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b)
    (hat : a < t) (htb : t < b) (hcont : ContinuousAt f t)
    (hprefix : ∀ s ∈ Icc a b, (∫ u in a..s, f u) = r s) :
    HasDerivAt r (f t) t := by
  have hmeas : StronglyMeasurableAtFilter f (𝓝 t) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem
      hf.1.aestronglyMeasurable (Ioc_mem_nhds hat htb)
  have hfi : IntervalIntegrable f MeasureTheory.volume a t := by
    apply hf.mono_set
    rw [uIcc_of_le hat.le, uIcc_of_le (hat.trans htb).le]
    exact Icc_subset_Icc le_rfl htb.le
  refine (intervalIntegral.integral_hasDerivAt_right hfi hmeas hcont).congr_of_eventuallyEq ?_
  filter_upwards [Icc_mem_nhds hat htb] with s hs
  exact (hprefix s hs).symm

/-- Equality in the Gauss speed bound fixes the entire coordinate velocity,
including a zero velocity. -/
theorem normal_chart_coordinate_velocity_of_pairing_eq (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    (u : TangentSpace S (fiberExponential F p v))
    (hr : tangentNorm g p v ≠ 0)
    (heq : pairing g p v
      (E.symm ((tangentStructure S).fiberCoordinates.equiv d hd.2.1
        (fiberExponential F p v) (normal_chart_exp g F p E R d hd v hv).2.1 u)) =
      tangentNorm g p v * tangentNorm g (fiberExponential F p v) u) :
    (tangentStructure S).fiberCoordinates.equiv d hd.2.1
        (fiberExponential F p v) (normal_chart_exp g F p E R d hd v hv).2.1 u =
      (tangentNorm g (fiberExponential F p v) u / tangentNorm g p v) • E v := by
  obtain ⟨e, he, hp⟩ := S.smoothStructure.property.1.1 p
  let hq := (normal_chart_exp g F p E R d hd v hv).2.1
  let D := (tangentStructure S).fiberCoordinates.equiv d hd.2.1
    (fiberExponential F p v) hq
  let L := P202.GaussData.fiberDifferential F p v e he hp d hd.2.1 hq
  let w := E.symm (D u)
  have hLu : L w = u := by
    apply D.injective
    rw [normal_chart_fiberDifferential g F p E R d hd v hv e he hp w]
    exact E.apply_symm_apply _
  have hgauss := GaussLemma.gauss_lemma S g C hC F hF p v
    (normal_chart_exp g F p E R d hd v hv).1 e he hp d hd.2.1 hq w
  have hrad := GaussLemma.radial_length S g C hC F hF p v
    (normal_chart_exp g F p E R d hd v hv).1 e he hp d hd.2.1 hq
  have hLne : L v ≠ 0 := by
    intro hz
    have hh : tangentNorm g (fiberExponential F p v) (L v) = 0 := by
      rw [hz, SmoothMetrics.tangentNorm_zero]
    exact hr (hrad.symm.trans hh)
  have hpair : pairing g (fiberExponential F p v) (L v) u =
      tangentNorm g (fiberExponential F p v) (L v) *
        tangentNorm g (fiberExponential F p v) u := by
    rw [← hLu, hgauss, hrad, hLu]
    exact heq
  have hu := eq_smul_of_pairing_eq_norm_mul g (fiberExponential F p v) (L v) u hLne hpair
  have hu' := congrArg D hu
  rw [D.map_smul, normal_chart_fiberDifferential g F p E R d hd v hv e he hp v,
    hrad] at hu'
  exact hu'

/-- The same equality statement at any point of the normal chart. -/
theorem normal_chart_coordinate_velocity_at_of_pairing_eq (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (q : M) (hq : q ∈ d.source) (u : TangentSpace S q)
    (hr : tangentNorm g p (E.symm (d q).val) ≠ 0)
    (heq : pairing g p (E.symm (d q).val)
      (E.symm ((tangentStructure S).fiberCoordinates.equiv d hd.2.1 q hq u)) =
      tangentNorm g p (E.symm (d q).val) * tangentNorm g q u) :
    (tangentStructure S).fiberCoordinates.equiv d hd.2.1 q hq u =
      (tangentNorm g q u / tangentNorm g p (E.symm (d q).val)) • (d q).val := by
  obtain ⟨hv, hexp⟩ := normal_chart_inverse g F p E R d hd q hq
  generalize hw : E.symm (d q).val = w at hv hexp hr heq ⊢
  have hx : E w = (d q).val := by rw [← hw, E.apply_symm_apply]
  rw [← hx]
  subst q
  exact normal_chart_coordinate_velocity_of_pairing_eq g C hC F hF p E R d hd w hv u hr heq

/-- A coordinate path whose velocity is purely outward radial has constant
normalized coordinates, with no nonzero-speed requirement. -/
theorem normalized_coordinates_hasDerivAt_zero {x : ℝ → Euclidean n}
    {r : ℝ → ℝ} {t s : ℝ} (hr : r t ≠ 0)
    (hx : HasDerivAt x ((s / r t) • x t) t)
    (hder : HasDerivAt r s t) :
    HasDerivAt (fun u => (r u)⁻¹ • x u) 0 t := by
  have hd := (hder.inv hr).smul hx
  have hcoef : (r t)⁻¹ * (s / r t) + -s / r t ^ 2 = 0 := by
    field_simp
    ring
  convert hd using 1;
    simp only [Pi.inv_apply, smul_smul, ← add_smul, hcoef, zero_smul]

theorem eq_endpoints_of_hasDerivAt_zero_off_countable {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]
    {f : ℝ → V} {a b : ℝ}
    (hab : a ≤ b) {s : Set ℝ} (hs : s.Countable)
    (hc : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b \ s, HasDerivAt f 0 x) : f b = f a := by
  have h := MeasureTheory.integral_eq_of_hasDerivAt_off_countable_of_le
    f (fun _ => (0 : V)) hab hs hc hd (intervalIntegrable_const)
  simpa only [intervalIntegral.integral_zero, eq_comm, sub_eq_zero] using h


/-- Prefix equality forces the normalized coordinate derivative to vanish
at every non-corner point of positive radius. -/
theorem normal_chart_normalized_deriv_eq_zero (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (hsource : ∀ t ∈ Icc a b, c t ∈ d.source)
    (hprefix : ∀ t ∈ Icc a b, (∫ u in a..t, speed g c u) =
      tangentNorm g p (E.symm (d (c t)).val))
    {t : ℝ} (ht : t ∈ Ioo a b) (htK : t ∉ breakpoints c)
    (hr : tangentNorm g p (E.symm (d (c t)).val) ≠ 0) :
    HasDerivAt (fun u => (tangentNorm g p (E.symm (d (c u)).val))⁻¹ •
      (d (c u)).val) 0 t := by
  let x : ℝ → Euclidean n := fun u => (d (c u)).val
  let r : ℝ → ℝ := fun u => tangentNorm g p (E.symm (x u))
  have ht' := Ioo_subset_Icc_self ht
  have hrder : HasDerivAt r (speed g c t) t :=
    prefix_hasDerivAt (PiecewiseCurves.speed_integrable g c) ht.1 ht.2
      (speed_continuousAt_off_breakpoints g c ht' htK) hprefix
  have hxt := PiecewiseCurves.hasVelocityAt_coordinates
    (PiecewiseCurves.hasVelocityAt_off_breakpoints c ht' htK) d hd.2.1 (hsource t ht')
  have hsq := coordinateNorm_sq_hasDerivAt g p E hxt
  have heqder := hsq.unique (hrder.pow 2)
  have hpair : pairing g p (E.symm (x t))
      (E.symm ((tangentStructure S).fiberCoordinates.equiv d hd.2.1
        (c t) (hsource t ht') (velocity S c t))) = r t * speed g c t := by
    dsimp only [r, x] at heqder ⊢
    norm_num at heqder
    nlinarith only [heqder]
  have hz := normal_chart_coordinate_velocity_at_of_pairing_eq g C hC F hF p E R d hd
    (c t) (hsource t ht') (velocity S c t) hr hpair
  have hxder : HasDerivAt x ((speed g c t / r t) • x t) t := by
    dsimp only [x, r, speed]
    rw [← hz]
    exact hxt
  exact normalized_coordinates_hasDerivAt_zero hr hxder hrder

/-- Equality and monotonicity of prefix lengths give a radial
parametrization, allowing arbitrarily many pauses and center times. -/
theorem normal_chart_rigidity_of_prefix (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F) (p : M)
    (E : TangentSpace S p ≃ₗ[ℝ] Euclidean n) (R : ℝ)
    (d : ModelChart n .euclidean M) (hd : IsNormalChart g F p E R d)
    (v : TangentSpace S p) (hv : tangentNorm g p v < R)
    {a b : ℝ} (c : PiecewiseC1Curve S a b)
    (h0 : c a = p) (h1 : c b = fiberExponential F p v)
    (hsource : ∀ t ∈ Icc a b, c t ∈ d.source)
    (hprefix : ∀ t ∈ Icc a b, (∫ u in a..t, speed g c u) =
      tangentNorm g p (E.symm (d (c t)).val))
    (hmono : MonotoneOn (fun t => tangentNorm g p (E.symm (d (c t)).val)) (Icc a b)) :
    RadialParametrization g F p v a b c := by
  classical
  let x : ℝ → Euclidean n := fun t => (d (c t)).val
  let r : ℝ → ℝ := fun t => tangentNorm g p (E.symm (x t))
  have hxc : ContinuousOn x (Icc a b) :=
    (continuous_subtype_val.comp_continuousOn d.continuousOn).comp c.continuousOn hsource
  have hrc : ContinuousOn r (Icc a b) :=
    (coordinateNorm_continuous g p E).comp_continuousOn hxc
  have hr0 : r a = 0 := by
    dsimp only [r, x]
    rw [h0, hd.2.2.2.1, map_zero, SmoothMetrics.tangentNorm_zero]
  have hx1 : x b = E v := by
    dsimp only [x]
    rw [h1, (normal_chart_exp g F p E R d hd v hv).2.2]
  have hr1 : r b = tangentNorm g p v := by
    dsimp only [r]
    rw [hx1, E.symm_apply_apply]
  refine ⟨r, hrc, hmono, hr0, hr1, ?_⟩
  intro t ht
  rw [← (normal_chart_inverse g F p E R d hd (c t) (hsource t ht)).2]
  apply congrArg (fiberExponential F p)
  apply E.injective
  simp only [E.apply_symm_apply, E.map_smul]
  change x t = (r t / tangentNorm g p v) • E v
  by_cases hrt : r t = 0
  · have hz : E.symm (x t) = 0 := (SmoothMetrics.tangentNorm_eq_zero_iff g p _).mp hrt
    have hxt0 : x t = 0 := by
      have h := congrArg E hz
      simpa only [E.apply_symm_apply, map_zero] using h
    rw [hxt0, hrt, zero_div, zero_smul]
  · have hrtpos : 0 < r t := lt_of_le_of_ne
      (SmoothMetrics.tangentNorm_nonneg g p _) (Ne.symm hrt)
    have hsub : Icc t b ⊆ Icc a b := Icc_subset_Icc ht.1 le_rfl
    have hne (s : ℝ) (hs : s ∈ Icc t b) : r s ≠ 0 :=
      ne_of_gt (hrtpos.trans_le (hmono ht (hsub hs) hs.1))
    have hnc : ContinuousOn (fun u => (r u)⁻¹ • x u) (Icc t b) :=
      ((hrc.mono hsub).inv₀ hne).smul (hxc.mono hsub)
    have hnd : ∀ s ∈ Ioo t b \ (breakpoints c : Set ℝ),
        HasDerivAt (fun u => (r u)⁻¹ • x u) 0 s := by
      intro s hs
      exact normal_chart_normalized_deriv_eq_zero g C hC F hF p E R d hd c hsource hprefix
        ⟨ht.1.trans_lt hs.1.1, hs.1.2⟩ hs.2 (hne s (Ioo_subset_Icc_self hs.1))
    have heq := eq_endpoints_of_hasDerivAt_zero_off_countable ht.2
      (breakpoints c).finite_toSet.countable hnc hnd
    have hscaled := congrArg (fun z : Euclidean n => r t • z) heq
    simp only [smul_smul, mul_inv_cancel₀ hrt, one_smul] at hscaled
    rw [hx1, hr1] at hscaled
    simpa only [div_eq_mul_inv] using hscaled.symm


/-- Equality in the normal-chart length comparison permits precisely outward
radial motion with variable speed and pauses. -/
theorem chart_rigidity :
    P202Specs.Geometry.NormalMinimality.chart_rigidityType.{u} := by
  intro n M _ S g C hC F hF p E R d hd v hv a b c h0 h1 hsource hL
  obtain ⟨hprefix, hmono⟩ :=
    normal_chart_minimizing_prefix g C hC F hF p E R d hd v hv c h0 h1 hsource hL
  exact normal_chart_rigidity_of_prefix g C hC F hF p E R d hd v hv c h0 h1
    hsource hprefix hmono

/-- The centered normal-ball minimality theorem for all compact piecewise C¹
competitors in the manifold, with distance equality and the complete rigidity
statement, including pauses and the constant radial segment. -/
theorem normal_minimality :
    P202Specs.Geometry.NormalMinimality.normal_minimalityType.{u} :=
  normal_minimality_of_comparison_and_rigidity global_comparison chart_rigidity

end P202.Geometry.NormalMinimality
