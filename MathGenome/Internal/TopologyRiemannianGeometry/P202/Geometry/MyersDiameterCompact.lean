import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.MyersDiameterCompact
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.MinimizingIndexForm
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.HopfRinow
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Tactic.FinCases
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ParallelTransport
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.RicciScalarBianchi
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Bonnet--Myers: the sharp segment and diameter bounds, and compactness.
The proof constructs smooth parallel normal fields in the original tangent
fibers, applies minimizing-index nonnegativity, and then uses Hopf--Rinow. -/
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false


open Set Filter
open scoped Topology ContDiff

namespace P202.Geometry.MyersRegularity

section
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
lemma smoothAt_of_linear_equation {A : ℝ → F →L[ℝ] F} {Y : ℝ → F} {t : ℝ}
    (hA : ContDiffAt ℝ (⊤ : ℕ∞) A t) (hY : ContDiffAt ℝ 1 Y t)
    (hd : ∀ᶠ s in 𝓝 t, HasDerivAt Y (A s (Y s)) s) :
    ContDiffAt ℝ (⊤ : ℕ∞) Y t := by
  apply contDiffAt_infty.mpr
  intro k
  induction k with
  | zero => exact hY.of_le (by simp)
  | succ k ih =>
    rw [show ((k+1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω)+1 by simp]
    apply contDiffAt_succ_iff_hasFDerivAt.mpr
    refine ⟨fun s => ContinuousLinearMap.toSpanSingleton ℝ (A s (Y s)), ?_, ?_⟩
    · exact ⟨{s | HasDerivAt Y (A s (Y s)) s}, hd, fun s hs => hs.hasFDerivAt⟩
    · exact ContinuousLinearMap.toSpanSingletonCLE.contDiff.contDiffAt.comp t
        ((hA.of_le (by simp)).clm_apply ih)
end

section Extension
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

lemma linear_ode_smooth_germ {a b t : ℝ} (hab : a < b) (ht : t ∈ Icc a b)
    {A : ℝ → F →L[ℝ] F} (hA : ContDiffAt ℝ (⊤ : ℕ∞) A t)
    {Z : ℝ → F}
    (hd : ∀ᶠ r in 𝓝[Icc a b] t,
      HasDerivWithinAt Z (A r (Z r)) (Icc a b) r) :
    ∃ Y : ℝ → F, ContDiffAt ℝ (⊤ : ℕ∞) Y t ∧ Y t = Z t ∧
      Z =ᶠ[𝓝[Icc a b] t] Y := by
  obtain ⟨u, hut, hu⟩ := hA.contDiffOn (m := 1) (by simp) (by simp)
  obtain ⟨l, q, ⟨hlt, htq⟩, hIu⟩ := mem_nhds_iff_exists_Ioo_subset.mp hut
  let l₀ := (l+t)/2
  let q₀ := (t+q)/2
  have hl₀t : l₀ < t := by dsimp [l₀]; linarith
  have htq₀ : t < q₀ := by dsimp [q₀]; linarith
  have hK₀u : Icc l₀ q₀ ⊆ u := by
    apply Subset.trans _ hIu
    intro r hr
    dsimp [l₀,q₀] at hr
    constructor <;> linarith [hr.1, hr.2]
  have hK₀n : Icc l₀ q₀ ∈ 𝓝 t := Icc_mem_nhds hl₀t htq₀
  obtain ⟨Y, hY, hYt, hYd, hYu⟩ := P202.Geometry.ParallelTransport.linear_ode_c1_extension (hl₀t.trans htq₀).le A
    (hu.continuousOn.mono hK₀u) ⟨hl₀t.le, htq₀.le⟩ (Z t)
  have hYs : ContDiffAt ℝ (⊤ : ℕ∞) Y t := by
    apply smoothAt_of_linear_equation hA hY.contDiffAt
    filter_upwards [Ioo_mem_nhds hl₀t htq₀] with r hr
    exact (hYd r ⟨hr.1.le,hr.2.le⟩).hasDerivAt (Icc_mem_nhds hr.1 hr.2)
  obtain ⟨l₁,q₁,hl₁q₁,ht₁,hK₁J,hK₁W,hK₁n⟩ := P202.Geometry.ParallelTransport.exists_compact_subinterval hab ht
    (inter_mem hd (nhdsWithin_le_nhds hK₀n))
  have hZc : ContinuousOn Z (Icc l₁ q₁) := by
    intro r hr
    exact ((hK₁W hr).1.mono hK₁J).continuousWithinAt
  have hZd : ∀ r ∈ Icc l₁ q₁,
      HasDerivWithinAt Z (A r (Z r)) (Icc l₁ q₁) r := by
    intro r hr
    exact (hK₁W hr).1.mono hK₁J
  -- Run uniqueness on the smaller interval, where both traces solve the same ODE.
  obtain ⟨W,hW,hWt,hWd,hWu⟩ := P202.Geometry.ParallelTransport.linear_ode_c1_extension hl₁q₁.le A
    (hu.continuousOn.mono (fun r hr => hK₀u (hK₁W hr).2)) ht₁ (Z t)
  have hYe : EqOn Y W (Icc l₁ q₁) := hWu Y hY.continuous.continuousOn hYt
    (fun r hr => (hYd r (hK₁W hr).2).mono (fun s hs => (hK₁W hs).2))
  have hZe : EqOn Z W (Icc l₁ q₁) := hWu Z hZc rfl hZd
  refine ⟨Y,hYs,hYt,?_⟩
  filter_upwards [hK₁n] with r hr
  exact (hZe hr).trans (hYe hr).symm
end Extension
end P202.Geometry.MyersRegularity


set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false
namespace P202.Geometry.MyersCoefficientODE
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData SmoothManifolds.VectorFieldData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData P202.LeviCivitaData
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- In an actual tangent frame, parallel fields satisfy a linear equation whose
coefficient matrix has an ambient smooth germ, even at the segment ends. -/
theorem coefficients_parallel_ode_germ
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hγ : SmoothCurveOn S γ (Icc a b))
    (hD : ∀ r ∈ Icc a b,
      HasCovariantDerivativeWithinAt C γ V (Icc a b) r 0)
    {t : ℝ} (ht : t ∈ Icc a b) :
    ∃ (c : TangentIndex S) (A : ℝ → Matrix (Fin n) (Fin n) ℝ)
      (y : ℝ → Euclidean n),
      γ t ∈ (tangentBundle S).baseSet c ∧
      ContDiffAt ℝ (⊤ : ℕ∞) A t ∧
      ContDiffAt ℝ (⊤ : ℕ∞) y t ∧
      y t = (c.val (γ t)).val ∧
      (fun r => (c.val (γ r)).val) =ᶠ[𝓝[Icc a b] t] y ∧
      let bf := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
      ∀ᶠ r in 𝓝[Icc a b] t,
        HasDerivWithinAt (coefficientsAlong bf γ V)
          ((A r).mulVec (coefficientsAlong bf γ V r)) (Icc a b) r := by
  classical
  let J := Icc a b
  obtain ⟨e,he,hp,y,hy,hyt,hycoords⟩ := hγ.2 t ht
  let c : TangentIndex S := ⟨e,he⟩
  let bf := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  have hpB : γ t ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hp
  have hdy : ContDiffAt ℝ (⊤ : ℕ∞) (deriv y) t := by
    simpa using hy.derivWithin (by simp)
  have hnear : ∀ᶠ r in 𝓝[J] t, γ r ∈ e.source :=
    (hγ.1 t ht).preimage_mem_nhdsWithin (e.open_source.mem_nhds hp)
  have hgamma (k i j : Fin n) : ∃ g : ℝ → ℝ, ContDiffAt ℝ (⊤ : ℕ∞) g t ∧
      ((fun p => totalize (fun q => christoffel C c q k i j) p) ∘ γ) =ᶠ[𝓝[J] t] g := by
    apply GeodesicCriticalityCorners.scalar_smooth_extension hγ ht
    exact VectorSmoothAt.totalize (GeodesicIVP.tangent_baseSet_isOpen c)
      (GeodesicIVP.christoffel_smooth C c k i j ⟨γ t,hpB⟩)
  choose g hg heqg using hgamma
  let A : ℝ → Matrix (Fin n) (Fin n) ℝ := fun r k j =>
    -(∑ i : Fin n, g k i j r * deriv y r i)
  have hA : ContDiffAt ℝ (⊤ : ℕ∞) A t := by
    apply contDiffAt_pi.mpr
    intro k
    apply contDiffAt_pi.mpr
    intro j
    exact (ContDiffAt.sum fun i _ =>
      (hg k i j).mul (contDiffAt_pi.mp hdy i)).neg
  refine ⟨c,A,y,hpB,hA,hy,hyt,hycoords,?_⟩
  change ∀ᶠ r in 𝓝[J] t, HasDerivWithinAt (coefficientsAlong bf γ V)
    ((A r).mulVec (coefficientsAlong bf γ V r)) J r
  have hgall : ∀ᶠ r in 𝓝[J] t, ∀ k i j : Fin n,
      totalize (fun q => christoffel C c q k i j) (γ r) = g k i j r :=
    Filter.eventually_all.mpr (fun k => Filter.eventually_all.mpr (fun i =>
      Filter.eventually_all.mpr (fun j => heqg k i j)))
  have hy1 : ContDiffAt ℝ 1 y t := hy.of_le (by simp)
  filter_upwards [hnear,hycoords.derivWithin,hgall,
    (hy1.eventually (by simp)).filter_mono nhdsWithin_le_nhds,
    self_mem_nhdsWithin] with r hpr hdyEq hgr hyr hr
  have hpBr : γ r ∈ (tangentBundle S).baseSet c := (tangentRealization S).baseSet c ▸ hpr
  have hud : UniqueDiffWithinAt ℝ J r := uniqueDiffOn_Icc hab r hr
  obtain ⟨W,hW,hrest⟩ := hD r hr
  have hWval : (bf.basis ⟨γ r,hpBr⟩).equivFun W = deriv y r := by
    rw [FirstVariation.tangentFrame_coordinates e he (γ r) hpr]
    rw [← (CurveCovariantDerivative.velocity_coordinates hW hr e he hpr).derivWithin hud,hdyEq]
    exact (hyr.differentiableAt (by simp)).derivWithin hud
  have hd := ParallelTransport.parallel_coefficients_derivative_velocity C bf hr hud hpBr hW (hD r hr)
  have hmatrix : -((connectionMatrix C bf ⟨γ r,hpBr⟩ W).mulVec
      (coefficientsAlong bf γ V r)) = (A r).mulVec (coefficientsAlong bf γ V r) := by
    ext k
    rw [Pi.neg_apply, GeodesicCriticalityCorners.connectionMatrix_mulVec_coordinates C c
      ⟨γ r,hpBr⟩ W (coefficientsAlong bf γ V r) k]
    rw [hWval]
    have hgij (i j : Fin n) : christoffel C c ⟨γ r,hpBr⟩ k i j = g k i j r := by
      have h := hgr k i j
      simpa only [totalize_of_mem _ (γ r) hpBr] using h
    simp_rw [hgij]
    simp only [A, Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib,
      Finset.sum_mul]
    congr 1
    rw [Finset.sum_comm]
  exact hmatrix ▸ hd
end P202.Geometry.MyersCoefficientODE

namespace P202.Geometry.MyersRegularity
open SmoothManifolds.ModelData SmoothManifolds.AtlasData
  SmoothManifolds.TangentData SmoothManifolds.TangentBundleData
  SmoothManifolds.BundleData SmoothManifolds.BundleOperationsData
  SmoothManifolds.FrameData SmoothManifolds.VectorFieldData
  P202.ConnectionData P202.MetricData P202.CurveData P202.CurveConnectionData
  P202.FirstVariationData P202.CriticalityData P202.GeodesicData
open Set Filter
open scoped Topology Matrix.Norms.Elementwise
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- A parallel field along a smooth compact segment is smooth through both
closed ends, in the original canonical tangent charts. -/
theorem parallel_field_smooth
    (C : Connection (tangentBundle S)) {γ : ℝ → M}
    {V : (t : ℝ) → TangentSpace S (γ t)} {a b : ℝ} (hab : a < b)
    (hγ : SmoothCurveOn S γ (Icc a b))
    (hD : ∀ r ∈ Icc a b,
      HasCovariantDerivativeWithinAt C γ V (Icc a b) r 0) :
    SmoothFieldAlongOn S γ V (Icc a b) := by
  classical
  apply GeodesicCriticalityCorners.smooth_field_of_coordinate_germs hγ.1
  intro t ht
  obtain ⟨c,A,y,hpB,hA,hy,hyt,hycoords,hd⟩ :=
    MyersCoefficientODE.coefficients_parallel_ode_germ C hab hγ hD ht
  let bf := SmoothManifolds.ConstantRankBundles.trivializationFrame (tangentBundle S) c
  let T : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ]
      (Euclidean n →L[ℝ] Euclidean n) :=
    LinearMap.toContinuousLinearMap.toLinearMap.comp (Matrix.mulVecBilin ℝ ℝ)
  let B : ℝ → Euclidean n →L[ℝ] Euclidean n := fun r => T.toContinuousLinearMap (A r)
  have hB : ContDiffAt ℝ (⊤ : ℕ∞) B t :=
    T.toContinuousLinearMap.contDiff.contDiffAt.comp t hA
  have hdB : ∀ᶠ r in 𝓝[Icc a b] t,
      HasDerivWithinAt (coefficientsAlong bf γ V)
        (B r (coefficientsAlong bf γ V r)) (Icc a b) r := hd
  obtain ⟨z,hz,hzt,hzcoords⟩ := linear_ode_smooth_germ hab ht hB hdB
  let L := (tangentStructure S).productCoordinates.linearEquiv.toContinuousLinearEquiv
  have hp : γ t ∈ c.val.source := by
    rwa [(tangentRealization S).baseSet] at hpB
  have hnear : ∀ᶠ r in 𝓝[Icc a b] t, γ r ∈ c.val.source :=
    (hγ.1 t ht).preimage_mem_nhdsWithin (c.val.open_source.mem_nhds hp)
  have hcoords : (fun r => (((tangentStructure S).chart c.val c.property)
      ⟨γ r,V r⟩).val) =ᶠ[𝓝[Icc a b] t] fun r => L (y r,z r) := by
    filter_upwards [hnear,hycoords,hzcoords] with r hpr hyr hzr
    have hpBr : γ r ∈ (tangentBundle S).baseSet c :=
      (tangentRealization S).baseSet c ▸ hpr
    rw [(tangentStructure S).chart_apply c.val c.property _ hpr,hyr]
    rw [CurveCovariantDerivative.coefficientsAlong_of_mem _ _ _ _ hpBr,
      FirstVariation.tangentFrame_coordinates c.val c.property (γ r) hpr] at hzr
    rw [hzr]
    rfl
  exact ⟨c.val,c.property,hp,fun r => L (y r,z r),
    L.contDiff.contDiffAt.comp t (hy.prodMk hz),
    (hcoords.self_of_nhdsWithin ht).symm,hcoords⟩
end P202.Geometry.MyersRegularity

namespace P202.Geometry.MyersDiameterCompact
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.RicciData P202.SecondVariationData
  P202.FirstVariationData P202.CriticalityData P202.MinimizingIndexData
  P202.GeodesicData P202.ExponentialData P202.CompletenessData
  P202.CompleteExponentialData P202.MyersData
open Set Filter MeasureTheory
open scoped Topology
universe u

noncomputable abbrev lengthDiameter := @P202.MyersData.lengthDiameter

/-- The two elementary integrals retain the actual parameter interval. -/
theorem sine_square_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, Real.sin (Real.pi / L * t) ^ 2) = L / 2 := by
  have hc : Real.pi / L ≠ 0 := ne_of_gt (div_pos Real.pi_pos hL)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.sin x ^ 2) hc]
  simp only [mul_zero, div_mul_cancel₀ Real.pi hL.ne', integral_sin_sq,
    Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, zero_mul, mul_zero,
    sub_zero, zero_add, smul_eq_mul]
  field_simp

theorem cosine_square_integral {L : ℝ} (hL : 0 < L) :
    (∫ t in (0 : ℝ)..L, Real.cos (Real.pi / L * t) ^ 2) = L / 2 := by
  have hc : Real.pi / L ≠ 0 := ne_of_gt (div_pos Real.pi_pos hL)
  rw [intervalIntegral.integral_comp_mul_left (fun x => Real.cos x ^ 2) hc]
  simp only [mul_zero, div_mul_cancel₀ Real.pi hL.ne', integral_cos_sq,
    Real.sin_zero, Real.cos_zero, Real.sin_pi, Real.cos_pi, mul_zero,
    sub_zero, zero_add, smul_eq_mul]
  field_simp

/-- The explicit scalar upper bound in the source calculation. -/
theorem comparison_integral {L : ℝ} (hL : 0 < L) (m k : ℝ) :
    (∫ t in (0 : ℝ)..L, m * ((Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2 -
      k * Real.sin (Real.pi / L * t) ^ 2)) =
      m * L / 2 * ((Real.pi / L) ^ 2 - k) := by
  have hs : IntervalIntegrable (fun t => Real.sin (Real.pi / L * t) ^ 2) volume 0 L :=
    ((Real.continuous_sin.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable 0 L
  have hc : IntervalIntegrable (fun t => Real.cos (Real.pi / L * t) ^ 2) volume 0 L :=
    ((Real.continuous_cos.comp (continuous_const.mul continuous_id)).pow 2).intervalIntegrable 0 L
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_sub (hc.const_mul _) (hs.const_mul _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    cosine_square_integral hL, sine_square_integral hL]
  ring

/-- Positivity of n-1 is precisely where the dimension assumption enters. -/
theorem bound_of_scalar_comparison {n : ℕ} (hn : 2 ≤ n) {L k : ℝ}
    (hL : 0 < L) (hk : 0 < k)
    (h : 0 ≤ ((n : ℝ) - 1) * L / 2 * ((Real.pi / L) ^ 2 - k)) :
    L ≤ Real.pi / Real.sqrt k := by
  have hn' : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hm : 0 < ((n : ℝ) - 1) * L / 2 := by positivity
  have hratio : k ≤ (Real.pi / L) ^ 2 := by
    have h' := (mul_nonneg_iff_of_pos_left hm).mp h
    linarith
  have hs := Real.sq_sqrt hk.le
  have hspos := Real.sqrt_pos.mpr hk
  have hquot : Real.sqrt k ≤ Real.pi / L := by
    have hp : 0 < Real.pi / L := div_pos Real.pi_pos hL
    nlinarith
  exact (le_div_iff₀ hspos).mpr (by
    have hmul := (le_div_iff₀ hL).mp hquot
    nlinarith)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- The metric pairing of any two parallel fields is constant, including
one-sided values at the closed ends. -/
theorem parallel_pairing_constant_on_segment
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    {V W : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ V (Icc a b) t 0)
    (hW : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ W (Icc a b) t 0) :
    ∀ t ∈ Icc a b, pairing g (γ t) (V t) (W t) = pairing g (γ a) (V a) (W a) := by
  let f (t : ℝ) := pairing g (γ t) (V t) (W t)
  have hd (t : ℝ) (ht : t ∈ Icc a b) : HasDerivWithinAt f 0 (Icc a b) t := by
    have h := TorsionAndMetric.metric_curve_product (tangentBundle S) g C hC.2
      ht (uniqueDiffOn_Icc hab t ht) (hV t ht) (hW t ht)
    simpa only [f, pairing, map_zero, LinearMap.zero_apply, add_zero] using h
  exact constant_of_derivWithin_zero (fun t ht => (hd t ht).differentiableWithinAt)
    (fun t ht => (hd t ⟨ht.1, ht.2.le⟩).derivWithin
      (uniqueDiffOn_Icc hab t ⟨ht.1, ht.2.le⟩))

/-- A parallel normal vector remains normal to an affine geodesic. -/
theorem parallel_tangent_pairing_constant
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) {γ : ℝ → M} {a b : ℝ} (hab : a < b)
    (hγ : IsAffineGeodesicSegment C γ a b)
    {V : (t : ℝ) → TangentSpace S (γ t)}
    (hV : ∀ t ∈ Icc a b, HasCovariantDerivativeWithinAt C γ V (Icc a b) t 0) :
    ∀ t ∈ Icc a b,
      pairing g (γ t) (V t) (segmentTangent S γ a b t) =
      pairing g (γ a) (V a) (segmentTangent S γ a b a) := by
  exact parallel_pairing_constant_on_segment g C hC hab hV hγ.2


/-- The source's test fields, in the original tangent fibers. -/
noncomputable def sineField {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {γ : ℝ → M} {L : ℝ} (F : NormalParallelFrame g C R γ L) (i : Fin (n-1))
    (t : ℝ) : TangentSpace S (γ t) := Real.sin (Real.pi / L * t) • F.field i t

theorem sineField_smooth {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {γ : ℝ → M} {L : ℝ} (F : NormalParallelFrame g C R γ L) (i : Fin (n-1)) :
    SmoothFieldAlongOn S γ (sineField F i) (Icc 0 L) := by
  exact GeodesicCriticalityCorners.smooth_field_smul (F.smooth i)
    ((contDiff_const.mul contDiff_id).sin)

theorem sineField_endpoints {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (F : NormalParallelFrame g C R γ L) (i : Fin (n-1)) :
    sineField F i 0 = 0 ∧ sineField F i L = 0 := by
  simp [sineField, div_mul_cancel₀ Real.pi hL.ne']

theorem sineField_derivative {g : RiemannianMetric S}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (F : NormalParallelFrame g C R γ L) (i : Fin (n-1)) {t : ℝ} (ht : t ∈ Icc 0 L) :
    covariantDerivativeWithin C γ (sineField F i) (Icc 0 L) t =
      (Real.pi / L * Real.cos (Real.pi / L * t)) • F.field i t := by
  have hd := CurveCovariantDerivative.derivative_smul C (F.parallel i t ht)
    (((hasDerivAt_id t).const_mul (Real.pi / L)).sin.hasDerivWithinAt)
  simp only [smul_zero, add_zero, id_eq, mul_one] at hd
  exact (CurveCovariantDerivative.covariantDerivativeWithin_eq C ht
    (uniqueDiffOn_Icc hL t ht) hd).trans (by congr 1; ring)

/-- Sum of the actual index integrands; the frame trace is the canonical Ricci. -/
theorem sum_sine_indexIntegrand (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (R : CurvatureTensor S)
    {γ : ℝ → M} {L : ℝ} (hL : 0 < L)
    (F : NormalParallelFrame g C R γ L) {t : ℝ} (ht : t ∈ Icc 0 L) :
    (∑ i, indexIntegrand g C R γ 0 L (sineField F i) (sineField F i) t) =
      (n - 1 : ℕ) * (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2 -
        Real.sin (Real.pi / L * t) ^ 2 *
          ricci R (γ t) (segmentTangent S γ 0 L t) (segmentTangent S γ 0 L t) := by
  classical
  have hi (i : Fin (n-1)) :
      indexIntegrand g C R γ 0 L (sineField F i) (sineField F i) t =
        (Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2 -
        Real.sin (Real.pi / L * t) ^ 2 * curvatureForm g R (γ t)
          (F.field i t) (segmentTangent S γ 0 L t) (segmentTangent S γ 0 L t)
          (F.field i t) := by
    rw [indexIntegrand, sineField_derivative hL F i ht]
    simp only [sineField, curvatureForm, pairing, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    have he := F.orthonormal t ht i i
    simp only [ite_true] at he
    change (g.form (γ t)) (F.field i t) (F.field i t) = 1 at he
    rw [he]
    ring
  simp_rw [hi]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← Finset.mul_sum, F.trace t ht]
  ring

/-- Smoothness in the intrinsic tangent charts gives the regularity required
by the upstream index-nonnegativity theorem on the single-piece partition. -/
theorem indexForm_nonneg_smooth (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {L : ℝ} (hL : 0 < L) (γ : PiecewiseC1Curve S 0 L)
    (hγ : IsAffineGeodesicSegment C γ 0 L) (hmin : IsLengthMinimizing g γ)
    (V : (t : ℝ) → TangentSpace S (γ t))
    (hV : SmoothFieldAlongOn S γ V (Icc 0 L)) (ha : V 0 = 0) (hb : V L = 0) :
    0 ≤ indexForm g C R γ 0 L V V := by
  let node : Fin 2 → ℝ := ![0,L]
  have hnode : StrictMono node := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [node]
  apply MinimizingIndexForm.indexForm_nonneg g C hC R hR γ hL hγ hmin
    node hnode (by simp [node]) (by simp [node]) V _ ha hb
  refine ⟨by simpa [node] using hV.1, ?_⟩
  intro i
  fin_cases i
  change SmoothFieldOn γ V (Icc 0 L)
  intro t ht
  obtain ⟨e,he,hp,x,hx,hxt,heq⟩ := hV.2 t ht
  exact ⟨e,he,hp,x,hx,hxt.symm,heq⟩

/-- The complete summed-index estimate, conditional only on the actual frame.
The nonnegativity half uses minimality, not a curvature certificate. -/
theorem index_comparison (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R) (hn : 2 ≤ n)
    {k L : ℝ} (hL : 0 < L) (hRic : RicciLowerBound g R k)
    (γ : PiecewiseC1Curve S 0 L) (hγ : IsAffineGeodesicSegment C γ 0 L)
    (hmin : IsLengthMinimizing g γ)
    (hunit : ∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1)
    (F : NormalParallelFrame g C R γ L) :
    0 ≤ ∑ i, indexForm g C R γ 0 L (sineField F i) (sineField F i) ∧
      (∑ i, indexForm g C R γ 0 L (sineField F i) (sineField F i)) ≤
        ((n : ℝ) - 1) * L / 2 * ((Real.pi / L) ^ 2 - k) := by
  classical
  have hncast : ((n-1 : ℕ) : ℝ) = (n : ℝ) - 1 := by
    simpa only [Nat.cast_one] using
      (Nat.cast_sub (R := ℝ) (show 1 ≤ n by omega))
  have hint (i : Fin (n-1)) := SecondVariation.indexIntegrand_intervalIntegrable g C R hL hγ.1
    (GeodesicCriticalityCorners.smooth_field_c1 (sineField_smooth F i))
    (GeodesicCriticalityCorners.smooth_field_c1 (sineField_smooth F i))
  refine ⟨Finset.sum_nonneg (fun i _ => ?_), ?_⟩
  · exact indexForm_nonneg_smooth g C hC R hR hL γ hγ hmin _
      (sineField_smooth F i) (sineField_endpoints hL F i).1 (sineField_endpoints hL F i).2
  · rw [← comparison_integral hL ((n : ℝ) - 1) k]
    simp only [indexForm]
    rw [← intervalIntegral.integral_finsetSum (fun i _ => hint i)]
    have hsum : IntervalIntegrable (fun t =>
        ∑ i, indexIntegrand g C R γ 0 L (sineField F i) (sineField F i) t) volume 0 L := by
      convert (IntervalIntegrable.sum Finset.univ (fun i _ => hint i)) using 1
      funext t
      simp only [Finset.sum_apply]
    have hmodel : Continuous (fun t : ℝ => ((n : ℝ) - 1) *
        ((Real.pi / L) ^ 2 * Real.cos (Real.pi / L * t) ^ 2 -
          k * Real.sin (Real.pi / L * t) ^ 2)) := by
      exact continuous_const.mul
        ((continuous_const.mul ((Real.continuous_cos.comp
          (continuous_const.mul continuous_id)).pow 2)).sub
          (continuous_const.mul ((Real.continuous_sin.comp
            (continuous_const.mul continuous_id)).pow 2)))
    apply intervalIntegral.integral_mono_on hL.le hsum (hmodel.intervalIntegrable 0 L)
    intro t ht
    rw [sum_sine_indexIntegrand g C R hL F ht, hncast]
    have hnorm := SmoothMetrics.tangentNorm_sq g (γ t) (segmentTangent S γ 0 L t)
    rw [hunit t ht, one_pow] at hnorm
    have hr := hRic (γ t) (segmentTangent S γ 0 L t)
    rw [← hnorm, mul_one] at hr
    have hh := mul_le_mul_of_nonneg_left hr (sq_nonneg (Real.sin (Real.pi / L * t)))
    nlinarith

/-- Unit speed identifies the parameter length with the canonical integral
length, although the chosen ordinary velocity may differ at the endpoints. -/
theorem unit_segment_length (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    {L : ℝ} (hL : 0 < L) (γ : PiecewiseC1Curve S 0 L)
    (hγ : IsAffineGeodesicSegment C γ 0 L)
    (hunit : ∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1) :
    length g γ = L := by
  have ha := hunit 0 (left_mem_Icc.mpr hL.le)
  have hae := MinimizingIndexForm.geodesic_speed_ae_constant g C hC hL hγ
  rw [ha] at hae
  change (∫ t in (0 : ℝ)..L, speed g γ t) = L
  rw [intervalIntegral.integral_of_le hL.le, MeasureTheory.integral_congr_ae hae]
  simp [Real.volume_real_Ioc_of_le hL.le]

/-- All segment comparison work after construction of the normal frame. -/
theorem segment_bound_of_frames :
    P202Specs.Geometry.MyersDiameterCompact.segment_bound_of_framesType.{u} := by
  intro n M _ S g C hC R hR hn hframes k hk hRic L hL γ hγ hmin hunit
  obtain ⟨F⟩ := hframes hL γ hγ hunit
  obtain ⟨h0,h1⟩ := index_comparison g C hC R hR hn hL hRic γ hγ hmin hunit F
  have hb := bound_of_scalar_comparison hn hL hk (h0.trans h1)
  exact ⟨hb, (unit_segment_length g C hC hL γ hγ hunit).le.trans hb⟩

/-- Bridge from an actual geodesic phase to the one-sided segment tangent.
This uses uniqueness of actual coordinate derivatives, including the ends. -/
theorem segmentTangent_eq_phase (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {a b : ℝ} (hab : a < b)
    (hdom : Icc a b ⊆ I.carrier) {t : ℝ} (ht : t ∈ Icc a b) :
    segmentTangent S (fun r => (q r).1) a b t = (q t).2 := by
  have hF := GeodesicCriticalityCorners.smooth_curve_constant_variation
    (GeodesicCriticalityCorners.geodesic_position_smoothCurveOn C I q hq hdom)
    (ε := (1 : ℝ)) Subset.rfl
  have hV := (hq t (hdom ht)).1
  have hV' : HasVelocityWithinAt S (fun r => (q r).1) (Icc a b) t (q t).2 := by
    obtain ⟨hc,e,he,hp,hd⟩ := hV
    exact ⟨hc.mono (subset_univ _),e,he,hp,hd.mono (subset_univ _)⟩
  exact CurveCovariantDerivative.velocity_unique ht (uniqueDiffOn_Icc hab t ht)
    (FirstVariation.segmentVelocity_spec hF zero_lt_one ht) hV'

/-- A genuine geodesic on an open time domain is an affine smooth segment
on every nondegenerate compact subinterval of that domain. -/
theorem affineSegment_of_geodesic (C : Connection (tangentBundle S))
    (I : D13Unified.OpenTimeInterval) (q : ℝ → Phase S)
    (hq : IsGeodesicOn S C I.carrier q) {a b : ℝ} (hab : a < b)
    (hdom : Icc a b ⊆ I.carrier) :
    IsAffineGeodesicSegment C (fun r => (q r).1) a b := by
  refine ⟨GeodesicCriticalityCorners.smooth_curve_constant_variation
    (GeodesicCriticalityCorners.geodesic_position_smoothCurveOn C I q hq hdom)
      Subset.rfl, ?_⟩
  intro t ht
  exact SecondVariation.hasCovariantDerivativeWithinAt_congr_field C ht
    (GeodesicCriticalityCorners.covariantDerivativeWithin_of_at C (hq t (hdom ht)).2)
    (fun r hr => segmentTangent_eq_phase C I q hq hab hdom hr)

/-- Hopf--Rinow and the existing affine change of geodesic time produce an
actual minimizing unit-speed segment whose parameter length is the distance.
The zero-distance case is excluded here and handled separately downstream. -/
theorem unit_minimizer [ConnectedSpace M] (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hc : LengthMetricComplete g) (p q : M) (hpq : p ≠ q) :
    ∃ γ : PiecewiseC1Curve S 0 (lengthDistance g p q),
      γ 0 = p ∧ γ (lengthDistance g p q) = q ∧
      IsAffineGeodesicSegment C γ 0 (lengthDistance g p q) ∧
      IsLengthMinimizing g γ ∧
      ∀ t ∈ Icc 0 (lengthDistance g p q),
        tangentNorm g (γ t) (segmentTangent S γ 0 (lengthDistance g p q) t) = 1 := by
  have hdpos : 0 < lengthDistance g p q :=
    lt_of_le_of_ne (CompleteExponentialMinimizers.lengthDistance_nonneg g p q)
      (Ne.symm (fun h => hpq ((CompleteExponentialMinimizers.lengthDistance_eq_zero_iff g p q).mp h)))
  obtain ⟨F,hF⟩ := ExponentialNormalCoordinates.family_exists S C
  have hgeoComplete := (HopfRinow.hopf_rinow S g C hC).1.mp hc
  have hfull := HopfRinow.full_exponential_of_geodesicallyComplete C hgeoComplete F hF p
  obtain ⟨v,η,hη0,hη1,hexp,htrace,hradial,hgeo,hlen,hdist,hmin,hzero⟩ :=
    (HopfRinow.complete_conclusions g C hC hc F hF p).1 q
  have hv : tangentNorm g p v = lengthDistance g p q := hlen.symm.trans hdist
  have hshift :=
    CompleteExponentialMinimizers.shifted_unit_segment g C hC F hF p v
      (lengthDistance g p q) 0 hdpos hv (hfull v)
  simp only [zero_add] at hshift
  obtain ⟨I,r,σ,hr,hdom,hstart,hend,hunit,hγ,hlenσ⟩ := hshift
  let γ : PiecewiseC1Curve S 0 (lengthDistance g p q) := {
    ordered := by simpa only [zero_add] using σ.ordered
    toFun := σ
    continuousOn := by simpa only [zero_add] using σ.continuousOn
    pieces := σ.pieces
    node := σ.node
    monotone_node := σ.monotone_node
    first_node := σ.first_node
    last_node := by simpa only [zero_add] using σ.last_node
    regular := σ.regular }
  have hlenγ : length g γ = lengthDistance g p q := by
    simpa only [length, γ, zero_add] using hlenσ
  have hγfun : (γ : ℝ → M) = fun t => (r t).1 := funext hγ
  have ha : γ 0 = p := (hγ 0).trans (congrArg (fun z : Phase S => z.1) hstart)
  have hb : γ (lengthDistance g p q) = q :=
    (hγ _).trans (hend.trans hexp)
  refine ⟨γ,ha,hb,?_,?_,?_⟩
  · rw [hγfun]
    exact affineSegment_of_geodesic C I r hr hdpos hdom
  · intro a b σ hσ0 hσ1
    rw [hlenγ]
    have h := CompleteExponentialMinimizers.lengthDistance_le_length g σ
    rwa [hσ0,hσ1,ha,hb] at h
  · rw [hγfun]
    intro t ht
    rw [segmentTangent_eq_phase C I r hr hdpos hdom ht]
    exact hunit t (hdom ht)

/-- The passage from minimizing segment lengths to pairwise distances has no
curvature premise of its own. Equal endpoints require no positive-length path. -/
theorem distance_bound_of_segment_bound [ConnectedSpace M] (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hc : LengthMetricComplete g) {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ {L : ℝ}, 0 < L → ∀ γ : PiecewiseC1Curve S 0 L,
      IsAffineGeodesicSegment C γ 0 L → IsLengthMinimizing g γ →
      (∀ t ∈ Icc 0 L, tangentNorm g (γ t) (segmentTangent S γ 0 L t) = 1) → L ≤ B) :
    ∀ p q : M, lengthDistance g p q ≤ B := by
  intro p q
  by_cases hpq : p = q
  · subst q
    rw [CompleteExponentialMinimizers.lengthDistance_self]
    exact hB
  · have hdpos : 0 < lengthDistance g p q :=
      lt_of_le_of_ne (CompleteExponentialMinimizers.lengthDistance_nonneg g p q)
        (Ne.symm (fun h => hpq ((CompleteExponentialMinimizers.lengthDistance_eq_zero_iff g p q).mp h)))
    obtain ⟨γ,_,_,hγ,hmin,hunit⟩ := unit_minimizer g C hC hc p q hpq
    exact hbound hdpos γ hγ hmin hunit

/-- The supremum of all original distances has the same bound. -/
theorem diameter_bound_of_distance_bound [Nonempty M] (g : RiemannianMetric S)
    {B : ℝ} (hB : ∀ p q : M, lengthDistance g p q ≤ B) :
    lengthDiameter g ≤ B := by
  apply csSup_le (Set.range_nonempty _)
  rintro x ⟨⟨p,q⟩,rfl⟩
  exact hB p q

/-- Compactness is deduced from the bound and Hopf--Rinow; it is never a
premise of the curvature or segment estimate. -/
theorem compact_of_distance_bound [ConnectedSpace M] (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (hc : LengthMetricComplete g) {B : ℝ}
    (hB : ∀ p q : M, lengthDistance g p q ≤ B) : IsCompact (univ : Set M) := by
  obtain ⟨p⟩ := (inferInstance : Nonempty M)
  have hproper := (HopfRinow.hopf_rinow S g C hC).2.1.mp hc p
  exact hproper univ isClosed_univ ⟨B,fun q _ => hB p q⟩

/-- The global comparison argument after a normal frame has been constructed.
The unconditional theorem below discharges the frame premise. -/
theorem diameter_compact_of_frames :
    P202Specs.Geometry.MyersDiameterCompact.diameter_compact_of_framesType.{u} := by
  intro n M _ _ S g C hC R hR hn hframes k hk hRic hc
  have hB : ∀ p q : M, lengthDistance g p q ≤ Real.pi / Real.sqrt k :=
    distance_bound_of_segment_bound g C hC hc (by positivity)
      (fun {L} hL γ hγ hmin hunit =>
        (segment_bound_of_frames g C hC R hR hn hframes k hk hRic hL γ hγ hmin hunit).1)
  exact ⟨hB,diameter_bound_of_distance_bound g hB,compact_of_distance_bound g C hC hc hB⟩

end P202.Geometry.MyersDiameterCompact



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
namespace P202.Geometry.MyersDiameterCompact
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.BundleData SmoothManifolds.FrameData
  P202.MetricData P202.CurveData P202.ConnectionData P202.CurveConnectionData
  P202.LeviCivitaData P202.CurvatureData P202.RicciData P202.FirstVariationData
  P202.GeodesicData P202.SecondVariationData P202.CriticalityData P202.ParallelData P202.MyersData
open Set Filter
open scoped Topology
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

theorem exists_orthonormal_basis_first (g : RiemannianMetric S) (p : M)
    (hn : 0 < n) (v : TangentSpace S p) (hv : pairing g p v v = 1) :
    ∃ b : Module.Basis (Fin n) ℝ (TangentSpace S p),
      IsOrthonormalBasis g p b ∧ b ⟨0, hn⟩ = v := by
  classical
  letI : AddCommGroup (TangentSpace S p) := Module.addCommMonoidToAddCommGroup ℝ
  letI : InnerProductSpace.Core ℝ (TangentSpace S p) := {
    inner := fun x y => pairing g p x y
    conj_inner_symm := fun x y => g.symmetric p y x
    re_inner_nonneg := fun x => by
      change 0 ≤ pairing g p x x
      by_cases hx : x = 0
      · subst x; simp [pairing]
      · exact le_of_lt (g.positive p x hx)
    add_left := fun x y z => (g.form p).map_add₂ x y z
    smul_left := fun x y c => (g.form p).map_smul₂ c x y
    definite := fun x hx => by
      by_contra h
      exact (ne_of_gt (g.positive p x h)) hx }
  letI := InnerProductSpace.Core.toNormedAddCommGroup (𝕜 := ℝ) (F := TangentSpace S p)
  letI := InnerProductSpace.ofCore (inferInstance : PreInnerProductSpace.Core ℝ (TangentSpace S p))
  letI := SmoothManifolds.ConstantRankBundles.finite_fiber (tangentBundle S) p
  let i₀ : Fin n := ⟨0, hn⟩
  have horth : Orthonormal ℝ (({i₀} : Set (Fin n)).domRestrict (fun _ => v)) := by
    rw [orthonormal_iff_ite]
    intro i j
    have hij : i = j := by apply Subtype.ext; simpa using i.property.trans j.property.symm
    simp only [hij, ↓reduceIte]
    exact hv
  obtain ⟨b, hb⟩ := horth.exists_orthonormalBasis_extension_of_card_eq
    (by simpa using SmoothManifolds.ConstantRankBundles.finrank_fiber (tangentBundle S) p)
  refine ⟨b.toBasis, ?_, hb i₀ (by simp)⟩
  intro i j
  exact b.inner_eq_ite i j


theorem normal_frames_from_smooth_parallel
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (hC : IsLeviCivita g C) (R : CurvatureTensor S)
    (hR : RepresentsCurvature C R) (hn : 0 < n)
    (hsmooth : ∀ {L : ℝ}, 0 < L → ∀ (γ : ℝ → M),
      IsAffineGeodesicSegment C γ 0 L →
      ∀ f : (t : ℝ) → TangentSpace S (γ t),
        (∀ t ∈ Icc 0 L, HasCovariantDerivativeWithinAt C γ f (Icc 0 L) t 0) →
        SmoothFieldAlongOn S γ f (Icc 0 L))
    (hpair : ∀ {L : ℝ}, 0 < L → ∀ (γ : ℝ → M),
      IsAffineGeodesicSegment C γ 0 L →
      ∀ f : (t : ℝ) → TangentSpace S (γ t),
        (∀ t ∈ Icc 0 L, HasCovariantDerivativeWithinAt C γ f (Icc 0 L) t 0) →
        ∀ t ∈ Icc 0 L,
          pairing g (γ t) (f t) (segmentTangent S γ 0 L t) =
            pairing g (γ 0) (f 0) (segmentTangent S γ 0 L 0)) :
    NormalFramesExist g C R := by
  classical
  cases n with
  | zero => omega
  | succ m =>
    intro L hL γ hγ hunit
    have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by constructor <;> norm_num
    let c : PiecewiseC1Curve S 0 L :=
      FirstVariation.variationSlice hγ.1 h0 hL.le
    let s₀ : Icc (0 : ℝ) L := ⟨0, le_rfl, hL.le⟩
    let T := segmentTangent S γ 0 L
    have hnorm (t : ℝ) (ht : t ∈ Icc 0 L) : pairing g (γ t) (T t) (T t) = 1 := by
      have h := SmoothMetrics.tangentNorm_sq g (γ t) (T t)
      rw [hunit t ht] at h
      simpa using h.symm
    obtain ⟨b, hb, hb0⟩ := exists_orthonormal_basis_first g (γ 0)
      (Nat.succ_pos m) (T 0) (hnorm 0 s₀.property)
    let E (i : Fin (m+1)) : (t : ℝ) → TangentSpace S (γ t) :=
      selectedField C c s₀ (b i)
    have hEpar (i : Fin (m+1)) : ParallelField C c (E i) :=
      (ParallelTransport.selectedField_parallel C c s₀ (b i)).1
    have hEinit (i : Fin (m+1)) : E i 0 = b i :=
      (ParallelTransport.selectedField_parallel C c s₀ (b i)).2
    have hEd (i : Fin (m+1)) (t : ℝ) (ht : t ∈ Icc 0 L) :
        HasCovariantDerivativeWithinAt C γ (E i) (Icc 0 L) t 0 :=
      by
        have hd := (hEpar i).2.2 ⟨0, by change 0 < 1; norm_num⟩
        dsimp only [c, FirstVariation.variationSlice] at hd
        exact hd hL t ht
    have hEorth (t : ℝ) (ht : t ∈ Icc 0 L) (i j : Fin (m+1)) :
        pairing g (γ t) (E i t) (E j t) = if i = j then 1 else 0 := by
      exact (ParallelTransport.transport_isometry C g hC.2 c s₀ ⟨t, ht⟩ (b i) (b j)).trans (hb i j)
    have hEtan (i : Fin (m+1)) (t : ℝ) (ht : t ∈ Icc 0 L) :
        pairing g (γ t) (E i t) (T t) = if i = 0 then 1 else 0 := by
      rw [hpair hL γ hγ (E i) (hEd i) t ht, hEinit i]
      change pairing g (γ 0) (b i) (T 0) = _
      rw [← hb0]
      exact hb i 0
    have hEzero (t : ℝ) (ht : t ∈ Icc 0 L) : E 0 t = T t := by
      have h₁ := hEorth t ht 0 0
      have h₂ := hEtan 0 t ht
      simp only [↓reduceIte] at h₁ h₂
      have hsym := g.symmetric (γ t) (T t) (E 0 t)
      change pairing g (γ t) (T t) (E 0 t) = pairing g (γ t) (E 0 t) (T t) at hsym
      have hzero : pairing g (γ t) (E 0 t - T t) (E 0 t - T t) = 0 := by
        simp only [LeviCivita.tangent_sub_as_add, pairing, map_add, map_smul,
          LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
        change pairing g (γ t) (E 0 t) (E 0 t) + (-1) * pairing g (γ t) (T t) (E 0 t) +
          (-1) * (pairing g (γ t) (E 0 t) (T t) + (-1) * pairing g (γ t) (T t) (T t)) = 0
        rw [h₁, h₂, hsym, h₂, hnorm t ht]
        norm_num
      apply sub_eq_zero.mp
      by_contra hne
      exact (ne_of_gt (g.positive (γ t) _ hne)) hzero
    let e (t : Icc (0 : ℝ) L) : TangentSpace S (γ 0) ≃ₗ[ℝ] TangentSpace S (γ t) :=
      Classical.choose (ParallelTransport.transport_equiv C c s₀ t)
    have he (t : Icc (0 : ℝ) L) (v : TangentSpace S (γ 0)) :
        e t v = transport C c s₀ t v :=
      (Classical.choose_spec (ParallelTransport.transport_equiv C c s₀ t)).1 v
    let bt (t : Icc (0 : ℝ) L) : Module.Basis (Fin (m+1)) ℝ (TangentSpace S (γ t)) :=
      b.map (e t)
    have hbt (t : Icc (0 : ℝ) L) (i : Fin (m+1)) : bt t i = E i t := he t (b i)
    have hbtorth (t : Icc (0 : ℝ) L) : IsOrthonormalBasis g (γ t) (bt t) := by
      intro i j
      rw [hbt t i, hbt t j]
      exact hEorth t t.property i j
    refine ⟨{
      field := fun i => E i.succ
      smooth := fun i => hsmooth hL γ hγ (E i.succ) (hEd i.succ)
      parallel := fun i => hEd i.succ
      orthonormal := ?_
      normal := ?_
      trace := ?_ }⟩
    · intro t ht i j
      simpa only [Fin.succ_inj] using hEorth t ht i.succ j.succ
    · intro t ht i
      simpa only [Fin.succ_ne_zero, ↓reduceIte] using hEtan i.succ t ht
    · intro t ht
      have htrace := (RicciScalarBianchi.orthonormal_contractions g R (γ t)
        (bt ⟨t, ht⟩) (hbtorth ⟨t, ht⟩)).1 (T t) (T t)
      simp_rw [hbt] at htrace
      rw [Fin.sum_univ_succ, hEzero t ht] at htrace
      have hz := CurvatureAlgebra.form_self_first C g R hR (γ t) (T t) (T t) (T t)
      change curvatureForm g R (γ t) (T t) (T t) (T t) (T t) = 0 at hz
      rw [hz, zero_add] at htrace
      exact htrace.symm

end P202.Geometry.MyersDiameterCompact

namespace P202.Geometry.MyersDiameterCompact
open SmoothManifolds.AtlasData SmoothManifolds.TangentData
  P202.MetricData P202.ConnectionData P202.LeviCivitaData P202.CurvatureData
  P202.SecondVariationData P202.CriticalityData P202.MyersData
open Set
universe u
variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

/-- Parallel transport of an orthonormal basis with first member the tangent
constructs the smooth normal frame, without completeness or a Ricci bound. -/
theorem normal_frames_exist (g : RiemannianMetric S)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R) (hn : 2 ≤ n) :
    NormalFramesExist g C R := by
  apply normal_frames_from_smooth_parallel g C hC R hR (by omega)
  · intro L hL γ hγ f hf
    exact MyersRegularity.parallel_field_smooth C hL
      (GeodesicCriticalityCorners.smooth_field_base_smooth
        (GeodesicCriticalityCorners.smooth_segmentVelocity hγ.1 zero_lt_one hL)) hf
  · intro L hL γ hγ f hf t ht
    exact parallel_tangent_pairing_constant g C hC hL hγ hf t ht

/-- Bonnet--Myers for every positive-length unit-speed minimizing segment,
with no frame-existence premise. -/
theorem segment_bound :
    P202Specs.Geometry.MyersDiameterCompact.segment_boundType.{u} := by
  intro n M _ S g C hC R hR hn k hk hRic L hL γ hγ hmin hunit
  exact segment_bound_of_frames g C hC R hR hn
    (normal_frames_exist g C hC R hR hn) k hk hRic hL γ hγ hmin hunit

/-- The sharp pairwise and diameter bounds and compactness under the original
completeness and curvature assumptions. -/
theorem diameter_compact :
    P202Specs.Geometry.MyersDiameterCompact.diameter_compactType.{u} := by
  intro n M _ _ S g C hC R hR hn k hk hRic hc
  exact diameter_compact_of_frames S g C hC R hR hn
    (normal_frames_exist g C hC R hR hn) k hk hRic hc

end P202.Geometry.MyersDiameterCompact
