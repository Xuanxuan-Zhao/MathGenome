import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Geometry.PolarDensityComparison
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.PolarVolumeDensity
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Geometry.ConstantCurvaturePolar
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Module
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Topology ENNReal

namespace P202.Geometry.PolarDensityComparison
open SmoothManifolds.ModelData SmoothManifolds.AtlasData SmoothManifolds.TangentData
  SmoothManifolds.MaximalFlowData P202.MetricData P202.ConnectionData
  P202.CurveConnectionData P202.LeviCivitaData P202.GeodesicData P202.CurvatureData
  P202.ExponentialData P202.JacobiMatrixData P202.RicciData P202.CompletenessData
  P202.CutTimeData P202.PolarVolumeData P202.ConstantCurvaturePolarData
  P202.PolarComparisonData
open Set Filter Module
universe u

lemma model_positive {k t : ℝ} (ht : t ∈ comparisonInterval k) : 0 < s k t := by
  by_cases hk : 0 < k
  · have hs := Real.sqrt_pos.mpr hk
    exact (by
      rw [s, ite_eq_left hk]
      exact div_pos (Real.sin_pos_of_pos_of_lt_pi (mul_pos hs ht.1)
        (by simpa only [mul_comm] using (lt_div_iff₀ hs).mp (ht.2 hk))) hs)
  · by_cases hz : k = 0
    · simpa [s, hk, hz] using ht.1
    · rw [s, ite_eq_right hk, ite_eq_right hz]
      have hs : 0 < Real.sqrt (-k) := Real.sqrt_pos.mpr (by
        exact neg_pos.mpr (lt_of_le_of_ne (le_of_not_gt hk) hz))
      exact div_pos (Real.sinh_pos_iff.mpr (mul_pos hs ht.1)) hs

lemma model_normalization (k : ℝ) :
    Tendsto (fun t => s k t / t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have h := (ConstantCurvaturePolar.s_derivative k 0).tendsto_slope_zero_right
  simpa [ConstantCurvaturePolar.s_zero, ConstantCurvaturePolar.c_zero,
    smul_eq_mul, div_eq_mul_inv, mul_comm] using h

lemma comparisonInterval_eventually (k : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ comparisonInterval k := by
  by_cases hk : 0 < k
  · have hr : 0 < Real.pi / Real.sqrt k := div_pos Real.pi_pos (Real.sqrt_pos.mpr hk)
    filter_upwards [self_mem_nhdsWithin,
      Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hr)] with t ht htr
    exact ⟨ht, fun _ => htr⟩
  · filter_upwards [self_mem_nhdsWithin] with t ht
    exact ⟨ht, fun h => False.elim (hk h)⟩


/-- Elementary trace Cauchy--Schwarz for a real symmetric matrix. Its
 application to U is justified separately by actual metric self-adjointness. -/
lemma matrix_trace_square {r : ℕ} (A : Matrix (Fin r) (Fin r) ℝ)
    (hA : ∀ i j, A i j = A j i) :
    Matrix.trace A ^ 2 ≤ (r : ℝ) * Matrix.trace (A * A) := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun _ : Fin r => (1 : ℝ)) (fun i => A i i)
  have hdiag : (∑ i, A i i ^ 2) ≤ Matrix.trace (A * A) := by
    unfold Matrix.trace
    apply Finset.sum_le_sum
    intro i _
    simp only [Matrix.diag_apply, Matrix.mul_apply]
    calc
      A i i ^ 2 ≤ ∑ j, A i j ^ 2 :=
        Finset.single_le_sum (fun j _ => sq_nonneg (A i j)) (Finset.mem_univ i)
      _ = ∑ j, A i j * A j i := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← hA i j, pow_two]
  have hh : Matrix.trace A ^ 2 ≤ (r : ℝ) * ∑ i, A i i ^ 2 := by
    simpa [Matrix.trace] using hcs
  exact hh.trans (mul_le_mul_of_nonneg_left hdiag (Nat.cast_nonneg r))

lemma trace_normal {V : Type*} [AddCommGroup V] [Module ℝ V]
    [Module.Free ℝ V] [Module.Finite ℝ V]
    {r : ℕ} (B : LinearMap.BilinForm ℝ V) (T : V) (hT : B T T = 1)
    (F : (Fin r → ℝ) →ₗ[ℝ] V)
    (horth : ∀ x y, B (F x) (F y) = ∑ i, x i * y i)
    (hnorm : ∀ w, (∃ x, F x = w) ↔ B w T = 0)
    (K : V →ₗ[ℝ] V) (A : (Fin r → ℝ) →ₗ[ℝ] (Fin r → ℝ))
    (hKT : K T = 0) (hKF : ∀ x, K (F x) = F (A x)) :
    LinearMap.trace ℝ V K = LinearMap.trace ℝ (Fin r → ℝ) A := by
  classical
  let P : V →ₗ[ℝ] (Fin r → ℝ) := LinearMap.pi (fun i => B (F (Pi.single i 1)))
  have hPF (x : Fin r → ℝ) : P (F x) = x := by
    ext i
    change B (F (Pi.single i 1)) (F x) = x i
    rw [horth]
    simp [Pi.single_apply]
  have hPT : P T = 0 := by
    ext i
    exact (hnorm (F (Pi.single i 1))).mp ⟨_, rfl⟩
  have hK : K = (F.comp A).comp P := by
    ext w
    have hw : B (w - (B w T) • T) T = 0 := by
      simp only [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.smul_left, hT,
        mul_one, sub_self]
    obtain ⟨x, hx⟩ := (hnorm _).mpr hw
    have hw' : w = F x + (B w T) • T := by
      rw [hx]
      module
    rw [hw', map_add, map_smul, hKT, smul_zero, add_zero, hKF]
    change F (A x) = F (A (P (F x + (B w T) • T)))
    rw [map_add, map_smul, hPF, hPT, smul_zero, add_zero]
  rw [hK, LinearMap.trace_comp_comm']
  have hh : P.comp (F.comp A) = A := LinearMap.ext (fun x => hPF (A x))
  rw [hh]

def operatorTrace (r : ℕ) : Operator r →L[ℝ] ℝ :=
  ({ toFun := fun U => LinearMap.trace ℝ (Euclidean r) U.toLinearMap
     map_add' := by intro x y; simp
     map_smul' := by intro c x; simp } : Operator r →ₗ[ℝ] ℝ).toContinuousLinearMap

lemma operatorTrace_apply {r : ℕ} (U : Operator r) :
    operatorTrace r U = LinearMap.trace ℝ (Euclidean r) U.toLinearMap := rfl

lemma scaled_inverse {r : ℕ} (A : Operator r) (t : ℝ) (ht : t ≠ 0)
    (hX : IsUnit (t⁻¹ • A)) :
    Ring.inverse (t⁻¹ • A) = t • Ring.inverse A := by
  have htu : IsUnit (algebraMap ℝ (Operator r) t) :=
    (isUnit_iff_ne_zero.mpr ht).map (algebraMap ℝ (Operator r))
  have hu : IsUnit A := by
    convert htu.mul hX using 1
    rw [← Algebra.smul_def, smul_smul, mul_inv_cancel₀ ht, one_smul]
  have he : (t⁻¹ • A) * (t • Ring.inverse A) = 1 := by
    rw [smul_mul_smul_comm, inv_mul_cancel₀ ht, one_smul,
      Ring.mul_inverse_cancel A hu]
  calc
    Ring.inverse (t⁻¹ • A) = Ring.inverse (t⁻¹ • A) * 1 := by rw [mul_one]
    _ = Ring.inverse (t⁻¹ • A) * ((t⁻¹ • A) * (t • Ring.inverse A)) := by rw [he]
    _ = t • Ring.inverse A := Ring.inverse_mul_cancel_left _ _ hX

lemma normalized_riccati_limit {n r : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : Connection (tangentBundle S)}
    {R : CurvatureTensor S} {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (h0 : 0 ∈ I.carrier) :
    Tendsto (fun t => t • riccati D t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hA := (D.derivatives 0 h0).1.tendsto_slope_zero_right
  simp only [zero_add, D.initial_A, sub_zero, D.initial_B] at hA
  have hB : Tendsto D.B (𝓝[>] (0 : ℝ)) (𝓝 (1 : Operator r)) := by
    simpa only [D.initial_B] using
      (D.derivatives 0 h0).2.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hInv := (NormedRing.inverse_continuousAt (1 : (Operator r)ˣ)).tendsto.comp hA
  simp only [Units.val_one, Ring.inverse_one] at hInv
  have hh := hB.mul hInv
  simp only [one_mul] at hh
  have hunit : ∀ᶠ t in 𝓝[>] (0 : ℝ), IsUnit (t⁻¹ • D.A t) :=
    hA.eventually (Units.isOpen.mem_nhds isUnit_one)
  apply hh.congr'
  filter_upwards [hunit, self_mem_nhdsWithin] with t ht htpos
  simp only [Function.comp_apply]
  rw [scaled_inverse (D.A t) t (ne_of_gt (show 0 < t from htpos)) ht]
  simp only [riccati, mul_smul_comm]


lemma trace_riccati_initial {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M} {C : Connection (tangentBundle S)}
    {R : CurvatureTensor S} {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q (n - 1)) (h0 : 0 ∈ I.carrier) (hn : 2 ≤ n) :
    Tendsto (fun t => t * (LinearMap.trace ℝ (Euclidean (n - 1))
      (riccati D t).toLinearMap / (n - 1 : ℕ))) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hh := (operatorTrace (n - 1)).continuous.tendsto 1 |>.comp
    (normalized_riccati_limit D h0)
  have htr : Tendsto (fun t => t * LinearMap.trace ℝ (Euclidean (n - 1))
      (riccati D t).toLinearMap) (𝓝[>] (0 : ℝ)) (𝓝 (n - 1 : ℕ)) := by
    simpa [Function.comp_def, map_smul, smul_eq_mul, operatorTrace_apply, Module.finrank_pi] using hh
  have hm : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  simpa [mul_div_assoc, div_self hm] using htr.div_const ((n - 1 : ℕ) : ℝ)

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  {S : SmoothManifold n .euclidean M}

lemma ratio_initial_limit [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) (k : ℝ) :
    Tendsto (densityRatio g F p v k) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hj := (PolarVolumeDensity.regularity S g hn hc C hC R hR F hF p).1 v
  have hmod := (model_normalization k).pow (n - 1)
  have hh := hj.div hmod (by simp : (1 : ℝ) ^ (n - 1) ≠ 0)
  simp only [one_pow, div_one] at hh
  apply hh.congr'
  filter_upwards [self_mem_nhdsWithin, comparisonInterval_eventually k] with t ht htk
  unfold densityRatio
  simp only [Pi.div_apply]
  rw [div_pow, div_div_div_cancel_right₀ (pow_ne_zero _ (ne_of_gt (show 0 < t from ht)))]

lemma truncatedRatio_eq (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k t : ℝ) (ht : 0 < t) :
    truncatedRatio g F p v k t =
      if ENNReal.ofReal t < cutTime g F p v then densityRatio g F p v k t else 0 := by
  classical
  by_cases hcut : ENNReal.ofReal t < cutTime g F p v
  · simp [truncatedRatio, truncatedDensity, polarDomain, ht, hcut, densityRatio]
  · simp [truncatedRatio, truncatedDensity, polarDomain, ht, hcut]

lemma truncatedRatio_nonneg (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k t : ℝ) (ht : t ∈ comparisonInterval k) :
    0 ≤ truncatedRatio g F p v k t :=
  div_nonneg (PolarVolumeDensity.truncatedDensity_nonneg g F p (t, v))
    (pow_nonneg (model_positive ht).le _)

lemma truncated_initial_limit [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) (k : ℝ) :
    Tendsto (truncatedRatio g F p v k) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
  have hcpos := (CutTime.cut_time_interval S g (by omega) hc C hC F hF p v).2.1
  have hcut : ∀ᶠ t in 𝓝 (0 : ℝ), ENNReal.ofReal t < cutTime g F p v := by
    have h : Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
    exact h.eventually (Iio_mem_nhds hcpos)
  apply (ratio_initial_limit g hn hc C hC R hR F hF p v k).congr'
  filter_upwards [self_mem_nhdsWithin, hcut.filter_mono nhdsWithin_le_nhds] with t ht htc
  exact ((truncatedRatio_eq g F p v k t ht).trans (ite_eq_left htc)).symm

theorem initial_limit : P202Specs.Geometry.PolarDensityComparison.initial_limitType.{u} := by
  intro n M _ _ S g hn hc C hC R hR k _ F hF p v
  exact ⟨ratio_initial_limit g hn hc C hC R hR F hF p v k,
    truncated_initial_limit g hn hc C hC R hR F hF p v k⟩


/-- Extending a nonnegative directionwise ratio by zero can only add a
 downward jump. This uses the actual ENNReal cut time, with no finiteness
 assumption. -/
lemma truncated_antitone_of_preCut (g : RiemannianMetric S)
    (F : CurveFamily (Phase S)) (p : M) (v : UnitDirection g p) (k : ℝ)
    (hmono : AntitoneOn (densityRatio g F p v k) (preCutInterval g F p v k)) :
    AntitoneOn (truncatedRatio g F p v k) (comparisonInterval k) := by
  intro a ha b hb hab
  rw [truncatedRatio_eq g F p v k a ha.1, truncatedRatio_eq g F p v k b hb.1]
  by_cases hbc : ENNReal.ofReal b < cutTime g F p v
  · have hac := (ENNReal.ofReal_le_ofReal hab).trans_lt hbc
    rw [ite_eq_left hac, ite_eq_left hbc]
    exact hmono ⟨ha, hac⟩ ⟨hb, hbc⟩ hab
  · rw [ite_eq_right hbc]
    have hn := truncatedRatio_nonneg g F p v k a ha
    rwa [truncatedRatio_eq g F p v k a ha.1] at hn

lemma preCut_eventually [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) (k : ℝ) :
    ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ preCutInterval g F p v k := by
  have hcpos := (CutTime.cut_time_interval S g (by omega) hc C hC F hF p v).2.1
  have hcut : ∀ᶠ t in 𝓝 (0 : ℝ), ENNReal.ofReal t < cutTime g F p v := by
    have h : Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      simpa using ENNReal.continuous_ofReal.tendsto (0 : ℝ)
    exact h.eventually (Iio_mem_nhds hcpos)
  filter_upwards [comparisonInterval_eventually k,
    hcut.filter_mono nhdsWithin_le_nhds] with t ht htc
  exact ⟨ht, htc⟩

/-- The upper bound comes from monotonicity and the proved initial limit,
 rather than an extra hypothesis on the density. -/
lemma truncated_le_one_of_preCut [ConnectedSpace M]
    (g : RiemannianMetric S) (hn : 2 ≤ n) (hc : LengthMetricComplete g)
    (C : Connection (tangentBundle S)) (hC : IsLeviCivita g C)
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    (F : CurveFamily (Phase S)) (hF : IsMaximalFamily S C F)
    (p : M) (v : UnitDirection g p) (k : ℝ)
    (hmono : AntitoneOn (densityRatio g F p v k) (preCutInterval g F p v k))
    (t : ℝ) (ht : t ∈ comparisonInterval k) :
    truncatedRatio g F p v k t ≤ 1 := by
  apply ge_of_tendsto (truncated_initial_limit g hn hc C hC R hR F hF p v k)
  filter_upwards [comparisonInterval_eventually k,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds ht.1)] with a ha hat
  exact truncated_antitone_of_preCut g F p v k hmono ha ht hat.le

/-- The parent assembly only needs the still outstanding untruncated
 comparison; all cut-time and bound conclusions are established here. -/
theorem truncated_comparison_of_preCut
    (h : P202Specs.Geometry.PolarDensityComparison.preCut_comparisonType.{u}) :
    P202Specs.Geometry.PolarDensityComparison.truncated_comparisonType.{u} := by
  intro n M _ _ S g hn hc C hC R hR k hk F hF p v
  have hmono := h S g hn hc C hC R hR k hk F hF p v
  exact ⟨truncated_antitone_of_preCut g F p v k hmono, fun t ht =>
    ⟨truncatedRatio_nonneg g F p v k t ht,
      truncated_le_one_of_preCut g hn hc C hC R hR F hF p v k hmono t ht⟩⟩

lemma antitoneOn_of_local_derivative {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hf : ∀ t ∈ D, ∃ a, HasDerivAt f a t ∧ a ≤ 0) : AntitoneOn f D := by
  apply antitoneOn_of_deriv_nonpos hD
  · intro t ht
    obtain ⟨a, ha, _⟩ := hf t ht
    exact ha.continuousAt.continuousWithinAt
  · intro t ht
    obtain ⟨a, ha, _⟩ := hf t (interior_subset ht)
    exact ha.differentiableAt.differentiableWithinAt
  · intro t ht
    obtain ⟨a, ha, hle⟩ := hf t (interior_subset ht)
    rwa [ha.deriv]

lemma singular_riccati {D : Set ℝ} (hD : Convex ℝ D)
    (hD0 : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ D) (hDp : ∀ t ∈ D, 0 < t)
    (k : ℝ) (s c θ : ℝ → ℝ)
    (hs : ∀ t ∈ D, HasDerivAt s (c t) t)
    (hc : ∀ t ∈ D, HasDerivAt c (-k * s t) t)
    (hθ : ∀ t ∈ D, ∃ a, HasDerivAt θ a t ∧ a + θ t ^ 2 + k ≤ 0)
    (hsp : ∀ t ∈ D, 0 < s t)
    (hs0 : Tendsto s (𝓝[>] (0 : ℝ)) (𝓝 0))
    (hc0 : Tendsto c (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hst : Tendsto (fun t => s t / t) (𝓝[>] (0 : ℝ)) (𝓝 1))
    (hθt : Tendsto (fun t => t * θ t) (𝓝[>] (0 : ℝ)) (𝓝 1)) :
    ∀ t ∈ D, θ t ≤ c t / s t := by
  let W : ℝ → ℝ := fun t => s t ^ 2 * θ t - s t * c t
  have hW : AntitoneOn W D := by
    apply antitoneOn_of_local_derivative hD
    intro t ht
    obtain ⟨a, ha, hle⟩ := hθ t ht
    refine ⟨_, ((hs t ht).pow 2 |>.mul ha).sub ((hs t ht).mul (hc t ht)), ?_⟩
    have hh := mul_nonpos_of_nonneg_of_nonpos (sq_nonneg (s t)) hle
    simp only [Pi.pow_apply, Nat.reduceSub, pow_one, Nat.cast_ofNat]
    nlinarith [sq_nonneg (s t * θ t - c t)]
  have hstheta : Tendsto (fun t => s t * θ t) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    have hh := hst.mul hθt
    simp only [mul_one] at hh
    apply hh.congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : 0 < t := ht
    field_simp [ne_of_gt ht']
  have hW0 : Tendsto W (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have hh := hs0.mul (hstheta.sub hc0)
    simp only [sub_self, mul_zero] at hh
    convert hh using 1
    ext t
    dsimp [W]
    ring
  intro t ht
  have hle : W t ≤ 0 := by
    apply ge_of_tendsto hW0
    filter_upwards [hD0, Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds (hDp t ht))]
      with a ha hat
    exact hW ha ht hat.le
  have hstp := hsp t ht
  apply (le_div_iff₀ hstp).mpr
  dsimp [W] at hle
  nlinarith

lemma density_antitone_of_trace {D : Set ℝ} (hD : Convex ℝ D)
    (m : ℕ) (hm : 0 < m) (s c θ j : ℝ → ℝ)
    (hs : ∀ t ∈ D, HasDerivAt s (c t) t)
    (hj : ∀ t ∈ D, HasDerivAt j ((m : ℝ) * θ t * j t) t)
    (hsp : ∀ t ∈ D, 0 < s t) (hjp : ∀ t ∈ D, 0 ≤ j t)
    (hcomp : ∀ t ∈ D, θ t ≤ c t / s t) :
    AntitoneOn (fun t => j t / s t ^ m) D := by
  apply antitoneOn_of_local_derivative hD
  intro t ht
  have hst := hsp t ht
  have hd := (hj t ht).div ((hs t ht).pow m) (pow_ne_zero _ hst.ne')
  refine ⟨_, hd, ?_⟩
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
  have hpow : s t ^ m = s t ^ (m - 1) * s t := by
    rw [← pow_succ, Nat.sub_add_cancel hm]
  have hcomp' := (le_div_iff₀ hst).mp (hcomp t ht)
  have hprod : (m : ℝ) * j t * s t ^ (m - 1) * (θ t * s t - c t) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (hjp t ht))
        (pow_nonneg hst.le _)) (sub_nonpos.mpr hcomp')
  simp only [Pi.pow_apply] at *
  rw [hpow]
  nlinarith only [hprod]

lemma normal_curvature_trace {n : ℕ} {M : Type u} [TopologicalSpace M]
    {S : SmoothManifold n .euclidean M}
    (g : RiemannianMetric S) (C : Connection (tangentBundle S))
    (R : CurvatureTensor S) (hR : RepresentsCurvature C R)
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q (n - 1)) (hD : IsOrthonormalNormalFrame g D)
    (t : ℝ) (ht : t ∈ I.carrier)
    (hunit : pairing g (q t).1 (q t).2 (q t).2 = 1) :
    LinearMap.trace ℝ (Euclidean (n - 1)) (D.curvature t).toLinearMap =
      ricci R (q t).1 (q t).2 (q t).2 := by
  let : AddCommGroup (TangentSpace S (q t).1) := Module.addCommMonoidToAddCommGroup ℝ
  let := SmoothManifolds.ConstantRankBundles.finite_fiber (tangentBundle S) (q t).1
  let K : TangentSpace S (q t).1 →ₗ[ℝ] TangentSpace S (q t).1 := {
    toFun := fun w => R.val (q t).1 w (q t).2 (q t).2
    map_add' := by intros; simp only [map_add, LinearMap.add_apply]
    map_smul' := by intros; simp only [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hKT : K (q t).2 = 0 := by
    by_contra hne
    have hp := g.positive (q t).1 (K (q t).2) hne
    have hz := P202.Geometry.CurvatureAlgebra.form_self_first C g R hR (q t).1
      (q t).2 (q t).2 (K (q t).2)
    exact (ne_of_gt hp) hz
  have hh := trace_normal (pairing g (q t).1) (q t).2 hunit (D.frame t)
    (hD.1 t ht) (hD.2 t ht) K (D.curvature t).toLinearMap hKT
    (fun x => (D.curvature_eq t ht x).symm)
  exact hh.symm

lemma trace_square_of_self_adjoint {r : ℕ} (U : Operator r)
    (hU : ∀ x y, (∑ i, U x i * y i) = ∑ i, x i * U y i) :
    (LinearMap.trace ℝ (Euclidean r) U.toLinearMap) ^ 2 ≤
      (r : ℝ) * LinearMap.trace ℝ (Euclidean r) (U * U).toLinearMap := by
  classical
  let b := Pi.basisFun ℝ (Fin r)
  let A := LinearMap.toMatrix b b U.toLinearMap
  have hA : ∀ i j, A i j = A j i := by
    intro i j
    simpa [A, b, LinearMap.toMatrix_apply, Pi.single_apply] using
      hU (Pi.single j 1) (Pi.single i 1)
  have hh := matrix_trace_square A hA
  rw [LinearMap.trace_eq_matrix_trace ℝ b,
    LinearMap.trace_eq_matrix_trace ℝ b]
  change Matrix.trace A ^ 2 ≤ (r : ℝ) *
    Matrix.trace (LinearMap.toMatrix b b (U.toLinearMap * U.toLinearMap))
  rwa [LinearMap.toMatrix_mul]

lemma trace_riccati : P202Specs.Geometry.PolarDensityComparison.trace_riccatiType.{u} := by
  intro n M _ S g hn C hC R hR k hk I q hq h0 hunit D hD t ht hbij
  dsimp only
  let U := riccati D t
  let m : ℝ := (n - 1 : ℕ)
  have hm : 0 < m := Nat.cast_pos.mpr (by omega)
  have hcurv := normal_curvature_trace g C R hR D hD t ht (hunit t ht)
  have hself : ∀ x y, (∑ i, U x i * y i) = ∑ i, x i * U y i := by
    intro x y
    simpa only [hD.1 t ht] using
      P202.Geometry.JacobiMatrix.riccati_self_adjoint_of_bijective
        g C hC R hR I q hq h0 D t ht hbij x y
  have hsq := trace_square_of_self_adjoint U hself
  have hdU := P202.Geometry.JacobiMatrix.riccati_derivative_of_bijective D t ht hbij
  have hdtr := (operatorTrace (n - 1)).hasFDerivAt.comp_hasDerivAt t hdU
  have hdθ : HasDerivAt (meanTrace D)
      (-(LinearMap.trace ℝ (Euclidean (n - 1)) (U * U).toLinearMap +
        ricci R (q t).1 (q t).2 (q t).2) / m) t := by
    simpa [meanTrace, operatorTrace_apply, hcurv, m, U] using! hdtr.div_const m
  refine ⟨hcurv, hself, hsq, hdθ, ?_⟩
  have hRic := hk (q t).1 (q t).2
  rw [hunit t ht, mul_one] at hRic
  change -(LinearMap.trace ℝ (Euclidean (n - 1)) (U * U).toLinearMap +
      ricci R (q t).1 (q t).2 (q t).2) / m +
    (LinearMap.trace ℝ (Euclidean (n - 1)) U.toLinearMap / m) ^ 2 + k ≤ 0
  have he (a b c : ℝ) : -(b + c) / m + (a / m) ^ 2 + k =
      (a ^ 2 - m * b - m * c + k * m ^ 2) / m ^ 2 := by
    field_simp
    ring
  rw [he]
  apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg m)
  have hh := mul_le_mul_of_nonneg_left hRic hm.le
  change m * (m * k) ≤ m * ricci R (q t).1 (q t).2 (q t).2 at hh
  nlinarith only [hsq, hh]

lemma preCut_convex (g : RiemannianMetric S) (F : CurveFamily (Phase S))
    (p : M) (v : UnitDirection g p) (k : ℝ) :
    Convex ℝ (preCutInterval g F p v k) := by
  apply Set.OrdConnected.convex
  constructor
  intro a ha b hb t ht
  exact ⟨⟨lt_of_lt_of_le ha.1.1 ht.1, fun hk => ht.2.trans_lt (hb.1.2 hk)⟩,
    (ENNReal.ofReal_le_ofReal ht.2).trans_lt hb.2⟩

lemma determinant_derivative {r : ℕ}
    {C : Connection (tangentBundle S)} {R : CurvatureTensor S}
    {I : D13Unified.OpenTimeInterval} {q : ℝ → Phase S}
    (D : JacobiSystem S C R I q r) (t : ℝ) (ht : t ∈ I.carrier)
    (hbij : Function.Bijective (D.A t)) (hpos : 0 < LinearMap.det (D.A t).toLinearMap) :
    HasDerivAt (fun s => LinearMap.det (D.A s).toLinearMap)
      (LinearMap.trace ℝ (Euclidean r) (riccati D t).toLinearMap *
        LinearMap.det (D.A t).toLinearMap) t := by
  have hl := JacobiMatrix.logarithmic_determinant_derivative D t ht hbij hpos
  have hc := ContinuousLinearMap.continuous_det.continuousAt.comp
    (D.derivatives t ht).1.continuousAt
  have he := hl.exp
  rw [Real.exp_log hpos, mul_comm] at he
  apply he.congr_of_eventuallyEq
  have hp : ∀ᶠ s in 𝓝 t, 0 < LinearMap.det (D.A s).toLinearMap :=
    hc.eventually (Ioi_mem_nhds hpos)
  filter_upwards [hp] with s hs
  exact (Real.exp_log hs).symm

theorem preCut_comparison :
    P202Specs.Geometry.PolarDensityComparison.preCut_comparisonType.{u} := by
  intro n M _ _ S g hn hcomplete C hC R hR k hRic F hF p v
  let I := F.interval ⟨p, v.val⟩
  let q := F.curve ⟨p, v.val⟩
  let Dset := preCutInterval g F p v k
  have h0 : 0 ∈ I.carrier := (hF ⟨p, v.val⟩).1
  have hq : IsGeodesicOn S C I.carrier q := (hF ⟨p, v.val⟩).2.2.1
  obtain ⟨D, hD⟩ := PolarVolumeDensity.normal_frame_exists S g hn hcomplete C hC R hR F hF p v
  have hmem (t : ℝ) (ht : t ∈ Dset) : t ∈ I.carrier :=
    (CutCriterion.interior_unique_nonconjugate S g (by omega) hcomplete
      C hC R hR F hF p v t ht.1.1 ht.2).2.2.choose
  have hbij (t : ℝ) (ht : t ∈ Dset) : Function.Bijective (D.A t) := by
    obtain ⟨_, _, htI, hnc⟩ := CutCriterion.interior_unique_nonconjugate S g
      (by omega) hcomplete C hC R hR F hF p v t ht.1.1 ht.2
    exact JacobiMatrix.invertible S g C hC R hR I q hq h0 D t ht.1.1 htI hnc
  have hunit (t : ℝ) (ht : t ∈ I.carrier) :
      pairing g (q t).1 (q t).2 (q t).2 = 1 := by
    have hi : tangentNorm g (q 0).1 (q 0).2 = 1 := by
      dsimp only [q]
      rw [(hF ⟨p, v.val⟩).2.1]
      exact v.property
    have hv := GeodesicIVP.speed_is_constant g C hC I q hq ht h0
    rw [hi] at hv
    rw [← SmoothMetrics.tangentNorm_sq, hv, one_pow]
  have hmean (t : ℝ) (ht : t ∈ Dset) :
      ∃ a, HasDerivAt (meanTrace D) a t ∧ a + meanTrace D t ^ 2 + k ≤ 0 := by
    have hh := trace_riccati S g hn C hC R hR k hRic I q hq h0 hunit D hD
      t (hmem t ht) (hbij t ht)
    exact ⟨_, hh.2.2.2⟩
  have hconv : Convex ℝ Dset := preCut_convex g F p v k
  have hevent : ∀ᶠ t in 𝓝[>] (0 : ℝ), t ∈ Dset :=
    preCut_eventually g hn hcomplete C hC F hF p v k
  have hsp (t : ℝ) (ht : t ∈ Dset) : 0 < s k t := model_positive ht.1
  have hs0 : Tendsto (s k) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    simpa only [ConstantCurvaturePolar.s_zero] using
      (ConstantCurvaturePolar.s_derivative k 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hc0 : Tendsto (c k) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
    simpa only [ConstantCurvaturePolar.c_zero] using
      (ConstantCurvaturePolar.c_derivative k 0).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hθt : Tendsto (fun t => t * meanTrace D t) (𝓝[>] (0 : ℝ)) (𝓝 1) :=
    trace_riccati_initial D h0 hn
  have hcomp := singular_riccati hconv hevent (fun t ht => ht.1.1) k
    (s k) (c k) (meanTrace D)
    (fun t _ => ConstantCurvaturePolar.s_derivative k t)
    (fun t _ => ConstantCurvaturePolar.c_derivative k t)
    hmean hsp hs0 hc0 (model_normalization k) hθt
  let j := fun t => LinearMap.det (D.A t).toLinearMap
  have hjpos (t : ℝ) (ht : t ∈ Dset) : 0 < j t :=
    PolarVolumeDensity.system_positive S g hn hcomplete C hC R hR F hF p v D
      t ht.1.1 ht.2
  have hjderiv (t : ℝ) (ht : t ∈ Dset) :
      HasDerivAt j ((n - 1 : ℕ) * meanTrace D t * j t) t := by
    have hh := determinant_derivative D t (hmem t ht) (hbij t ht) (hjpos t ht)
    have hm : ((n - 1 : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    simpa only [meanTrace, mul_div_cancel₀ _ hm] using hh
  have hmono := density_antitone_of_trace hconv (n - 1) (by omega)
    (s k) (c k) (meanTrace D) j
    (fun t _ => ConstantCurvaturePolar.s_derivative k t) hjderiv hsp
    (fun t ht => (hjpos t ht).le) hcomp
  intro a ha b hb hab
  change radialDensity g F p (b, v) / s k b ^ (n - 1) ≤
    radialDensity g F p (a, v) / s k a ^ (n - 1)
  rw [(PolarVolumeDensity.jacobi_density S g hn hcomplete C hC R hR F hF
      p v D hD b hb.1.1 hb.2).1,
    (PolarVolumeDensity.jacobi_density S g hn hcomplete C hC R hR F hF
      p v D hD a ha.1.1 ha.2).1]
  exact hmono ha hb hab

theorem truncated_comparison :
    P202Specs.Geometry.PolarDensityComparison.truncated_comparisonType.{u} :=
  truncated_comparison_of_preCut preCut_comparison

end P202.Geometry.PolarDensityComparison
