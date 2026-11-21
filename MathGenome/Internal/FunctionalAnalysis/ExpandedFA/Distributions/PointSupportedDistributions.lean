import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Distributions.PointSupportedDistributions
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionFiniteOrder
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.DistributionLocalizationAndGluing
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Analysis.Calculus.MeanValue

open Set TopologicalSpace
open scoped Distributions Topology

namespace ExpandedFA.Distributions

variable {𝕜 : Type} [RCLike 𝕜] {d : ℕ} {Ω : Opens (Domain d)}

@[simp] theorem coordinateJet_apply (a : Domain d) {k : ℕ} (w : Fin k → Fin d)
    (φ : Tests 𝕜 Ω) :
    coordinateJet 𝕜 Ω a w φ =
      iteratedFDeriv ℝ k φ a (fun j => coordinateVector (w j)) := rfl

@[simp] theorem deltaCoordinateDerivative_apply (a : Domain d) {k : ℕ}
    (w : Fin k → Fin d) (φ : Tests 𝕜 Ω) :
    deltaCoordinateDerivative 𝕜 Ω a w φ =
      (-1 : 𝕜) ^ k * iteratedFDeriv ℝ k φ a (fun j => coordinateVector (w j)) := rfl

/-- Order zero really is Dirac evaluation, including in dimension zero. -/
@[simp] theorem deltaCoordinateDerivative_empty (a : Domain d)
    (w : Fin 0 → Fin d) (φ : Tests 𝕜 Ω) :
    deltaCoordinateDerivative 𝕜 Ω a w φ = φ a := by
  simp [iteratedFDeriv_zero_apply]

/-- Finite-dimensional algebraic step of the classification. A functional
annihilating the kernel of a finite jet is a finite sum of Dirac derivatives.
No surjectivity of the Taylor-jet map is assumed or needed. -/
theorem exists_delta_sum_of_jet_annihilation (a : Domain d)
    (u : ScalarDistribution 𝕜 Ω) (m : ℕ)
    (hu : ∀ φ : Tests 𝕜 Ω,
      (∀ i : JetIndex d m, coordinateJet 𝕜 Ω a i.2 φ = 0) → u φ = 0) :
    ∃ c : JetIndex d m → 𝕜,
      u = ∑ i, c i • deltaCoordinateDerivative 𝕜 Ω a i.2 := by
  classical
  let L (i : JetIndex d m) := (deltaCoordinateDerivative 𝕜 Ω a i.2).toLinearMap
  have hker : (⨅ i, LinearMap.ker (L i)) ≤ LinearMap.ker u.toLinearMap := by
    intro φ hφ
    apply hu φ
    intro i
    have hi := (Submodule.mem_iInf _).mp hφ i
    change (-1 : 𝕜) ^ i.1.val * coordinateJet 𝕜 Ω a i.2 φ = 0 at hi
    exact (mul_eq_zero.mp hi).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun 𝕜).mp
    (mem_span_of_iInf_ker_le_ker hker)
  refine ⟨c, ?_⟩
  ext φ
  simpa [L] using congrArg (fun f : Tests 𝕜 Ω →ₗ[𝕜] 𝕜 => f φ) hc.symm

/-- A finite sum of the stated derivatives includes the zero distribution. -/
theorem zero_delta_sum (a : Domain d) :
    (0 : ScalarDistribution 𝕜 Ω) =
      ∑ i : JetIndex d 0, (0 : 𝕜) • deltaCoordinateDerivative 𝕜 Ω a i.2 := by
  ext φ
  simp only [sum_apply, smul_apply, zero_apply, smul_eq_mul, zero_mul, Finset.sum_const_zero]

/-- Tests vanishing near the supporting point are annihilated. This is a
consequence of the accepted locality theorem, without a finite-order claim. -/
theorem point_support_locality (a : Domain d) (u : ScalarDistribution 𝕜 Ω)
    (hu : distributionSupport u ⊆ {a}) (φ : Tests 𝕜 Ω)
    (hφ : φ =ᶠ[𝓝 a] 0) : u φ = 0 := by
  obtain ⟨V, hzero, hV, hVa⟩ := eventually_nhds_iff.mp hφ
  have hs : distributionSupport u ⊆ V := by
    intro x hx
    exact (mem_singleton_iff.mp (hu hx)) ▸ hVa
  simpa using pairing_locality 𝕜 d Ω u φ 0 V hV hs hzero

/-- Coordinate jets determine the full multilinear derivative, including the
empty coordinate type. This uses the accepted finite-coordinate estimate. -/
theorem iteratedFDeriv_eq_zero_of_coordinateJet_eq_zero (a : Domain d)
    (φ : Tests 𝕜 Ω) {k : ℕ}
    (h : ∀ w : Fin k → Fin d, coordinateJet 𝕜 Ω a w φ = 0) :
    iteratedFDeriv ℝ k φ a = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hb := norm_multilinear_le_coordinate_bound (iteratedFDeriv ℝ k φ a) 0 le_rfl
    (fun w => by rw [← coordinateJet_apply a w φ, h w, norm_zero])
  simpa using hb

/-- A Taylor bound obtained directly by descending induction and the mean
value theorem. No factorial is needed for this upper bound. -/
theorem norm_iteratedFDeriv_le_pow_of_vanishing
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : E → F} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : E) (n : ℕ) (R C : ℝ) (hC : 0 ≤ C)
    (hz : ∀ k ≤ n, iteratedFDeriv ℝ k f a = 0)
    (hb : ∀ x ∈ Metric.closedBall a R, ‖iteratedFDeriv ℝ (n + 1) f x‖ ≤ C) :
    ∀ k ≤ n + 1, ∀ x ∈ Metric.closedBall a R,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖x - a‖ ^ (n + 1 - k) := by
  have hi : ∀ j ≤ n + 1, ∀ x ∈ Metric.closedBall a R,
      ‖iteratedFDeriv ℝ (n + 1 - j) f x‖ ≤ C * ‖x - a‖ ^ j := by
    intro j
    induction j with
    | zero =>
      intro _ x hx
      simpa using hb x hx
    | succ j ih =>
      intro hj x hx
      have hjn : j ≤ n := by omega
      let k := n - j
      have hk : k ≤ n := Nat.sub_le _ _
      have hkj : k + 1 = n + 1 - j := by dsimp [k]; omega
      have hD : ∀ y ∈ Metric.closedBall a ‖x - a‖,
          ‖fderiv ℝ (iteratedFDeriv ℝ k f) y‖ ≤ C * ‖x - a‖ ^ j := by
        intro y hy
        have hyx : ‖y - a‖ ≤ ‖x - a‖ := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using hy
        have hyr : y ∈ Metric.closedBall a R := by
          simpa only [Metric.mem_closedBall, dist_eq_norm] using
            hyx.trans (by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx)
        rw [norm_fderiv_iteratedFDeriv, hkj]
        exact (ih (by omega) y hyr).trans (mul_le_mul_of_nonneg_left
          (pow_le_pow_left₀ (norm_nonneg _) hyx j) hC)
      have hm := (convex_closedBall a ‖x - a‖).norm_image_sub_le_of_norm_fderiv_le
        (x := a) (y := x)
        (fun y _ => hf.differentiable_iteratedFDeriv (by exact_mod_cast ENat.natCast_lt_top k) y)
        hD (Metric.mem_closedBall_self (norm_nonneg _))
        (by simp only [Metric.mem_closedBall, dist_eq_norm, le_refl])
      rw [hz k hk, sub_zero] at hm
      have heq : n + 1 - (j + 1) = k := by dsimp [k]; omega
      rw [heq, pow_succ]
      simpa only [mul_assoc] using hm
  intro k hk x hx
  have h := hi (n + 1 - k) (Nat.sub_le _ _) x hx
  have heq : n + 1 - (n + 1 - k) = k := by omega
  rw [heq] at h
  exact h

/-- Translate a unit-scale cutoff to `a` and shrink it by a positive scale. -/
noncomputable def scaledCutoff (χ : Domain d → ℝ) (a : Domain d) (ε : ℝ) : Domain d → ℝ :=
  fun x => χ (ε⁻¹ • (x - a))

theorem contDiff_scaledCutoff {χ : Domain d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (a : Domain d) (ε : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (scaledCutoff χ a ε) :=
  hχ.comp ((contDiff_id.sub contDiff_const).const_smul _)

theorem tsupport_scaledCutoff_subset {χ : Domain d → ℝ}
    (hχ : tsupport χ ⊆ Metric.closedBall 0 1) (a : Domain d) {ε : ℝ} (hε : 0 < ε) :
    tsupport (scaledCutoff χ a ε) ⊆ Metric.closedBall a ε := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  have hm := hχ (subset_tsupport χ hx)
  have hn : ε⁻¹ * ‖x - a‖ ≤ 1 := by
    simpa [Metric.mem_closedBall, dist_eq_norm, norm_smul, abs_of_pos hε,
      scaledCutoff] using hm
  have hn' := mul_le_mul_of_nonneg_left hn hε.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hε.ne', one_mul, mul_one,
    Metric.mem_closedBall, dist_eq_norm] using hn'

theorem norm_iteratedFDeriv_scaledCutoff {χ : Domain d → ℝ}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (a : Domain d) {ε : ℝ} (hε : 0 < ε)
    (k : ℕ) (x : Domain d) :
    ‖iteratedFDeriv ℝ k (scaledCutoff χ a ε) x‖ =
      ε⁻¹ ^ k * ‖iteratedFDeriv ℝ k χ (ε⁻¹ • (x - a))‖ := by
  change ‖iteratedFDeriv ℝ k (fun z => (fun y => χ (ε⁻¹ • y)) (z - a)) x‖ = _
  rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := fun y => χ (ε⁻¹ • y)) k a x,
    iteratedFDeriv_comp_const_smul _
    (hχ.of_le (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))), norm_smul]
  simp [abs_of_pos hε]

private theorem scaling_power_bound {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    {m k i : ℕ} (hk : k ≤ m) (hi : i ≤ k) :
    ε⁻¹ ^ i * ε ^ (m + 1 - (k - i)) ≤ ε := by
  have heq : m + 1 - (k - i) = i + (m + 1 - k) := by omega
  rw [heq, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hε.ne', one_pow, one_mul]
  simpa only [pow_one] using pow_le_pow_of_le_one hε.le hε1 (show 1 ≤ m + 1 - k by omega)

/-- The analytic shrinking-cutoff estimate. Each Leibniz term contributes at
least one positive power of the scale, uniformly in the evaluation point. -/
theorem norm_iteratedFDeriv_scaled_product_le
    {χ : Domain d → ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hs : tsupport χ ⊆ Metric.closedBall 0 1)
    {f : Domain d → 𝕜} (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (a : Domain d) (m : ℕ) (R B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hb : ∀ k ≤ m, ∀ x, ‖iteratedFDeriv ℝ k χ x‖ ≤ B)
    (hflat : ∀ k ≤ m + 1, ∀ x ∈ Metric.closedBall a R,
      ‖iteratedFDeriv ℝ k f x‖ ≤ C * ‖x - a‖ ^ (m + 1 - k))
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) (hεR : ε ≤ R)
    {k : ℕ} (hk : k ≤ m) (x : Domain d) :
    ‖iteratedFDeriv ℝ k (fun y => scaledCutoff χ a ε y • f y) x‖ ≤
      (∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B * C) * ε := by
  have hsprod : tsupport (fun y => scaledCutoff χ a ε y • f y) ⊆ Metric.closedBall a ε :=
    (tsupport_smul_subset_left _ _).trans (tsupport_scaledCutoff_subset hs a hε)
  by_cases hx : x ∈ Metric.closedBall a ε
  · have hxr : x ∈ Metric.closedBall a R := hx.trans (by exact hεR)
    have hnorm : ‖x - a‖ ≤ ε := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hx
    apply (norm_iteratedFDeriv_smul_le (contDiff_scaledCutoff hχ a ε) hf x
      (by exact_mod_cast (show (k : ℕ∞) ≤ ⊤ from le_top))).trans
    rw [Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    have hik : i ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    have hχb : ‖iteratedFDeriv ℝ i (scaledCutoff χ a ε) x‖ ≤ ε⁻¹ ^ i * B := by
      rw [norm_iteratedFDeriv_scaledCutoff hχ a hε]
      exact mul_le_mul_of_nonneg_left (hb i (hik.trans hk) _) (by positivity)
    have hfb : ‖iteratedFDeriv ℝ (k - i) f x‖ ≤ C * ε ^ (m + 1 - (k - i)) :=
      (hflat _ (by omega) x hxr).trans (mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (norm_nonneg _) hnorm _) hC)
    calc
      (k.choose i : ℝ) * ‖iteratedFDeriv ℝ i (scaledCutoff χ a ε) x‖ *
          ‖iteratedFDeriv ℝ (k - i) f x‖ ≤
        (k.choose i : ℝ) * (ε⁻¹ ^ i * B) * (C * ε ^ (m + 1 - (k - i))) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hχb (by positivity)) hfb (norm_nonneg _) (by positivity)
      _ = ((k.choose i : ℝ) * B * C) *
          (ε⁻¹ ^ i * ε ^ (m + 1 - (k - i))) := by ring
      _ ≤ ((k.choose i : ℝ) * B * C) * ε :=
        mul_le_mul_of_nonneg_left (scaling_power_bound hε hε1 hk hik) (by positivity)
  · have hz : iteratedFDeriv ℝ k (fun y => scaledCutoff χ a ε y • f y) x = 0 :=
      image_eq_zero_of_notMem_tsupport (fun hx' => hx (hsprod
        (tsupport_iteratedFDeriv_subset k hx')))
    rw [hz, norm_zero]
    positivity

/-- A point-supported distribution annihilates the kernel of some finite
Taylor jet. The order comes from a single compact neighborhood of the point. -/
theorem point_support_finite_jet (a : Domain d) (ha : a ∈ Ω)
    (u : ScalarDistribution 𝕜 Ω) (hu : distributionSupport u ⊆ {a}) :
    ∃ m : ℕ, ∀ φ : Tests 𝕜 Ω,
      (∀ i : JetIndex d m, coordinateJet 𝕜 Ω a i.2 φ = 0) → u φ = 0 := by
  classical
  obtain ⟨r, hr, hball⟩ := Metric.nhds_basis_closedBall.mem_iff.mp (Ω.isOpen.mem_nhds ha)
  let K : Compacts (Domain d) := ⟨Metric.closedBall a r, isCompact_closedBall a r⟩
  obtain ⟨Cu, hCu, m, horder⟩ :=
    (finite_order_criterion 𝕜 d Ω u.toLinearMap).mp u.continuous K hball
  let U₀ : Opens (Domain d) := ⟨Metric.ball 0 1, Metric.isOpen_ball⟩
  obtain ⟨χ, V, hV, h0V, hχone⟩ := cutoff_existence d U₀ {0} isCompact_singleton
    (by intro x hx; rcases mem_singleton_iff.mp hx with rfl
        exact Metric.mem_ball_self zero_lt_one)
  have hχs : tsupport χ ⊆ Metric.closedBall 0 1 := χ.tsupport_subset.trans Metric.ball_subset_closedBall
  let K₀ : Compacts (Domain d) := ⟨Metric.closedBall 0 1, isCompact_closedBall _ _⟩
  let χs : Step ℝ K₀ := .of_support_subset χ.contDiff (subset_closure.trans hχs)
  let B := ∑ k ∈ Finset.range (m + 1),
    ContDiffMapSupportedIn.seminorm ℝ (Domain d) ℝ ⊤ K₀ k χs
  have hB : 0 ≤ B := Finset.sum_nonneg fun k _ => apply_nonneg _ _
  have hBbound (k : ℕ) (hk : k ≤ m) (x : Domain d) :
      ‖iteratedFDeriv ℝ k χ x‖ ≤ B := by
    apply (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ (f := χs) (x := x)).trans
    exact Finset.single_le_sum (fun j _ => apply_nonneg _ _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  refine ⟨m, fun φ hjet => ?_⟩
  let Kφ : Compacts (Domain d) := ⟨tsupport φ, φ.hasCompactSupport⟩
  let φs : Step 𝕜 Kφ := .of_support_subset φ.contDiff subset_closure
  let C := ContDiffMapSupportedIn.seminorm 𝕜 (Domain d) 𝕜 ⊤ Kφ (m + 1) φs
  have hC : 0 ≤ C := apply_nonneg _ _
  have hz (k : ℕ) (hk : k ≤ m) : iteratedFDeriv ℝ k φ a = 0 := by
    apply iteratedFDeriv_eq_zero_of_coordinateJet_eq_zero
    intro w
    exact hjet ⟨⟨k, Nat.lt_succ_of_le hk⟩, w⟩
  have hflat := norm_iteratedFDeriv_le_pow_of_vanishing φ.contDiff a m r C hC hz
    (fun x _ => ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top 𝕜 (f := φs) (x := x))
  let A (k : ℕ) := ∑ i ∈ Finset.range (k + 1), (k.choose i : ℝ) * B * C
  have hA (k : ℕ) : 0 ≤ A k := by dsimp [A]; positivity
  let D := ∑ k ∈ Finset.range (m + 1), A k
  have hD : 0 ≤ D := Finset.sum_nonneg fun k _ => hA k
  have hAbound (k : ℕ) (hk : k ≤ m) : A k ≤ D :=
    Finset.single_le_sum (fun j _ => hA j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hk))
  have hsmall (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hεr : ε ≤ r) :
      ‖u φ‖ ≤ Cu * D * ε := by
    let χε := scaledCutoff (χ : Domain d → ℝ) a ε
    have hχε : ContDiff ℝ (⊤ : ℕ∞) χε := contDiff_scaledCutoff χ.contDiff a ε
    have hsε : tsupport χε ⊆ Metric.closedBall a ε := tsupport_scaledCutoff_subset hχs a hε
    let ψ : Step 𝕜 K := .of_support_subset (hχε.smul φ.contDiff)
      (subset_closure.trans ((tsupport_smul_subset_left χε φ).trans
        (hsε.trans (Metric.closedBall_subset_closedBall hεr))))
    let ψ₀ : Tests 𝕜 Ω := TestFunction.ofSupportedIn hball ψ
    have heq : u ψ₀ = u φ := by
      let W := (fun x : Domain d => ε⁻¹ • (x - a)) ⁻¹' V
      have hW : IsOpen W := hV.preimage
        (show Continuous (fun x : Domain d => ε⁻¹ • (x - a)) by fun_prop)
      have haW : a ∈ W := by simpa [W] using h0V (mem_singleton _)
      apply pairing_locality 𝕜 d Ω u ψ₀ φ W hW
        (fun x hx => (mem_singleton_iff.mp (hu hx)) ▸ haW)
      intro x hx
      change χ (ε⁻¹ • (x - a)) • φ x = φ x
      rw [hχone hx]
      exact one_smul ℝ _
    have hp : stepSeminorm 𝕜 K m ψ ≤ D * ε := by
      apply (step_seminorm_formula 𝕜 d K m ψ (D * ε) (mul_nonneg hD hε.le)).mpr
      intro k hk w x
      calc
        ‖iteratedFDeriv ℝ k ψ x (fun j => coordinateVector (w j))‖ ≤
          ‖iteratedFDeriv ℝ k ψ x‖ * ∏ j, ‖coordinateVector (w j)‖ :=
          ContinuousMultilinearMap.le_opNorm _ _
        _ = ‖iteratedFDeriv ℝ k ψ x‖ := by simp [coordinateVector, Pi.norm_single]
        _ ≤ A k * ε := norm_iteratedFDeriv_scaled_product_le χ.contDiff hχs φ.contDiff
          a m r B C hB hC hBbound hflat hε hε1 hεr hk x
        _ ≤ D * ε := mul_le_mul_of_nonneg_right (hAbound k hk) hε.le
    rw [← heq]
    exact (horder ψ).trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hCu)
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have hlim : Filter.Tendsto (fun ε : ℝ => Cu * D * ε) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (show Filter.Tendsto (fun ε : ℝ => ε)
      (𝓝[>] 0) (𝓝 0) from nhdsWithin_le_nhds))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin,
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 from zero_lt_one)),
    mem_nhdsWithin_of_mem_nhds (Iio_mem_nhds hr)] with ε hε hε1 hεr
  exact hsmall ε hε hε1.le hεr.le

/-- Every scalar distribution supported at a point is a finite linear
combination of coordinate derivatives of its Dirac distribution. -/
theorem point_supported_distributions :
    Specs.ExpandedFA.Distributions.PointSupportedDistributions.pointSupportType := by
  intro 𝕜 _ d Ω a ha u hu
  obtain ⟨m, hm⟩ := point_support_finite_jet a ha u hu
  obtain ⟨c, hc⟩ := exists_delta_sum_of_jet_annihilation a u m hm
  exact ⟨m, c, hc⟩

end ExpandedFA.Distributions
