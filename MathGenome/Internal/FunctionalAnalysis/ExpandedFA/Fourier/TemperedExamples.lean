import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Fourier.TemperedExamples
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierInversion
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Distributions.CompactDistributionsAndSmoothDual

open MeasureTheory TopologicalSpace Set
open scoped SchwartzMap Topology FourierTransform ContDiff

noncomputable section
namespace ExpandedFA.Fourier.Examples

open ExpandedFA.Distributions

/-- Forget rapid decay, retaining the compact-local smooth topology. -/
def schwartzToSmoothLM (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    SchwartzMap (Domain d) 𝕜 →ₗ[𝕜] SmoothFunctions 𝕜 (⊤ : Opens (Domain d)) where
  toFun f := ⟨f, (f.smooth ⊤).contDiffOn, by simp⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def schwartzToSmooth (𝕜 : Type) [RCLike 𝕜] (d : ℕ) :
    SchwartzMap (Domain d) 𝕜 →L[𝕜] SmoothFunctions 𝕜 (⊤ : Opens (Domain d)) where
  toLinearMap := schwartzToSmoothLM 𝕜 d
  cont := by
    apply WithSeminorms.continuous_of_continuous_comp smooth_withSeminorms
    intro q
    apply Seminorm.continuous_of_le
      ((schwartz_withSeminorms 𝕜 (Domain d) 𝕜).continuous_seminorm (0, q.2))
    intro f
    change ‖smoothJetLM 𝕜 (⊤ : Opens (Domain d)) q _‖ ≤ _
    apply (ContinuousMap.norm_le _ (apply_nonneg _ _)).mpr
    intro x
    exact SchwartzMap.norm_iteratedFDeriv_le_seminorm 𝕜 f q.2 x

theorem compact_support_tempered :
    Specs.ExpandedFA.Fourier.TemperedExamples.compactSupportType := by
  intro 𝕜 _ d u hu
  obtain ⟨L, hL, _⟩ := compact_dual_extension 𝕜 d ⊤ u hu
  let P : Schwartz 𝕜 d →L[𝕜] SchwartzMap (Domain d) 𝕜 :=
    SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜
    (EuclideanSpace.equiv (Fin d) ℝ).symm
  refine ⟨L.comp ((schwartzToSmooth 𝕜 d).comp P), ?_⟩
  intro φ
  change L (schwartzToSmooth 𝕜 d (P (testSchwartz 𝕜 φ))) = u φ
  rw [show schwartzToSmooth 𝕜 d (P (testSchwartz 𝕜 φ)) =
      testToSmoothLM 𝕜 ⊤ φ by
    apply Subtype.ext
    funext x
    change φ ((EuclideanSpace.equiv (Fin d) ℝ)
      ((EuclideanSpace.equiv (Fin d) ℝ).symm x)) = φ x
    rw [ContinuousLinearEquiv.apply_symm_apply]]
  exact hL φ

@[simp] theorem delta_apply (𝕜 : Type) [RCLike 𝕜] (d : ℕ) (φ : Schwartz 𝕜 d) :
    delta 𝕜 d φ = φ 0 := rfl

@[simp] theorem oneDistribution_apply (𝕜 : Type) [RCLike 𝕜] (d : ℕ)
    (φ : Schwartz 𝕜 d) : oneDistribution 𝕜 d φ = ∫ x, φ x := rfl

theorem basic_fourier : Specs.ExpandedFA.Fourier.TemperedExamples.basicFourierType := by
  intro d
  have hd : temperedFourier (delta ℂ d) = oneDistribution ℂ d := by
    ext φ
    change (𝓕 φ : Schwartz ℂ d) 0 = ∫ x, φ x
    rw [SchwartzMap.fourier_coe, Real.fourier_eq]
    simp
  refine ⟨?_, hd⟩
  rw [← hd]
  ext φ
  change schwartzFourier (schwartzFourier φ) 0 = φ 0
  simpa using Inversion.fourier_square d φ 0

/-- Weighted integral growth gives the usual quantitative Schwartz bound. -/
theorem weighted_pairing_bound (𝕜 : Type) [RCLike 𝕜] {d : ℕ}
    (f : Euclidean d → 𝕜) (N : ℕ) (φ : Schwartz 𝕜 d) (x : Euclidean d) :
    ‖f x * φ x‖ ≤ ((1 + ‖x‖)⁻¹ ^ N * ‖f x‖) *
      (2 ^ N * (Finset.Iic (N, 0)).sup (schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜) φ) := by
  have hp : 0 < 1 + ‖x‖ := by positivity
  have hφ := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜)
    (m := (N, 0)) (k := N) (n := 0) le_rfl le_rfl φ x
  rw [norm_iteratedFDeriv_zero] at hφ
  have hb : ‖φ x‖ ≤ (1 + ‖x‖)⁻¹ ^ N *
      (2 ^ N * (Finset.Iic (N, 0)).sup
        (schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜) φ) := by
    rw [inv_pow, ← div_eq_inv_mul, le_div_iff₀' (pow_pos hp N)]
    exact hφ
  rw [norm_mul]
  calc
    ‖f x‖ * ‖φ x‖ ≤ ‖f x‖ * ((1 + ‖x‖)⁻¹ ^ N *
      (2 ^ N * (Finset.Iic (N, 0)).sup
        (schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜) φ)) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg _)
    _ = _ := by ring

theorem integral_growth_tempered :
    Specs.ExpandedFA.Fourier.TemperedExamples.integralGrowthType := by
  intro 𝕜 _ d f hf N hN
  have hi (φ : Schwartz 𝕜 d) : Integrable (fun x => f x * φ x) := by
    apply (hN.mul_const (2 ^ N * (Finset.Iic (N, 0)).sup
      (schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜) φ)).mono
      (hf.aestronglyMeasurable.mul φ.continuous.aestronglyMeasurable)
    filter_upwards [] with x
    exact (weighted_pairing_bound 𝕜 f N φ x).trans (le_abs_self _)
  let U : Tempered 𝕜 d := SchwartzMap.mkCLMtoNormedSpace
    (fun φ : Schwartz 𝕜 d => ∫ x, f x * φ x)
    (fun φ ψ => by
      simp only [add_apply, mul_add]
      exact integral_add (hi φ) (hi ψ))
    (fun c φ => by
      simp only [smul_apply, smul_eq_mul]
      simp_rw [show ∀ x, f x * (c * φ x) = c * (f x * φ x) by intro x; ring]
      exact integral_const_mul c _) (by
      refine ⟨Finset.Iic (N, 0), (∫ x, (1 + ‖x‖)⁻¹ ^ N * ‖f x‖) * 2 ^ N,
        by positivity, ?_⟩
      intro φ
      calc
        ‖∫ x, f x * φ x‖ ≤ ∫ x, ‖f x * φ x‖ := norm_integral_le_integral_norm _
        _ ≤ ∫ x, ((1 + ‖x‖)⁻¹ ^ N * ‖f x‖) *
            (2 ^ N * (Finset.Iic (N, 0)).sup
              (schwartzSeminormFamily 𝕜 (Euclidean d) 𝕜) φ) :=
          integral_mono (hi φ).norm (hN.mul_const _) (weighted_pairing_bound 𝕜 f N φ)
        _ = _ := by rw [integral_mul_const]; ring)
  exact ⟨U, fun φ => ⟨hi φ, rfl⟩⟩

/-- Iterated coordinate multiplication preserves the integral interpretation. -/
theorem monomial_pairing :
    Specs.ExpandedFA.Fourier.TemperedExamples.monomialPairingType := by
  intro d w
  induction w with
  | nil =>
    intro φ
    simpa [wordMonomial, monomialDistribution] using
      And.intro φ.integrable (oneDistribution_apply ℂ d φ)
  | cons i w ih =>
    intro φ
    obtain ⟨hi, he⟩ := ih (coordinateMultiply i φ)
    have hfun : (fun x => wordMonomial w x * coordinateMultiply i φ x) =
        (fun x => wordMonomial (i :: w) x * φ x) := by
      funext x
      rw [show coordinateMultiply i φ x = (x i : ℂ) * φ x from
        (coordinate_pairing d i (0 : Tempered ℂ d) φ).1 x]
      simp only [wordMonomial]
      ring
    rw [hfun] at hi he
    exact ⟨hi, he⟩

@[simp] theorem temperedFourier_smul {d : ℕ} (c : ℂ) (u : Tempered ℂ d) :
    temperedFourier (c • u) = c • temperedFourier u := by ext φ; rfl

@[simp] theorem temperedPartial_smul {d : ℕ} (i : Fin d) (c : ℂ) (u : Tempered ℂ d) :
    temperedPartial i (c • u) = c • temperedPartial i u := by
  ext φ
  change -(c * u _) = c * -u _
  ring

@[simp] theorem temperedCoordinateMultiply_smul {d : ℕ} (i : Fin d)
    (c : ℂ) (u : Tempered ℂ d) :
    temperedCoordinateMultiply i (c • u) = c • temperedCoordinateMultiply i u := by
  ext φ
  rfl

/-- Monomial transforms, with the minus sign from scalar-linear transposition. -/
theorem fourier_monomial {d : ℕ} (w : List (Fin d)) :
    temperedFourier (monomialDistribution w) =
      (-(2 * (Real.pi : ℂ) * Complex.I)⁻¹) ^ w.length • deltaDerivative w := by
  induction w with
  | nil => simpa [monomialDistribution, deltaDerivative] using (basic_fourier d).1
  | cons i w ih =>
    rw [monomialDistribution, Inversion.tempered_fourier_coordinate, ih,
      temperedPartial_smul, smul_smul, deltaDerivative, List.length_cons, pow_succ']

/-- Conversely every delta derivative transforms to the indicated monomial. -/
theorem fourier_deltaDerivative {d : ℕ} (w : List (Fin d)) :
    temperedFourier (deltaDerivative w) =
      (2 * (Real.pi : ℂ) * Complex.I) ^ w.length • monomialDistribution w := by
  induction w with
  | nil => simpa [monomialDistribution, deltaDerivative] using (basic_fourier d).2
  | cons i w ih =>
    rw [deltaDerivative, Inversion.tempered_fourier_partial, ih,
      temperedCoordinateMultiply_smul, smul_smul, monomialDistribution,
      List.length_cons, pow_succ']

theorem temperedFourier_sum {d : ℕ} {ι : Type*} (s : Finset ι) (u : ι → Tempered ℂ d) :
    temperedFourier (∑ i ∈ s, u i) = ∑ i ∈ s, temperedFourier (u i) := by
  ext φ
  simp [temperedFourier]

theorem polynomial_fourier :
    Specs.ExpandedFA.Fourier.TemperedExamples.polynomialFourierType := by
  intro d s c
  constructor
  · simp_rw [temperedFourier_sum, temperedFourier_smul, fourier_monomial, smul_smul]
  · simp_rw [temperedFourier_sum, temperedFourier_smul, fourier_deltaDerivative, smul_smul]

/-- Translation on Schwartz functions, with its usual underlying function. -/
def translateSchwartz {𝕜 : Type} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] (a : E) :
    SchwartzMap E 𝕜 →L[𝕜] SchwartzMap E 𝕜 :=
  SchwartzMap.compCLMOfAntilipschitz 𝕜
    (show (fun x : E => x - a).HasTemperateGrowth by fun_prop)
    (IsometryEquiv.subRight a).isometry.antilipschitzWith

@[simp] theorem translateSchwartz_apply {𝕜 : Type} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (f : SchwartzMap E 𝕜) (x : E) : translateSchwartz a f x = f (x-a) := rfl

theorem seminorm_translate_le {𝕜 : Type} [RCLike 𝕜] {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (a : E) (f : SchwartzMap E 𝕜) (k n : ℕ) :
    SchwartzMap.seminorm 𝕜 k n (translateSchwartz a f) ≤
      (1 + ‖a‖)^k * (2^k * (Finset.Iic (k,n)).sup
        (schwartzSeminormFamily 𝕜 E 𝕜) f) := by
  apply SchwartzMap.seminorm_le_bound 𝕜 k n _ (by positivity)
  intro x
  change ‖x‖ ^ k * ‖iteratedFDeriv ℝ n (fun y => f (y-a)) x‖ ≤ _
  rw [iteratedFDeriv_comp_sub]
  have hx : ‖x‖ ≤ (1 + ‖a‖) * (1 + ‖x-a‖) := by
    have ht : ‖x‖ ≤ ‖x-a‖ + ‖a‖ := by
      simpa using norm_add_le (x-a) a
    nlinarith [norm_nonneg a, norm_nonneg (x-a), mul_nonneg (norm_nonneg a) (norm_nonneg (x-a))]
  calc
    _ ≤ ((1 + ‖a‖) * (1 + ‖x-a‖))^k * ‖iteratedFDeriv ℝ n f (x-a)‖ := by gcongr
    _ = (1 + ‖a‖)^k * ((1 + ‖x-a‖)^k * ‖iteratedFDeriv ℝ n f (x-a)‖) := by
      rw [mul_pow]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := 𝕜) (m := (k,n)) le_rfl le_rfl f (x-a))
      (by positivity)

/-- Exponential damping of translates tends to zero in every Schwartz seminorm. -/
theorem damped_translates_tendsto_zero (𝕜 : Type) [RCLike 𝕜]
    (f : SchwartzMap (Domain 1) 𝕜) :
    Filter.Tendsto (fun n : ℕ => (Real.exp (-(n : ℝ)) : 𝕜) •
      translateSchwartz (fun _ : Fin 1 => (n : ℝ) + 1) f)
      Filter.atTop (𝓝 0) := by
  apply (schwartz_withSeminorms 𝕜 (Domain 1) 𝕜).tendsto_nhds _ _ |>.mpr
  intro q ε hε
  let C := 2 ^ q.1 * (Finset.Iic q).sup
    (schwartzSeminormFamily 𝕜 (Domain 1) 𝕜) f
  have hb (n : ℕ) :
      SchwartzMap.seminorm 𝕜 q.1 q.2
        ((Real.exp (-(n : ℝ)) : 𝕜) • translateSchwartz (fun _ : Fin 1 => (n : ℝ)+1) f) ≤
      (((n : ℝ)+2)^q.1 * Real.exp (-(n : ℝ))) * C := by
    rw [map_smul_eq_mul, RCLike.norm_ofReal, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (-(n : ℝ)) * ((1 + ‖fun _ : Fin 1 => (n : ℝ)+1‖)^q.1 * C) :=
        mul_le_mul_of_nonneg_left (seminorm_translate_le _ f q.1 q.2) (Real.exp_pos _).le
      _ = _ := by
        rw [pi_norm_const, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [show (1 : ℝ) + ((n : ℝ) + 1) = (n : ℝ) + 2 by ring]
        ring
  have ht : Filter.Tendsto (fun n : ℕ =>
      (((n : ℝ)+2)^q.1 * Real.exp (-(n : ℝ))) * C) Filter.atTop (𝓝 0) := by
    have hnat : Filter.Tendsto (fun n : ℕ => (n : ℝ)+2) Filter.atTop Filter.atTop :=
      tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
    have h := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero q.1).comp hnat).mul_const
      (Real.exp 2 * C)
    convert h using 1
    · funext n
      simp only [Function.comp_apply]
      have he : Real.exp (-(n : ℝ)) = Real.exp (-((n : ℝ)+2)) * Real.exp 2 := by
        rw [← Real.exp_add]
        congr 1
        ring
      rw [he]
      ring
    · simp
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn
  simp only [sub_zero]
  change SchwartzMap.seminorm 𝕜 q.1 q.2 _ < ε
  exact (hb n).trans_lt hn

/-- A damped translate as an actual compactly supported LF test. -/
def dampedRealTest (b : Tests ℝ (⊤ : Opens (Domain 1))) (n : ℕ) :
    Tests ℝ (⊤ : Opens (Domain 1)) where
  toFun x := Real.exp (-(n : ℝ)) * b (x - fun _ => (n : ℝ)+1)
  contDiff' := contDiff_const.mul (b.contDiff.comp (contDiff_id.sub contDiff_const))
  hasCompactSupport' := (b.hasCompactSupport.comp_homeomorph
    (IsometryEquiv.subRight (fun _ : Fin 1 => (n : ℝ)+1)).toHomeomorph).mul_left
  tsupport_subset' := subset_univ _

theorem damped_tests_tendsto_zero (𝕜 : Type) [RCLike 𝕜]
    (b : Tests ℝ (⊤ : Opens (Domain 1))) :
    Filter.Tendsto (fun n => testSchwartz 𝕜 (scalarCutoff 𝕜 (dampedRealTest b n)))
      Filter.atTop (𝓝 0) := by
  let f : SchwartzMap (Domain 1) 𝕜 :=
    (scalarCutoff 𝕜 b).hasCompactSupport.toSchwartzMap (scalarCutoff 𝕜 b).contDiff
  let P : SchwartzMap (Domain 1) 𝕜 →L[𝕜] Schwartz 𝕜 1 :=
    SchwartzMap.compCLMOfContinuousLinearEquiv 𝕜 (EuclideanSpace.equiv (Fin 1) ℝ)
  have he (n : ℕ) : testSchwartz 𝕜 (scalarCutoff 𝕜 (dampedRealTest b n)) =
      P ((Real.exp (-(n : ℝ)) : 𝕜) • translateSchwartz (fun _ : Fin 1 => (n : ℝ)+1) f) := by
    ext x
    change (↑(Real.exp (-(n : ℝ)) *
      b ((EuclideanSpace.equiv (Fin 1) ℝ) x - fun _ : Fin 1 => (n : ℝ)+1)) : 𝕜) =
      (Real.exp (-(n : ℝ)) : 𝕜) •
        (b ((EuclideanSpace.equiv (Fin 1) ℝ) x - fun _ : Fin 1 => (n : ℝ)+1) : 𝕜)
    rw [RCLike.ofReal_mul, smul_eq_mul]
  simp_rw [he]
  have h := P.continuous.continuousAt.tendsto.comp (damped_translates_tendsto_zero 𝕜 f)
  change Filter.Tendsto (fun n : ℕ => P ((Real.exp (-(n : ℝ)) : 𝕜) •
    translateSchwartz (fun _ : Fin 1 => (n : ℝ)+1) f)) Filter.atTop (𝓝 (P 0)) at h
  rw [map_zero] at h
  exact h

/-- The positive pairings grow exponentially along these compact tests. -/
theorem exp_square_damped_pairings
    (b : Tests ℝ (⊤ : Opens (Domain 1)))
    (hb : ∀ x, 0 ≤ b x) (hs : tsupport b ⊆ Metric.ball 0 1) (h0 : b 0 = 1) :
    Filter.Tendsto (fun n : ℕ => ∫ x : Domain 1,
      Real.exp ((x 0)^2) * dampedRealTest b n x) Filter.atTop Filter.atTop := by
  have hi : Integrable (b : Domain 1 → ℝ) :=
    b.continuous.integrable_of_hasCompactSupport b.hasCompactSupport
  have hI : 0 < ∫ x : Domain 1, b x :=
    integral_pos_of_integrable_nonneg_nonzero b.continuous hi hb (by rw [h0]; norm_num)
  have hlow : ∀ᶠ n : ℕ in Filter.atTop,
      Real.exp (n : ℝ) * (∫ x : Domain 1, b x) ≤
        ∫ x : Domain 1, Real.exp ((x 0)^2) * dampedRealTest b n x := by
    filter_upwards [Filter.eventually_ge_atTop 2] with n hn
    let a : Domain 1 := fun _ => (n : ℝ)+1
    have htrans : Integrable (fun x => b (x-a)) := hi.comp_sub_right a
    have hprod : Integrable (fun x : Domain 1 =>
        Real.exp ((x 0)^2) * dampedRealTest b n x) := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact (Real.continuous_exp.comp ((continuous_apply 0).pow 2)).mul
          (dampedRealTest b n).continuous
      · exact (dampedRealTest b n).hasCompactSupport.mul_left
    calc
      _ = ∫ x : Domain 1, Real.exp (n : ℝ) * b (x-a) := by
        rw [integral_const_mul, integral_sub_right_eq_self]
      _ ≤ _ := by
        apply integral_mono (htrans.const_mul _) hprod
        intro x
        by_cases hx : b (x-a) = 0
        · change Real.exp (n : ℝ) * b (x-a) ≤
            Real.exp ((x 0)^2) * (Real.exp (-(n : ℝ)) * b (x-a))
          rw [hx]
          simp
        have hmem : x-a ∈ tsupport b := subset_tsupport _ hx
        have hnorm : ‖x-a‖ < 1 := by simpa using hs hmem
        have hc : |x 0 - ((n : ℝ)+1)| < 1 :=
          lt_of_le_of_lt (by simpa [a] using norm_le_pi_norm (x-a) (0 : Fin 1)) hnorm
        have hn' : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
        have hxn : (n : ℝ) < x 0 := by have := (abs_lt.mp hc).1; linarith
        have hsquare : (2 : ℝ) * n ≤ (x 0)^2 := by nlinarith
        have he : Real.exp (n : ℝ) ≤ Real.exp ((x 0)^2) * Real.exp (-(n : ℝ)) := by
          rw [← Real.exp_add]
          exact Real.exp_le_exp.mpr (by linarith)
        change Real.exp (n : ℝ) * b (x-a) ≤
          Real.exp ((x 0)^2) * (Real.exp (-(n : ℝ)) * b (x-a))
        nlinarith [mul_le_mul_of_nonneg_right he (hb (x-a))]
  apply Filter.tendsto_atTop_mono' Filter.atTop hlow
  exact (Real.tendsto_exp_atTop.comp tendsto_natCast_atTop_atTop).atTop_mul_const hI

/-- The chosen exponential density is locally integrable in the original LF domain. -/
theorem exp_square_locallyIntegrable (𝕜 : Type) [RCLike 𝕜] :
    LocallyIntegrable (fun x : Domain 1 => (Real.exp ((x 0)^2) : 𝕜)) volume := by
  apply Continuous.locallyIntegrable
  exact RCLike.continuous_ofReal.comp (Real.continuous_exp.comp ((continuous_apply 0).pow 2))

/-- This part of the counterexample already supplies an actual distribution. -/
theorem exp_square_distribution (𝕜 : Type) [RCLike 𝕜] :
    ∃ u : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)),
      ∀ φ, u φ = ∫ x : Domain 1, (Real.exp ((x 0)^2) : 𝕜) * φ x := by
  exact integration 𝕜 1 ⊤ volume _
    ((exp_square_locallyIntegrable 𝕜).locallyIntegrableOn _)

/-- Sequential failure of continuity excludes every possible tempered extension. -/
theorem no_tempered_extension_of_tests (𝕜 : Type) [RCLike 𝕜]
    (u : ScalarDistribution 𝕜 (⊤ : Opens (Domain 1)))
    (ψ : ℕ → Tests 𝕜 (⊤ : Opens (Domain 1)))
    (hψ : Filter.Tendsto (fun n => testSchwartz 𝕜 (ψ n)) Filter.atTop (𝓝 0))
    (hu : Filter.Tendsto (fun n => RCLike.re (u (ψ n))) Filter.atTop Filter.atTop) :
    ¬ ∃ U : Tempered 𝕜 1, ∀ φ, U (testSchwartz 𝕜 φ) = u φ := by
  rintro ⟨U, hU⟩
  have hz : Filter.Tendsto (fun n => RCLike.re (u (ψ n))) Filter.atTop (𝓝 0) := by
    have h := RCLike.continuous_re.continuousAt.tendsto.comp
      (U.continuous.continuousAt.tendsto.comp hψ)
    change Filter.Tendsto (fun n => RCLike.re (U (testSchwartz 𝕜 (ψ n))))
      Filter.atTop (𝓝 (RCLike.re (U 0))) at h
    simpa only [map_zero, RCLike.zero_re, hU] using h
  exact not_tendsto_nhds_of_tendsto_atTop hu 0 hz

theorem exp_square_not_tempered :
    Specs.ExpandedFA.Fourier.TemperedExamples.nonTemperedType := by
  intro 𝕜 _
  obtain ⟨b, hbs, hbc, hbd, hbr, hb0⟩ :=
    exists_contDiff_tsupport_subset (n := (⊤ : ℕ∞))
      (Metric.ball_mem_nhds (0 : Domain 1) (by norm_num : (0 : ℝ) < 1))
  let B : Tests ℝ (⊤ : Opens (Domain 1)) := ⟨b, hbd, hbc, subset_univ _⟩
  obtain ⟨u, hu⟩ := exp_square_distribution 𝕜
  let ψ (n : ℕ) := scalarCutoff 𝕜 (dampedRealTest B n)
  have hz : Filter.Tendsto (fun n => testSchwartz 𝕜 (ψ n)) Filter.atTop (𝓝 0) :=
    damped_tests_tendsto_zero 𝕜 B
  have hp (n : ℕ) : RCLike.re (u (ψ n)) = ∫ x : Domain 1,
      Real.exp ((x 0)^2) * dampedRealTest B n x := by
    rw [hu]
    change RCLike.re (∫ x : Domain 1,
      (Real.exp ((x 0)^2) : 𝕜) * (dampedRealTest B n x : 𝕜)) = _
    simp_rw [← RCLike.ofReal_mul]
    rw [integral_ofReal, RCLike.ofReal_re]
  have hinf : Filter.Tendsto (fun n => RCLike.re (u (ψ n))) Filter.atTop Filter.atTop := by
    simp_rw [hp]
    exact exp_square_damped_pairings B (fun x => (hbr ⟨x, rfl⟩).1) hbs hb0
  exact ⟨u, hu, ⟨ψ, hz, hinf⟩, no_tempered_extension_of_tests 𝕜 u ψ hz hinf⟩

end ExpandedFA.Fourier.Examples
