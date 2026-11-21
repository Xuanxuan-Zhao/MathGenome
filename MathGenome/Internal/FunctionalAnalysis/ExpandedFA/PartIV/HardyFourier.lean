import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.HardyFourier
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.AtomicHardySpace
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.SchwartzFourierConvention
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Fourier.Plancherel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Hardy.HardyCZEndpoint
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic

noncomputable section
open MeasureTheory Filter Set
open scoped Topology FourierTransform ENNReal

namespace ExpandedFA.PartIV.HardyFourier
open ExpandedFA.Fourier ExpandedFA.Hardy.AtomicHardySpaceSpec
open HardyFourierSpec

lemma fourier_complex {d : ℕ} (f : Euclidean d → ℂ) :
    HardyFourierSpec.fourier f = integralFourier f := by
  simp [HardyFourierSpec.fourier]

lemma fourier_real {d : ℕ} (f : Euclidean d → ℝ) :
    HardyFourierSpec.fourier f = integralFourier (fun x => (f x : ℂ)) := by
  simp [HardyFourierSpec.fourier, RCLike.ofRealCLM_apply]

lemma fourier_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    HardyFourierSpec.fourier (0 : Euclidean d → 𝕜) = 0 := by
  ext ξ
  simp [HardyFourierSpec.fourier, integralFourier]

lemma weightedIntegral_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    weightedIntegral (0 : Euclidean d → 𝕜) = 0 := by
  simp [weightedIntegral, fourier_zero]

lemma fourier_congr_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f g : Euclidean d → 𝕜} (hfg : f =ᵐ[volume] g) :
    HardyFourierSpec.fourier f = HardyFourierSpec.fourier g := by
  ext ξ
  apply integral_congr_ae
  filter_upwards [hfg] with x hx
  simp only [hx]

lemma weightedIntegral_congr_ae {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f g : Euclidean d → 𝕜} (hfg : f =ᵐ[volume] g) :
    weightedIntegral f = weightedIntegral g := by
  unfold weightedIntegral
  rw [fourier_congr_ae hfg]

/-- The zero-dimensional Hardy space has no nonzero element: its L¹ embedding
has zero integral, while integration on the singleton is evaluation. -/
theorem zero_dimension : ZeroDimension := by
  intro 𝕜 _ h
  have hz := ExpandedFA.Hardy.AtomicHardySpace.integral_zero volume h
  have hv : (volume : Measure (Euclidean 0)) = Measure.dirac 0 :=
    volume_euclideanSpace_eq_dirac (Fin 0)
  have hz0 : EmbeddingValue volume h 0 = 0 := by
    have hi := congrArg (fun μ : Measure (Euclidean 0) =>
      ∫ x, EmbeddingValue volume h x ∂μ) hv
    simpa only [integral_dirac] using hi.symm.trans hz
  have he : EmbeddingValue volume h = 0 := by
    apply Lp.ext
    filter_upwards [] with x
    have hx : x = (0 : Euclidean 0) := Subsingleton.elim _ _
    rw [hx, hz0]
    simp
  have hh : h = 0 := (ExpandedFA.Hardy.AtomicHardySpace.embedding_properties volume).1
    (by simpa using he)
  refine ⟨hh, ?_⟩
  apply (weightedIntegral_congr_ae ?_).trans weightedIntegral_zero
  exact he ▸ Lp.coeFn_zero _ _ _

/-- The critical reciprocal power is nonintegrable on every neighborhood of
zero in positive Euclidean dimension. -/
lemma reciprocal_power_not_integrable {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    ¬ IntegrableOn (fun x : Euclidean d => (‖x‖ ^ d)⁻¹) (Metric.ball 0 r) := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  intro h
  have hi : IntegrableOn (fun t : ℝ => t ^ (d - 1) * (t ^ d)⁻¹) (Ioo 0 r) := by
    simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using
      (integrableOn_fun_norm_addHaar volume (f := fun t : ℝ => (t ^ d)⁻¹)).mp h
  have hi' : IntegrableOn (fun t : ℝ => t ^ (-1 : ℝ)) (Ioo 0 r) := by
    apply hi.congr_fun _ measurableSet_Ioo
    intro t ht
    dsimp only
    rw [Real.rpow_neg_one]
    have hp : t ^ d = t ^ (d - 1) * t := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hp]
    field_simp [ne_of_gt ht.1]
  have := (intervalIntegral.integrableOn_Ioo_rpow_iff hr).mp hi'
  linarith

/-- Actual L¹ Fourier transforms are continuous, also for real inputs. -/
lemma fourier_continuous {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {f : Euclidean d → 𝕜} (hf : Integrable f) :
    Continuous (HardyFourierSpec.fourier f) := by
  have hi : Integrable (fun x => RCLike.map 𝕜 ℂ (f x)) :=
    (RCLike.map 𝕜 ℂ).integrable_comp hf
  have he : HardyFourierSpec.fourier f = 𝓕 (fun x => RCLike.map 𝕜 ℂ (f x)) := by
    ext ξ
    exact integralFourier_eq_native _ _
  rw [he]
  exact VectorFourier.fourierIntegral_continuous Real.continuous_fourierChar
    (innerSL ℝ).continuous₂ hi

/-- Fourier continuity and a nonzero mean force logarithmic divergence.
This stronger helper is used only at positive dimensions. -/
lemma nonzero_mean_divergence {d : ℕ} (hd : 0 < d)
    {f : Euclidean d → ℝ} (hf : Integrable f) (hz : (∫ x, f x) ≠ 0) :
    weightedIntegral f = ∞ := by
  have hcont := fourier_continuous hf
  have hz0 : HardyFourierSpec.fourier f 0 = (∫ x, f x : ℝ) := by
    rw [fourier_real]
    simp only [integralFourier, inner_zero_right, Complex.ofReal_zero, mul_zero,
      Complex.exp_zero, one_mul]
    exact Complex.ofRealCLM.integral_comp_comm hf
  have hn : 0 < ‖HardyFourierSpec.fourier f 0‖ := by
    rw [hz0, Complex.norm_real]
    exact norm_pos_iff.mpr hz
  let m := ‖HardyFourierSpec.fourier f 0‖ / 2
  have hm : 0 < m := half_pos hn
  have hnhood : ∀ᶠ ξ in 𝓝 (0 : Euclidean d), m < ‖HardyFourierSpec.fourier f ξ‖ :=
    hcont.norm.continuousAt.eventually (lt_mem_nhds (half_lt_self hn))
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hnhood
  by_contra hfin
  have hq : Integrable (fun ξ => ‖HardyFourierSpec.fourier f ξ‖ / ‖ξ‖ ^ d) := by
    refine ⟨(hcont.norm.measurable.div (measurable_norm.pow_const d)).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal (ae_of_all _ fun ξ => by positivity)).mpr
      (lt_top_iff_ne_top.mpr hfin)
  apply reciprocal_power_not_integrable hd hr
  apply (hq.integrableOn.const_mul m⁻¹).mono'
    ((measurable_norm.pow_const d).inv.aestronglyMeasurable.restrict)
  filter_upwards [ae_restrict_mem measurableSet_ball] with ξ hξ
  have hb : m ≤ ‖HardyFourierSpec.fourier f ξ‖ := (hball hξ).le
  have hm' : m⁻¹ * m = 1 := inv_mul_cancel₀ hm.ne'
  have := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hm.le))
    (inv_nonneg.mpr (pow_nonneg (norm_nonneg ξ) d))
  simpa only [Pi.inv_apply, norm_inv, norm_pow, norm_norm, hm', one_mul, div_eq_mul_inv, mul_assoc] using this

/-- A normalized real ball indicator satisfies every atom requirement except
cancellation, and its actual Fourier integral is infinite. -/
theorem cancellation_necessary : CancellationNecessary := by
  intro d hd C
  let B := Metric.ball (0 : Euclidean d) 1
  let V := volume.real B
  have hB : MeasurableSet B := measurableSet_ball
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume 0 zero_lt_one).ne' measure_ball_ne_top
  let g : Euclidean d → ℝ := B.indicator (fun _ => V⁻¹)
  have hg : Integrable g := (integrable_indicator_iff hB).mpr
    (integrableOn_const measure_ball_ne_top)
  have hmean : (∫ x, g x) = 1 := by
    rw [integral_indicator_const _ hB]
    simp [V, smul_eq_mul, hV.ne']
  let f : HardyFourierSpec.L1 ℝ d := hg.toL1 g
  refine ⟨f, ⟨0, 1, zero_lt_one, ?_⟩, ?_⟩
  · filter_upwards [hg.coeFn_toL1] with x hx
    change f x = g x at hx
    rw [hx]
    constructor
    · intro hn
      exact indicator_of_notMem hn _
    · by_cases h : x ∈ B
      · simp only [g, indicator_of_mem h, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hV.le)]
        exact le_rfl
      · simp only [g, indicator_of_notMem h, norm_zero]
        exact inv_nonneg.mpr hV.le
  · have he : weightedIntegral (f : Euclidean d → ℝ) = ∞ := by
      rw [weightedIntegral_congr_ae hg.coeFn_toL1]
      exact nonzero_mean_divergence hd hg (by rw [hmean]; exact one_ne_zero)
    rw [he]
    exact ENNReal.ofReal_lt_top

lemma norm_complex_map {𝕜 : Type} [RCLike 𝕜] (c : 𝕜) :
    ‖RCLike.map 𝕜 ℂ c‖ = ‖c‖ := RCLike.norm_to_complex c

lemma complex_map_mul {𝕜 : Type} [RCLike 𝕜] (a b : 𝕜) :
    RCLike.map 𝕜 ℂ (a * b) = RCLike.map 𝕜 ℂ a * RCLike.map 𝕜 ℂ b := by
  apply Complex.ext <;> simp [RCLike.map_apply]

/-- Fourier evaluation as a continuous real-linear functional on the actual L¹
space. This proves convergence for completed atomic sums, not just polynomials. -/
def fourierEvaluation {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (ξ : Euclidean d) :
    HardyFourierSpec.L1 𝕜 d →L[ℝ] ℂ :=
  ((BoundedContinuousFunction.evalCLM ℂ ξ).restrictScalars ℝ).comp
    (((Real.Lp.fourierTransformCLM (Euclidean d) ℂ).restrictScalars ℝ).comp
      ((RCLike.map 𝕜 ℂ).compLpL 1 volume))

lemma fourierEvaluation_apply {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (ξ : Euclidean d) (f : HardyFourierSpec.L1 𝕜 d) :
    fourierEvaluation ξ f = HardyFourierSpec.fourier (f : Euclidean d → 𝕜) ξ := by
  change 𝓕 (((RCLike.map 𝕜 ℂ).compLp f) : Euclidean d → ℂ) ξ = _
  rw [← integralFourier_eq_native]
  apply integral_congr_ae
  filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp f] with x hx
  rw [hx]

lemma fourierLp_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : 𝕜) (f : HardyFourierSpec.L1 𝕜 d) (ξ : Euclidean d) :
    HardyFourierSpec.fourier ((c • f : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) ξ =
      RCLike.map 𝕜 ℂ c * HardyFourierSpec.fourier (f : Euclidean d → 𝕜) ξ := by
  have he : (RCLike.map 𝕜 ℂ).compLp (c • f) =
      RCLike.map 𝕜 ℂ c • (RCLike.map 𝕜 ℂ).compLp f := by
    apply Lp.ext
    filter_upwards [(RCLike.map 𝕜 ℂ).coeFn_compLp (c • f), Lp.coeFn_smul c f,
      Lp.coeFn_smul (RCLike.map 𝕜 ℂ c) ((RCLike.map 𝕜 ℂ).compLp f),
      (RCLike.map 𝕜 ℂ).coeFn_compLp f] with x h1 h2 h3 h4
    rw [h1, h2, h3]
    change RCLike.map 𝕜 ℂ (c * f x) = RCLike.map 𝕜 ℂ c *
      ((RCLike.map 𝕜 ℂ).compLp f) x
    rw [h4]
    exact complex_map_mul _ _
  rw [← fourierEvaluation_apply, ← fourierEvaluation_apply]
  change Real.Lp.fourierTransformCLM (Euclidean d) ℂ
      ((RCLike.map 𝕜 ℂ).compLp (c • f)) ξ = _
  rw [he, map_smul]
  rfl

lemma weightedLp_measurable {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : HardyFourierSpec.L1 𝕜 d) :
    Measurable (fun ξ => ENNReal.ofReal
      (‖HardyFourierSpec.fourier (f : Euclidean d → 𝕜) ξ‖ / ‖ξ‖ ^ d)) :=
  ((fourier_continuous (MeasureTheory.L1.integrable_coeFn f)).norm.measurable.div
    (measurable_norm.pow_const d)).ennreal_ofReal

lemma weightedLp_add {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f g : HardyFourierSpec.L1 𝕜 d) :
    weightedIntegral ((f + g : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) ≤
      weightedIntegral (f : Euclidean d → 𝕜) + weightedIntegral (g : Euclidean d → 𝕜) := by
  unfold weightedIntegral
  rw [← lintegral_add_left (weightedLp_measurable f)]
  apply lintegral_mono
  intro ξ
  dsimp only
  rw [← fourierEvaluation_apply, map_add, fourierEvaluation_apply, fourierEvaluation_apply]
  calc
    ENNReal.ofReal (‖HardyFourierSpec.fourier (f : Euclidean d → 𝕜) ξ +
        HardyFourierSpec.fourier (g : Euclidean d → 𝕜) ξ‖ / ‖ξ‖ ^ d) ≤
        ENNReal.ofReal ((‖HardyFourierSpec.fourier (f : Euclidean d → 𝕜) ξ‖ +
          ‖HardyFourierSpec.fourier (g : Euclidean d → 𝕜) ξ‖) / ‖ξ‖ ^ d) :=
      ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right (norm_add_le _ _) (by positivity))
    _ = _ := by rw [add_div, ENNReal.ofReal_add (by positivity) (by positivity)]

lemma weightedLp_smul {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (c : 𝕜) (f : HardyFourierSpec.L1 𝕜 d) :
    weightedIntegral ((c • f : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) =
      ENNReal.ofReal ‖c‖ * weightedIntegral (f : Euclidean d → 𝕜) := by
  unfold weightedIntegral
  simp only [fourierLp_smul, norm_mul, norm_complex_map,
    mul_div_assoc, ENNReal.ofReal_mul (norm_nonneg c)]
  exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

/-- Fatou's lemma for the weighted integral along genuine L¹ convergence.
Fourier evaluations converge at every frequency. -/
lemma weightedLp_le_of_tendsto {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (f : ℕ → HardyFourierSpec.L1 𝕜 d) (g : HardyFourierSpec.L1 𝕜 d)
    (hfg : Tendsto f atTop (𝓝 g)) (M : ℝ≥0∞)
    (hM : ∀ n, weightedIntegral (f n : Euclidean d → 𝕜) ≤ M) :
    weightedIntegral (g : Euclidean d → 𝕜) ≤ M := by
  let q := fun (n : ℕ) (ξ : Euclidean d) => ENNReal.ofReal
    (‖HardyFourierSpec.fourier (f n : Euclidean d → 𝕜) ξ‖ / ‖ξ‖ ^ d)
  have hq (ξ : Euclidean d) : Tendsto (fun n => q n ξ) atTop
      (𝓝 (ENNReal.ofReal (‖HardyFourierSpec.fourier (g : Euclidean d → 𝕜) ξ‖ / ‖ξ‖ ^ d))) := by
    simp_rw [q, ← fourierEvaluation_apply]
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (((fourierEvaluation ξ).continuous.continuousAt.tendsto.comp hfg).norm.div_const _)
  calc
    weightedIntegral (g : Euclidean d → 𝕜) = ∫⁻ ξ, liminf (fun n => q n ξ) atTop := by
      apply lintegral_congr
      intro ξ
      exact (hq ξ).liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ ξ, q n ξ) atTop :=
      lintegral_liminf_le (fun n => weightedLp_measurable (f n))
    _ ≤ M := liminf_le_of_frequently_le (Frequently.of_forall hM)

lemma weightedLp_zero {𝕜 : Type} [RCLike 𝕜] {d : ℕ} :
    weightedIntegral ((0 : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) = 0 :=
  (weightedIntegral_congr_ae (Lp.coeFn_zero _ _ _)).trans weightedIntegral_zero

lemma weightedLp_finsetSum {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    {ι : Type} (s : Finset ι) (f : ι → HardyFourierSpec.L1 𝕜 d) :
    weightedIntegral ((∑ j ∈ s, f j : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) ≤
      ∑ j ∈ s, weightedIntegral (f j : Euclidean d → 𝕜) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact weightedLp_zero.le
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (weightedLp_add _ _).trans (add_le_add le_rfl ih)

/-- Transfer of a uniform atom estimate through an absolutely convergent
L¹ atomic series. Fatou identifies the limit with its ordinary Fourier transform. -/
lemma series_bound {𝕜 : Type} [RCLike 𝕜] {d : ℕ} (C : ℝ) (hC : 0 ≤ C)
    (ha : ∀ a : HardyFourierSpec.Atom 𝕜 d,
      weightedIntegral (a.val : Euclidean d → 𝕜) ≤ ENNReal.ofReal C)
    (a : ℕ → HardyFourierSpec.Atom 𝕜 d) (b : ℕ → 𝕜)
    (hb : Summable (fun j => ‖b j‖)) (f : HardyFourierSpec.L1 𝕜 d)
    (hf : HasSum (fun j => b j • (a j).val) f) :
    weightedIntegral (f : Euclidean d → 𝕜) ≤
      ENNReal.ofReal (C * ∑' j, ‖b j‖) := by
  apply weightedLp_le_of_tendsto _ _ hf.tendsto_sum_nat
  intro n
  calc
    weightedIntegral ((∑ j ∈ Finset.range n, b j • (a j).val : HardyFourierSpec.L1 𝕜 d) :
        Euclidean d → 𝕜) ≤
        ∑ j ∈ Finset.range n, weightedIntegral
          ((b j • (a j).val : HardyFourierSpec.L1 𝕜 d) : Euclidean d → 𝕜) :=
      weightedLp_finsetSum _ _
    _ ≤ ∑ j ∈ Finset.range n, ENNReal.ofReal (C * ‖b j‖) := by
      apply Finset.sum_le_sum
      intro j _
      rw [weightedLp_smul, ENNReal.ofReal_mul hC, mul_comm]
      exact mul_le_mul_left (ha (a j)) _
    _ = ENNReal.ofReal (C * ∑ j ∈ Finset.range n, ‖b j‖) := by
      rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun j _ => by positivity)]
    _ ≤ ENNReal.ofReal (C * ∑' j, ‖b j‖) :=
      ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left
        (hb.sum_le_tsum _ (fun _ _ => norm_nonneg _)) hC)

/-- The analytic atom estimate suffices for the full completed Hardy theorem.
The infimum is the actual quotient norm; no preferred atomic decomposition or
extra certificate is imposed on a Hardy element. -/
theorem hardy_bound_of_atom_bound (ha : HardyFourierSpec.AtomBound) : HardyBound := by
  intro d
  obtain ⟨C, hC, ha⟩ := ha d
  refine ⟨C, hC, ?_⟩
  intro 𝕜 _ h
  have hat := ha 𝕜
  have := ExpandedFA.Hardy.AtomicHardySpace.euclidean_atoms_nonempty d 𝕜
  have hcoef (c : CoefficientsValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))) :
      weightedIntegral (SynthesisValue volume c : Euclidean d → 𝕜) ≤
        ENNReal.ofReal (C * ‖c‖) := by
    obtain ⟨a, b, hb, hf⟩ := ExpandedFA.Hardy.AtomicHardySpace.coefficient_sequence volume c
    simpa only [hb.tsum_eq] using series_bound C hC hat a b hb.summable _ hf
  obtain ⟨c₀, hc₀⟩ := (KernelValue (𝕜 := 𝕜) (volume : Measure (Euclidean d))).mkQ_surjective h
  have he₀ : SynthesisValue volume c₀ = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc₀
  have hfin : weightedIntegral (EmbeddingValue volume h : Euclidean d → 𝕜) ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top (he₀ ▸ hcoef c₀)
  rw [← ENNReal.ofReal_toReal hfin]
  apply ENNReal.ofReal_le_ofReal
  apply le_of_forall_pos_le_add
  intro ε hε
  have hδ : 0 < ε / (C + 1) := div_pos hε (by linarith)
  obtain ⟨c, hc, hcn⟩ := Submodule.Quotient.norm_mk_lt h hδ
  have he : SynthesisValue volume c = EmbeddingValue volume h :=
    congrArg (EmbeddingValue volume) hc
  have hbound := ENNReal.toReal_le_of_le_ofReal (by positivity) (he ▸ hcoef c)
  have hsmall : C * (ε / (C + 1)) ≤ ε := by
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by linarith : 0 < C + 1)).mpr
    nlinarith
  calc
    _ ≤ C * ‖c‖ := hbound
    _ ≤ C * (‖h‖ + ε / (C + 1)) := mul_le_mul_of_nonneg_left hcn.le hC
    _ ≤ C * ‖h‖ + ε := by rw [mul_add]; exact add_le_add le_rfl hsmall

/-- The complex exponential on the imaginary axis is one-Lipschitz. -/
lemma norm_exp_imag_sub (s t : ℝ) :
    ‖Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t)‖ ≤ ‖s - t‖ := by
  have he : Complex.exp (Complex.I * s) - Complex.exp (Complex.I * t) =
      Complex.exp (Complex.I * t) * (Complex.exp (Complex.I * (s - t)) - 1) := by
    have harg : Complex.I * (t : ℂ) + Complex.I * ((s : ℂ) - (t : ℂ)) =
        Complex.I * (s : ℂ) := by ring
    rw [mul_sub, ← Complex.exp_add, harg, mul_one]
  rw [he, norm_mul]
  have hn : ‖Complex.exp (Complex.I * t)‖ = 1 := by simp [Complex.norm_exp]
  rw [hn, one_mul]
  simpa only [Complex.ofReal_sub] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := s - t))

/-- Low-frequency bound obtained from the original atom's cancellation. -/
lemma atom_low_frequency {d : ℕ} (a : HardyFourierSpec.Atom ℂ d)
    (c : Euclidean d) (R : ℝ) (hR : 0 < R)
    (hs : ∀ᵐ x, x ∉ Metric.closedBall c R → a.val x = 0) (ξ : Euclidean d) :
    ‖integralFourier (a.val : Euclidean d → ℂ) ξ‖ ≤ 2 * Real.pi * R * ‖ξ‖ := by
  let e : Euclidean d → ℂ := fun x => Complex.exp
    (Complex.I * ((-2 * Real.pi * inner ℝ x ξ : ℝ) : ℂ))
  have he (x : Euclidean d) : e x =
      Complex.exp (-2 * (Real.pi : ℂ) * Complex.I * (inner ℝ x ξ : ℝ)) := by
    dsimp [e]
    congr 1
    push_cast
    ring
  have hen (x : Euclidean d) : ‖e x‖ = 1 := by simp [e, Complex.norm_exp]
  have hi := MeasureTheory.L1.integrable_coeFn a.val
  have hei : Integrable (fun x => e x * a.val x) :=
    hi.bdd_mul (by fun_prop) (ae_of_all _ fun x => (hen x).le)
  have hci : Integrable (fun x => e c * a.val x) := hi.const_mul _
  have hrep : integralFourier (a.val : Euclidean d → ℂ) ξ =
      ∫ x, (e x - e c) * a.val x := by
    simp_rw [sub_mul]
    rw [integral_sub hei hci, integral_const_mul, a.property.1, mul_zero, sub_zero]
    exact integral_congr_ae (ae_of_all _ fun x => by dsimp only; rw [he])
  have hpoint : ∀ᵐ x, ‖(e x - e c) * a.val x‖ ≤
      (2 * Real.pi * R * ‖ξ‖) * ‖a.val x‖ := by
    filter_upwards [hs] with x hx
    by_cases hxB : x ∈ Metric.closedBall c R
    · rw [norm_mul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      have hxR : ‖x - c‖ ≤ R := by simpa only [dist_eq_norm] using (Metric.mem_closedBall.mp hxB)
      have hec : ‖e x - e c‖ ≤ 2 * Real.pi * ‖x - c‖ * ‖ξ‖ := by
        calc
          _ ≤ ‖(-2 * Real.pi * inner ℝ x ξ) - (-2 * Real.pi * inner ℝ c ξ)‖ :=
            norm_exp_imag_sub _ _
          _ = (2 * Real.pi) * ‖inner ℝ (x - c) ξ‖ := by
            rw [inner_sub_left]
            have hh : (-2 * Real.pi * inner ℝ x ξ) - (-2 * Real.pi * inner ℝ c ξ) =
                (-2 * Real.pi) * (inner ℝ x ξ - inner ℝ c ξ) := by ring
            rw [hh, norm_mul]
            simp
          _ ≤ _ := by
            have := norm_inner_le_norm (𝕜 := ℝ) (x - c) ξ
            nlinarith [Real.pi_pos]
      exact hec.trans (by gcongr)
    · rw [hx hxB, mul_zero, norm_zero, mul_zero]
  rw [hrep]
  calc
    ‖∫ x, (e x - e c) * a.val x‖ ≤ ∫ x, ‖(e x - e c) * a.val x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ x, (2 * Real.pi * R * ‖ξ‖) * ‖a.val x‖ := by
      apply integral_mono_ae
      · exact (hei.sub hci).norm.congr (ae_of_all _ fun x => by dsimp only [Pi.sub_apply]; rw [← sub_mul])
      · exact hi.norm.const_mul _
      · exact hpoint
    _ = (2 * Real.pi * R * ‖ξ‖) * ‖a.val‖ := by
      rw [integral_const_mul, MeasureTheory.L1.norm_eq_integral_norm]
    _ ≤ 2 * Real.pi * R * ‖ξ‖ :=
      mul_le_of_le_one_right (by positivity)
        (ExpandedFA.Hardy.AtomicHardySpace.atom_norm_le volume a)

/-- Exact radial integral used for the low frequencies. -/
lemma near_radial {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    let f : Euclidean d → ℝ := fun x =>
      (Ioo 0 r).indicator (fun t : ℝ => t / t ^ d) ‖x‖
    Integrable f ∧ (∫ x, f x) =
      (d : ℝ) * volume.real (Metric.ball (0 : Euclidean d) 1) * r := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  dsimp only
  let g : ℝ → ℝ := (Ioo 0 r).indicator (fun t : ℝ => t / t ^ d)
  let u : ℝ → ℝ := (Ioo 0 r).indicator (fun _ : ℝ => 1)
  have hprod : ∀ t ∈ Ioi (0 : ℝ), t ^ (d - 1) * g t = u t := by
    intro t ht
    by_cases htr : t < r
    · simp only [g, u, indicator_of_mem (show t ∈ Ioo 0 r from ⟨ht, htr⟩)]
      have hp : t ^ d = t ^ (d - 1) * t := by
        rw [← pow_succ, Nat.sub_add_cancel hd]
      rw [hp]
      field_simp [ne_of_gt ht.out]
    · simp [g, u, htr]
  have hu : IntegrableOn u (Ioi 0) :=
    ((integrable_indicator_iff measurableSet_Ioo).mpr
      (integrableOn_const (by simp : volume (Ioo (0 : ℝ) r) ≠ ∞))).integrableOn
  have hint : IntegrableOn (fun t : ℝ => t ^ (d - 1) * g t) (Ioi 0) :=
    hu.congr_fun (fun t ht => (hprod t ht).symm) measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · exact (integrable_fun_norm_addHaar volume).mpr
      (by simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hint)
  · rw [integral_fun_norm_addHaar volume g]
    simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hprod]
    have huval : (∫ t in Ioi (0 : ℝ), u t) = r := by
      rw [integral_indicator measurableSet_Ioo, Measure.restrict_restrict measurableSet_Ioo,
        inter_eq_left.mpr Ioo_subset_Ioi_self]
      simp [Real.volume_Ioo, hr.le, measureReal_def]
    rw [huval]
    ring

/-- Exact integrable square-weight tail. -/
lemma far_radial {d : ℕ} (hd : 0 < d) {r : ℝ} (hr : 0 < r) :
    let f : Euclidean d → ℝ := fun x =>
      (Ioi r).indicator (fun t : ℝ => (t ^ (2 * d))⁻¹) ‖x‖
    Integrable f ∧ (∫ x, f x) =
      volume.real (Metric.ball (0 : Euclidean d) 1) * (r ^ d)⁻¹ := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  dsimp only
  let g : ℝ → ℝ := (Ioi r).indicator (fun t : ℝ => (t ^ (2 * d))⁻¹)
  let u : ℝ → ℝ := (Ioi r).indicator (fun t : ℝ => t ^ (-(d : ℝ) - 1))
  have hprod : ∀ t ∈ Ioi (0 : ℝ), t ^ (d - 1) * g t = u t := by
    intro t ht
    by_cases htr : r < t
    · simp only [g, u, indicator_of_mem (show t ∈ Ioi r from htr)]
      rw [← div_eq_mul_inv, ← Real.rpow_natCast, ← Real.rpow_natCast,
        ← Real.rpow_sub ht.out]
      congr 1
      rw [Nat.cast_sub hd, Nat.cast_one, Nat.cast_mul, Nat.cast_ofNat]
      ring
    · simp [g, u, htr]
  have hu : Integrable u := (integrable_indicator_iff measurableSet_Ioi).mpr
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(d : ℝ) - 1 < -1) hr)
  have hint : IntegrableOn (fun t : ℝ => t ^ (d - 1) * g t) (Ioi 0) :=
    hu.integrableOn.congr_fun (fun t ht => (hprod t ht).symm) measurableSet_Ioi
  refine ⟨?_, ?_⟩
  · exact (integrable_fun_norm_addHaar volume).mpr
      (by simpa only [finrank_euclideanSpace_fin, smul_eq_mul] using hint)
  · rw [integral_fun_norm_addHaar volume g]
    simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul]
    rw [setIntegral_congr_fun measurableSet_Ioi hprod]
    have huval : (∫ t in Ioi (0 : ℝ), u t) = (r ^ d)⁻¹ / (d : ℝ) := by
      rw [integral_indicator measurableSet_Ioi, Measure.restrict_restrict measurableSet_Ioi,
        inter_eq_left.mpr (Ioi_subset_Ioi hr.le)]
      rw [integral_Ioi_rpow_of_lt (by linarith : -(d : ℝ) - 1 < -1) hr]
      have he : -(d : ℝ) - 1 + 1 = -(d : ℝ) := by ring
      rw [he, Real.rpow_neg hr.le, Real.rpow_natCast]
      ring
    rw [huval]
    field_simp [hdR.ne']

/-- A finite dimension-only constant; no optimal constant is claimed. -/
def dimensionConstant (d : ℕ) : ℝ :=
  4 * Real.pi * d * volume.real (Metric.ball (0 : Euclidean d) 1) + 2

lemma dimensionConstant_nonneg (d : ℕ) : 0 ≤ dimensionConstant d := by
  unfold dimensionConstant
  positivity

/-- The two frequency estimates give a bound uniform in the atom's radius
and center. The overlap of the two cutoffs avoids any boundary convention. -/
lemma complex_atom_bound {d : ℕ} (hd : 0 < d) (a : HardyFourierSpec.Atom ℂ d) :
    weightedIntegral (a.val : Euclidean d → ℂ) ≤ ENNReal.ofReal (dimensionConstant d) := by
  obtain ⟨c, R, hR, hs, h2, he⟩ :=
    ExpandedFA.Hardy.HardyCZEndpoint.atom_energy a
  let V := volume.real (Metric.ball c R)
  let ω := volume.real (Metric.ball (0 : Euclidean d) 1)
  have hV : 0 < V := ENNReal.toReal_pos
    (Metric.measure_ball_pos volume c hR).ne' measure_ball_ne_top
  have hVform : V = R ^ d * ω := by
    simp only [V, ω, measureReal_def, Measure.addHaar_ball_of_pos volume c hR,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ R ^ Module.finrank ℝ (Euclidean d))]
    simp [Euclidean]
  let F : Euclidean d → ℝ := fun ξ => ‖integralFourier (a.val : Euclidean d → ℂ) ξ‖
  let N : Euclidean d → ℝ := fun ξ =>
    (Ioo 0 (2 / R)).indicator (fun t : ℝ => t / t ^ d) ‖ξ‖
  let T : Euclidean d → ℝ := fun ξ =>
    (Ioi R⁻¹).indicator (fun t : ℝ => (t ^ (2 * d))⁻¹) ‖ξ‖
  let k := 2 * Real.pi * R
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hN := near_radial hd (div_pos two_pos hR)
  change Integrable N ∧ (∫ ξ, N ξ) = (d : ℝ) * ω * (2 / R) at hN
  have hT := far_radial hd (inv_pos.mpr hR)
  change Integrable T ∧ (∫ ξ, T ξ) = ω * ((R⁻¹) ^ d)⁻¹ at hT
  have hTv : (∫ ξ, T ξ) = V := by rw [hT.2, inv_pow, inv_inv, hVform, mul_comm]
  have hNp (ξ) : 0 ≤ N ξ := by
    exact indicator_nonneg (fun t ht => div_nonneg ht.1.le (pow_nonneg ht.1.le _)) _
  have hTp (ξ) : 0 ≤ T ξ := by
    exact indicator_nonneg (fun t ht => inv_nonneg.mpr
      (pow_nonneg ((inv_pos.mpr hR).trans ht.out).le _)) _
  have hi := MeasureTheory.L1.integrable_coeFn a.val
  have hF2 : Integrable (fun ξ => F ξ ^ 2) :=
    (ExpandedFA.Fourier.Plancherel.integral_memLp d a.val hi h2).integrable_norm_pow (by norm_num)
  have hE : (∫ ξ, F ξ ^ 2) ≤ V⁻¹ := by
    rw [ExpandedFA.Fourier.Plancherel.classical_norm d a.val hi h2]
    exact he
  let G : Euclidean d → ℝ := fun ξ => k * N ξ + V * F ξ ^ 2 + V⁻¹ * T ξ
  have hGi : Integrable G := ((hN.1.const_mul k).add (hF2.const_mul V)).add (hT.1.const_mul V⁻¹)
  have hp (ξ : Euclidean d) : F ξ / ‖ξ‖ ^ d ≤ G ξ := by
    have ht : 0 ≤ ‖ξ‖ := norm_nonneg _
    have hFn : 0 ≤ F ξ := norm_nonneg _
    by_cases ht0 : ‖ξ‖ = 0
    · simp only [ht0, zero_pow hd.ne', div_zero]
      dsimp [G]
      positivity [hNp ξ, hTp ξ]
    have htp : 0 < ‖ξ‖ := lt_of_le_of_ne ht (Ne.symm ht0)
    by_cases hnear : ‖ξ‖ < 2 / R
    · have hNv : N ξ = ‖ξ‖ / ‖ξ‖ ^ d := indicator_of_mem (show ‖ξ‖ ∈ Ioo 0 (2 / R) from ⟨htp, hnear⟩) _
      have hl := atom_low_frequency a c R hR hs ξ
      change F ξ ≤ k * ‖ξ‖ at hl
      have hq : F ξ / ‖ξ‖ ^ d ≤ k * N ξ := by
        rw [hNv, ← mul_div_assoc]
        exact div_le_div_of_nonneg_right hl (pow_nonneg ht _)
      exact hq.trans (by
        dsimp only [G]
        have h1 := mul_nonneg hV.le (sq_nonneg (F ξ))
        have h2 := mul_nonneg (inv_nonneg.mpr hV.le) (hTp ξ)
        linarith)
    · have hfar : R⁻¹ < ‖ξ‖ := by
        have hI : 0 < R⁻¹ := inv_pos.mpr hR
        have hnear' : 2 * R⁻¹ ≤ ‖ξ‖ := by simpa only [div_eq_mul_inv] using le_of_not_gt hnear
        linarith
      have hTv' : T ξ = ((‖ξ‖ ^ d)⁻¹) ^ 2 := by
        dsimp [T]
        rw [indicator_of_mem (show ‖ξ‖ ∈ Ioi R⁻¹ from hfar),
          Nat.mul_comm 2 d, pow_mul, inv_pow]
      have hy : F ξ / ‖ξ‖ ^ d ≤ V * F ξ ^ 2 + V⁻¹ * T ξ := by
        rw [hTv', div_eq_mul_inv]
        apply (mul_le_mul_iff_right₀ hV).mp
        have hcancel := congrArg (fun t : ℝ => t * ((‖ξ‖ ^ d)⁻¹) ^ 2)
          (mul_inv_cancel₀ hV.ne')
        nlinarith [sq_nonneg (V * F ξ - (‖ξ‖ ^ d)⁻¹),
          mul_nonneg (mul_nonneg hV.le hFn) (inv_nonneg.mpr (pow_nonneg ht d))]
      exact hy.trans (by dsimp [G]; linarith [mul_nonneg hk (hNp ξ)])
  have hqmeas : AEStronglyMeasurable (fun ξ => F ξ / ‖ξ‖ ^ d) := by
    have hc := fourier_continuous hi
    rw [fourier_complex] at hc
    exact (hc.norm.measurable.div (measurable_norm.pow_const d)).aestronglyMeasurable
  have hqi : Integrable (fun ξ => F ξ / ‖ξ‖ ^ d) :=
    hGi.mono' hqmeas (ae_of_all _ fun ξ => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (show 0 ≤ F ξ from norm_nonneg _) (pow_nonneg (norm_nonneg ξ) d))] using hp ξ)
  unfold weightedIntegral
  rw [fourier_complex, ← ofReal_integral_eq_lintegral_ofReal hqi (ae_of_all _ fun ξ => by positivity)]
  apply ENNReal.ofReal_le_ofReal
  apply (integral_mono_ae hqi hGi (ae_of_all _ hp)).trans
  change (∫ ξ, k * N ξ + V * F ξ ^ 2 + V⁻¹ * T ξ) ≤ dimensionConstant d
  have hadd1 := integral_add ((hN.1.const_mul k).add (hF2.const_mul V)) (hT.1.const_mul V⁻¹)
  have hadd2 := integral_add (hN.1.const_mul k) (hF2.const_mul V)
  dsimp only [Pi.add_apply] at hadd1 hadd2
  rw [hadd1, hadd2, integral_const_mul, integral_const_mul, integral_const_mul,
    hN.2, hTv, inv_mul_cancel₀ hV.ne']
  have hVE : V * (∫ ξ, F ξ ^ 2) ≤ 1 := by
    calc
      _ ≤ V * V⁻¹ := mul_le_mul_of_nonneg_left hE hV.le
      _ = 1 := mul_inv_cancel₀ hV.ne'
  have hlocal : k * ((d : ℝ) * ω * (2 / R)) = 4 * Real.pi * d * ω := by
    dsimp [k]
    field_simp
    ring
  rw [hlocal]
  dsimp [dimensionConstant, ω] at *
  linarith

/-- Canonical complexification preserves the original atom conditions and its
ordinary Fourier transform. This covers real as well as complex scalars. -/
lemma complex_atom_realization {𝕜 : Type} [RCLike 𝕜] {d : ℕ}
    (a : HardyFourierSpec.Atom 𝕜 d) :
    ∃ b : HardyFourierSpec.Atom ℂ d,
      weightedIntegral (b.val : Euclidean d → ℂ) = weightedIntegral (a.val : Euclidean d → 𝕜) := by
  let g : HardyFourierSpec.L1 ℂ d := (RCLike.map 𝕜 ℂ).compLp a.val
  have hga : (g : Euclidean d → ℂ) =ᵐ[volume] fun x => RCLike.map 𝕜 ℂ (a.val x) :=
    (RCLike.map 𝕜 ℂ).coeFn_compLp a.val
  rcases a.property with ⟨hz, c, R, hR, hm0, hmt, hb⟩
  have hg : IsAtomValue volume g := by
    refine ⟨?_, c, R, hR, hm0, hmt, ?_⟩
    · calc
        (∫ x, g x) = ∫ x, RCLike.map 𝕜 ℂ (a.val x) := integral_congr_ae hga
        _ = RCLike.map 𝕜 ℂ (∫ x, a.val x) :=
          (RCLike.map 𝕜 ℂ).integral_comp_comm (MeasureTheory.L1.integrable_coeFn a.val)
        _ = 0 := by rw [hz, map_zero]
    · filter_upwards [hga, hb] with x hx hxb
      rw [hx]
      refine ⟨fun hn => ?_, ?_⟩
      · rw [hxb.1 hn, map_zero]
      · rw [norm_complex_map]
        exact hxb.2
  refine ⟨⟨g, hg⟩, ?_⟩
  have hF : HardyFourierSpec.fourier (g : Euclidean d → ℂ) =
      HardyFourierSpec.fourier (a.val : Euclidean d → 𝕜) := by
    rw [fourier_complex]
    ext ξ
    apply integral_congr_ae
    filter_upwards [hga] with x hx
    rw [hx]
  unfold weightedIntegral
  rw [hF]

/-- Uniform atom bound, including the genuine singleton space. -/
theorem atom_bound : HardyFourierSpec.AtomBound := by
  intro d
  refine ⟨dimensionConstant d, dimensionConstant_nonneg d, ?_⟩
  intro 𝕜 _ a
  by_cases hd : 0 < d
  · obtain ⟨b, hb⟩ := complex_atom_realization a
    rw [← hb]
    exact complex_atom_bound hd b
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    subst d
    have hz := (zero_dimension 𝕜 (ExpandedFA.Hardy.AtomicHardySpace.atomElement volume a)).2
    rw [ExpandedFA.Hardy.AtomicHardySpace.embedding_atomElement] at hz
    rw [hz]
    exact bot_le

/-- The source inequality for every member of the completed atomic Hardy space,
for both scalar fields and every Euclidean dimension. -/
theorem hardy_bound : HardyBound := hardy_bound_of_atom_bound atom_bound

end ExpandedFA.PartIV.HardyFourier
