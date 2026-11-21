import MathGenome.Internal.LinearPDE.P201.Hyperbolic.EnergyWaveCauchy
import Mathlib.Analysis.SpecialFunctions.Sqrt
import MathGenome.Internal.LinearPDE.P201Specs.Hyperbolic.WaveEnergy
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Evolution.SymmetricHyperbolicEquation

noncomputable section
set_option maxHeartbeats 800000
open MeasureTheory Set Filter
open P201Specs.Wave P201Specs.Wave.Cauchy
open P201Specs.Wave.Energy
namespace P201.Wave.Energy

abbrev gradientSize : P201Specs.Wave.Energy.gradientSizeType :=
  P201Specs.Wave.Energy.gradientSize
abbrev magnitude : P201Specs.Wave.Energy.stateQuantityType :=
  P201Specs.Wave.Energy.magnitude
abbrev energy : P201Specs.Wave.Energy.stateQuantityType :=
  P201Specs.Wave.Energy.energy
abbrev sourceWork : P201Specs.Wave.Energy.sourceWorkType :=
  P201Specs.Wave.Energy.sourceWork

variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

lemma gradientSize_sq (u : WholeH1 n 𝕜) :
    gradientSize u ^ 2 = ∑ j : Fin n, ‖hFirstDerivative u j‖ ^ 2 :=
  P201.Wave.hGradient_norm_sq u

lemma continuous_gradientSize : Continuous (gradientSize (n := n) (𝕜 := 𝕜)) := by
  have he (u : WholeH1 n 𝕜) : gradientSize u =
      Real.sqrt (∑ j : Fin n, ‖hFirstDerivative u j‖ ^ 2) := by
    rw [← gradientSize_sq]
    exact (Real.sqrt_sq (norm_nonneg _)).symm
  change Continuous (fun u : WholeH1 n 𝕜 => gradientSize u)
  simp_rw [he]
  exact Real.continuous_sqrt.comp (continuous_finsetSum _ (fun j _ =>
    (Cauchy.Uniqueness.firstDerivativeCLM j).continuous.norm.pow 2))

lemma continuous_magnitude (c : ℝ) :
    Continuous (fun p : WholeH1 n 𝕜 × WholeL2 n 𝕜 => magnitude c p.1 p.2) := by
  exact Real.continuous_sqrt.comp
    ((continuous_snd.norm.pow 2).add
      (continuous_const.mul ((continuous_gradientSize.comp continuous_fst).pow 2)))

lemma continuous_energy (c : ℝ) :
    Continuous (fun p : WholeH1 n 𝕜 × WholeL2 n 𝕜 => energy c p.1 p.2) :=
  (continuous_magnitude c).pow 2 |>.div_const 2

lemma magnitude_nonneg (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    0 ≤ magnitude c u v := Real.sqrt_nonneg _

lemma magnitude_sq (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    magnitude c u v ^ 2 = ‖v‖ ^ 2 + c ^ 2 * gradientSize u ^ 2 :=
  Real.sq_sqrt (by positivity)

lemma energy_eq (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    energy c u v = (‖v‖ ^ 2 + c ^ 2 * gradientSize u ^ 2) / 2 := by
  rw [energy, P201Specs.Wave.Energy.energy, magnitude_sq]

lemma norm_velocity_le_magnitude (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    ‖v‖ ≤ magnitude c u v := by
  apply (sq_le_sq₀ (norm_nonneg _) (magnitude_nonneg c u v)).mp
  rw [magnitude_sq]
  exact le_add_of_nonneg_right (mul_nonneg (sq_nonneg c) (sq_nonneg _))

lemma sourceWork_eq_re_inner (f v : ℝ → WholeL2 n 𝕜) (s : ℝ) :
    sourceWork f v s = RCLike.re (inner 𝕜 (f s) (v s)) :=
by
  change (∫ x, inner ℝ (f s x) (v s x) ∂domainMeasure (⊤ : Domain n)) =
    RCLike.re (∫ x, inner 𝕜 (f s x) (v s x) ∂domainMeasure (⊤ : Domain n))
  rw [← integral_re (L2.integrable_inner (𝕜 := 𝕜) (f s) (v s))]
  rfl

/-- Only local L¹ forcing and continuity of velocity enter this proof. -/
theorem workIntegrable : P201Specs.Wave.Energy.workIntegrableStatement := by
  intro n 𝕜 _ f v hf hv r t hr hrt
  have hsub : Icc r t ⊆ Ici (0 : ℝ) := fun s hs => hr.trans hs.1
  have hv' := hv.mono hsub
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hv'
  apply (innerSL ℝ : WholeL2 n 𝕜 →L[ℝ] WholeL2 n 𝕜 →L[ℝ] ℝ).integrable_of_bilin_of_bdd_right C
      ((hf t (hr.trans hrt)).mono_set (fun s hs => ⟨hr.trans hs.1, hs.2⟩))
      (hv'.aestronglyMeasurable measurableSet_Icc)
  exact (ae_restrict_mem measurableSet_Icc).mono (fun s hs => hC s hs)

lemma magnitude_integrable (c : ℝ) (u : ℝ → WholeH1 n 𝕜)
    (v : ℝ → WholeL2 n 𝕜) (hu : ContinuousOn u (Ici 0))
    (hv : ContinuousOn v (Ici 0)) (r t : ℝ) (hr : 0 ≤ r) :
    IntegrableOn (fun s => magnitude c (u s) (v s)) (Icc r t) := by
  have hsub : Icc r t ⊆ Ici (0 : ℝ) := fun s hs => hr.trans hs.1
  exact ((continuous_magnitude c).comp_continuousOn
    ((hu.mono hsub).prodMk (hv.mono hsub))).integrableOn_Icc

/-- The displacement increment is the Bochner integral of the velocity,
including the one-sided initial trace. -/
theorem displacement_increment (c : ℝ) (g : WholeH1 n 𝕜)
    (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hz : IsEnergySolution c g h f u v)
    (r t : ℝ) (hr : 0 ≤ r) (hrt : r ≤ t) :
    hUnderlying ⊤ 1 (u t) - hUnderlying ⊤ 1 (u r) = ∫ s in r..t, v s := by
  have hsub : uIcc r t ⊆ Ici (0 : ℝ) := by
    rw [uIcc_of_le hrt]
    exact fun s hs => hr.trans hs.1
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDeriv_right
    ((hUnderlying ⊤ 1).continuous.comp_continuousOn (hz.1.mono hsub))
    _ (hz.2.1.mono hsub).intervalIntegrable
  intro s hs
  have hsr : r < s := by simpa only [min_eq_left hrt] using hs.1
  have hs0 : 0 ≤ s := hr.trans hsr.le
  exact (hz.2.2.1 s hs0).mono (fun y hy => hs0.trans hy.le)

/-- The third displayed inequality does not require a second time derivative. -/
theorem displacementEstimate : P201Specs.Wave.Energy.displacementEstimateStatement := by
  intro n 𝕜 _ c g h f u v hz r t hr hrt
  have hsub : uIcc r t ⊆ Ici (0 : ℝ) := by
    rw [uIcc_of_le hrt]
    exact fun s hs => hr.trans hs.1
  have hvI : IntervalIntegrable (fun s => ‖v s‖) volume r t :=
    (hz.2.1.mono hsub).norm.intervalIntegrable
  have hGI : IntervalIntegrable (fun s => magnitude c (u s) (v s)) volume r t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr
      (magnitude_integrable c u v hz.1 hz.2.1 r t hr)
  have hle := intervalIntegral.integral_mono_on hrt hvI hGI
    (fun s _ => norm_velocity_le_magnitude c (u s) (v s))
  calc
    ‖hUnderlying ⊤ 1 (u t)‖ ≤ ‖hUnderlying ⊤ 1 (u r)‖ +
        ‖hUnderlying ⊤ 1 (u t) - hUnderlying ⊤ 1 (u r)‖ := by
      have hh := norm_le_insert (hUnderlying ⊤ 1 (u r)) (hUnderlying ⊤ 1 (u t))
      rw [norm_sub_rev] at hh
      exact hh
    _ = ‖hUnderlying ⊤ 1 (u r)‖ + ‖∫ s in r..t, v s‖ := by
      rw [displacement_increment c g h f u v hz r t hr hrt]
    _ ≤ _ := add_le_add (le_refl _)
      ((intervalIntegral.norm_integral_le_integral_norm (f := v) hrt).trans hle)

/-- A useful bound for the causal Bochner integral, uniform in the terminal time. -/
lemma convolution_norm_le {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [NormedSpace ℝ F]
    (A : ℝ → E →L[𝕜] F) (f : ℝ → E) (T t M : ℝ)
    (ht : t ∈ Icc 0 T) (hM : 0 ≤ M)
    (hA : ∀ r ∈ Icc 0 T, ‖A r‖ ≤ M) (hf : IntegrableOn f (Icc 0 T)) :
    ‖∫ s in Icc 0 t, A (t-s) (f s)‖ ≤ M * ∫ s in Icc 0 T, ‖f s‖ := by
  have hsub : Icc 0 t ⊆ Icc 0 T := fun s hs => ⟨hs.1, hs.2.trans ht.2⟩
  calc
    _ ≤ ∫ s in Icc 0 t, M * ‖f s‖ := by
      apply norm_integral_le_of_norm_le ((hf.mono_set hsub).norm.const_mul M)
      filter_upwards [ae_restrict_mem measurableSet_Icc] with s hs
      exact ((A _).le_opNorm _).trans (mul_le_mul_of_nonneg_right
        (hA (t-s) ⟨sub_nonneg.mpr hs.2, by linarith [hs.1, ht.2]⟩) (norm_nonneg _))
    _ = M * ∫ s in Icc 0 t, ‖f s‖ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_mono_set hf.norm (ae_of_all _ (fun _ => norm_nonneg _))
        (ae_of_all _ (fun _ hs => hsub hs))) hM

lemma displacement_sub (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (g₁ g₂ : WholeH1 n 𝕜) (h₁ h₂ : WholeL2 n 𝕜)
    (f₁ f₂ : ℝ → WholeL2 n 𝕜)
    (hf₁ : LocallyIntegrableForcing f₁) (hf₂ : LocallyIntegrableForcing f₂)
    (t : ℝ) (ht : 0 ≤ t) :
    displacement W g₁ h₁ f₁ t - displacement W g₂ h₂ f₂ t =
      displacement W (g₁-g₂) (h₁-h₂) (fun s => f₁ s - f₂ s) t := by
  have hi₁ := (Cauchy.duhamelIntegrable c κ W hW f₁ hf₁ t ht).1
  have hi₂ := (Cauchy.duhamelIntegrable c κ W hW f₂ hf₂ t ht).1
  simp only [displacement, map_sub, integral_sub hi₁ hi₂]
  abel

lemma velocity_sub (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (g₁ g₂ : WholeH1 n 𝕜) (h₁ h₂ : WholeL2 n 𝕜)
    (f₁ f₂ : ℝ → WholeL2 n 𝕜)
    (hf₁ : LocallyIntegrableForcing f₁) (hf₂ : LocallyIntegrableForcing f₂)
    (t : ℝ) (ht : 0 ≤ t) :
    velocity W g₁ h₁ f₁ t - velocity W g₂ h₂ f₂ t =
      velocity W (g₁-g₂) (h₁-h₂) (fun s => f₁ s - f₂ s) t := by
  have hi₁ := (Cauchy.duhamelIntegrable c κ W hW f₁ hf₁ t ht).2
  have hi₂ := (Cauchy.duhamelIntegrable c κ W hW f₂ hf₂ t ht).2
  simp only [velocity, map_sub, integral_sub hi₁ hi₂]
  abel

lemma displacement_norm_le (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (T t : ℝ) (ht : t ∈ Icc 0 T) (hf : IntegrableOn f (Icc 0 T)) :
    ‖displacement W g h f t‖ ≤ ‖g‖ + Real.sqrt (T^2 + c⁻¹^2) * ‖h‖ +
      Real.sqrt (T^2 + c⁻¹^2) * ∫ s in Icc 0 T, ‖f s‖ := by
  have hB := hW.2.2.2.2.1
  have hS (r : ℝ) (hr : r ∈ Icc 0 T) : ‖W.S r‖ ≤ Real.sqrt (T^2 + c⁻¹^2) := by
    apply (hB r).2.2.1.trans
    apply Real.sqrt_le_sqrt
    nlinarith [hr.1, hr.2]
  have hC : ‖W.C1 t g‖ ≤ ‖g‖ := by
    simpa using ((W.C1 t).le_opNorm g).trans
      (mul_le_mul_of_nonneg_right (hB t).2.1 (norm_nonneg _))
  have hS' := ((W.S t).le_opNorm h).trans
    (mul_le_mul_of_nonneg_right (hS t ht) (norm_nonneg _))
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hC hS'))
    (convolution_norm_le W.S f T t _ ht (Real.sqrt_nonneg _) hS hf))

lemma velocity_norm_le (c : ℝ) (κ : 𝕜 →L[ℝ] ℂ) (W : WaveOperators n 𝕜)
    (hW : WaveFamilyLaws c κ W)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜) (f : ℝ → WholeL2 n 𝕜)
    (T t : ℝ) (ht : t ∈ Icc 0 T) (hf : IntegrableOn f (Icc 0 T)) :
    ‖velocity W g h f t‖ ≤ |c| * ‖g‖ + ‖h‖ + ∫ s in Icc 0 T, ‖f s‖ := by
  have hB := hW.2.2.2.2.1
  have hD : ‖W.D t g‖ ≤ |c| * ‖g‖ :=
    ((W.D t).le_opNorm g).trans (mul_le_mul_of_nonneg_right
      ((hB t).2.2.2.trans (le_abs_self c)) (norm_nonneg _))
  have hC : ‖W.C0 t h‖ ≤ ‖h‖ := by
    simpa using ((W.C0 t).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right (hB t).1 (norm_nonneg _))
  have hI : ‖∫ s in Icc 0 t, W.C0 (t-s) (f s)‖ ≤ ∫ s in Icc 0 T, ‖f s‖ := by
    simpa using convolution_norm_le W.C0 f T t 1 ht zero_le_one
      (fun r _ => (hB r).1) hf
  exact (norm_add_le _ _).trans (add_le_add
    ((norm_add_le _ _).trans (add_le_add hD hC)) hI)

/-- A single explicit constant gives continuous dependence on all three data. -/
theorem uniformStability : P201Specs.Wave.Energy.uniformStabilityStatement := by
  intro n 𝕜 _ c κ W hW T hT
  let B := Real.sqrt (T^2 + c⁻¹^2)
  refine ⟨1 + |c| + B, by dsimp [B]; positivity, ?_⟩
  intro g₁ g₂ h₁ h₂ f₁ f₂ hf₁ hf₂ t ht
  rw [displacement_sub c κ W hW _ _ _ _ _ _ hf₁ hf₂ t ht.1,
    velocity_sub c κ W hW _ _ _ _ _ _ hf₁ hf₂ t ht.1]
  have hf := (hf₁ T hT).sub (hf₂ T hT)
  have hd := displacement_norm_le c κ W hW (g₁-g₂) (h₁-h₂) (fun s => f₁ s-f₂ s) T t ht hf
  have hv := velocity_norm_le c κ W hW (g₁-g₂) (h₁-h₂) (fun s => f₁ s-f₂ s) T t ht hf
  have hI : 0 ≤ ∫ s in Icc 0 T, ‖f₁ s - f₂ s‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hB : 0 ≤ B := Real.sqrt_nonneg _
  dsimp only [B] at hd hv ⊢
  nlinarith [norm_nonneg (g₁-g₂), norm_nonneg (h₁-h₂),
    mul_nonneg (abs_nonneg c) (norm_nonneg (h₁-h₂)),
    mul_nonneg (abs_nonneg c) hI,
    mul_nonneg hB (norm_nonneg (g₁-g₂))]


section Homogeneous
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence
open Cauchy.Uniqueness

attribute [local instance] Cauchy.Uniqueness.realInnerProductH1

/-- Dense scalar wave tests suffice for the zero-forcing dual graph,
with arbitrary prescribed initial data. -/
def homogeneousWeakEnergySolutionOfTestsWithData
    {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (D : ι → V) (hD : DenseRange D)
    (j : HilbertTriple V H) (T : ℝ) (hT : 0 ≤ T)
    (a : ℝ → Form V) (ha : ScalarC1 T a)
    (g : V) (h : H) (u : ℝ → V) (v : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt
      (fun s => j.embedding (u s)) (v t) (Ici 0) t)
    (hu0 : u 0 = g) (hv0 : v 0 = h)
    (hscalar : ∀ ψ : ι, derivativeValue T
      (fun t => inner ℝ (v t) (j.embedding (D ψ)))
      (fun t => -(a t (u t) (D ψ)))) :
    WeakEnergySolution j T a g h (0 : timeLpValue H 2 T) := by
  letI : IsFiniteMeasure (timeMeasureValue T) :=
    inferInstanceAs (IsFiniteMeasure (volume.restrict (Ioo 0 T)))
  have hum : MemLp u 2 (timeMeasureValue T) := continuousOn_time_memLp hu
  have hvm : MemLp v 2 (timeMeasureValue T) := continuousOn_time_memLp hv
  have hb : Integrable (fun t => pivotValue j (v t)) (timeMeasureValue T) :=
    ((pivotValue j).comp_memLp' hvm).integrable (by norm_num)
  have hg : Integrable (fun t => -(a t (u t))) (timeMeasureValue T) :=
    (form_apply_memLp T a ha u hum).neg.integrable (by norm_num)
  refine {
    displacement := u
    velocity := v
    acceleration := fun t => -(a t (u t))
    displacement_mem := continuousOn_time_memLp hu
    pivot_displacement_mem := continuousOn_time_memLp
      (j.embedding.continuous.comp_continuousOn hu)
    velocity_mem := continuousOn_time_memLp hv
    dual_velocity_mem := (pivotValue j).comp_memLp' hvm
    acceleration_mem := (form_apply_memLp T a ha u hum).neg
    displacement_derivative := derivativeValue_of_continuous_derivative
      j T hT u v hu hv hd
    velocity_derivative := ?_
    equation := ?_
    displacement_weak := fun L => L.continuous.comp_continuousOn hu
    velocity_weak := fun L => L.continuous.comp_continuousOn hv
    initial_displacement := hu0
    initial_velocity := hv0 }
  · apply derivativeValue_of_dense_evaluations D hD T _ _ hb hg
    intro ψ
    simpa only [← pivotInjection_apply, neg_apply] using! hscalar ψ
  · filter_upwards [Lp.coeFn_zero (E := H) (p := 2)
      (μ := timeMeasureValue T)] with t ht
    simp only [ht, Pi.zero_apply, map_zero, neg_add_cancel]

/-- The actual whole-space homogeneous energy solution has the abstract graph. -/
def homogeneousWeakEnergySolution (c : ℝ) (T : ℝ) (hT : 0 ≤ T)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hz : IsEnergySolution c g h 0 u v) :
    WeakEnergySolution (wholeSpaceHilbertTriple n 𝕜) T
      (fun _ => waveForm n 𝕜 c) g h 0 := by
  have hsub : Icc 0 T ⊆ Ici (0 : ℝ) := fun _ ht => ht.1
  refine homogeneousWeakEnergySolutionOfTestsWithData testH1 testH1_denseRange
    (wholeSpaceHilbertTriple n 𝕜) T hT (fun _ => waveForm n 𝕜 c)
    (fun _ _ => contDiffOn_const) g h u v (hz.1.mono hsub) (hz.2.1.mono hsub)
    hz.2.2.1 hz.2.2.2.1 hz.2.2.2.2.1 ?_
  intro ψ
  apply homogeneous_test_first_identity c T hT u v hz.1 hz.2.1 hz.2.2.1
  intro φ
  have he := hz.2.2.2.2.2 φ
  have hi (t : ℝ) : (∫ x : Space n, (0 : WholeL2 n 𝕜) x * φ (t,x)) = 0 := by
    apply integral_eq_zero_of_ae
    have hae := Lp.coeFn_zero (E := 𝕜) (p := 2) (μ := domainMeasure (⊤ : Domain n))
    simp only [domainMeasure, P201Specs.domainMeasure, TopologicalSpace.Opens.coe_top,
      Measure.restrict_univ] at hae
    filter_upwards [hae] with x hx
    simp only [hx, Pi.zero_apply, zero_mul]
  simpa only [Pi.zero_apply, hi, integral_zero] using he

/-- This conservation theorem applies to every homogeneous energy solution. -/
theorem homogeneousConservation : P201Specs.Wave.Energy.homogeneousConservationStatement := by
  intro n 𝕜 _ c hc g h u v hz r t hr hrt
  let z := homogeneousWeakEnergySolution c t (hr.trans hrt) g h u v hz
  have he := SymmetricHyperbolicEquation.energy_identity
    (wholeSpaceHilbertTriple n 𝕜) t (hr.trans hrt)
    (fun _ => waveForm n 𝕜 c) (c^2) (c^2) (waveForm_hypotheses c hc t)
    g h 0 z r ⟨hr, hrt⟩ t ⟨hr.trans hrt, le_rfl⟩
  have hzero : (fun s : ℝ => inner ℝ
      ((0 : timeLpValue (WholeL2 n 𝕜) 2 t) s) (v s)) =ᵐ[volume.restrict (Icc r t)] 0 := by
    have hsub : volume.restrict (Icc r t) ≤ volume.restrict (Icc 0 t) :=
      Measure.restrict_mono (show Icc r t ⊆ Icc 0 t from fun s hs => ⟨hr.trans hs.1, hs.2⟩) le_rfl
    have hae : (fun s => (0 : timeLpValue (WholeL2 n 𝕜) 2 t) s) =ᵐ[volume.restrict (Icc 0 t)] 0 := by
      simpa only [timeMeasureValue, Measure.restrict_congr_set Ioo_ae_eq_Icc] using
        (Lp.coeFn_zero (E := WholeL2 n 𝕜) (p := 2) (μ := timeMeasureValue t))
    filter_upwards [hae.filter_mono (ae_mono hsub)] with s hs
    simp only [hs, inner_zero_left, Pi.zero_apply]
  have hi : (∫ s in r..t, inner ℝ
      ((0 : timeLpValue (WholeL2 n 𝕜) 2 t) s) (v s)) = 0 := by
    have hsub : uIoc r t ⊆ Icc r t := by
      rw [uIoc_of_le hrt]
      exact Ioc_subset_Icc_self
    rw [intervalIntegral.integral_congr_ae_restrict
      (hzero.filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))),
      ]
    simp only [Pi.zero_apply, intervalIntegral.integral_zero]
  have hp (s : ℝ) : SymmetricHyperbolicSpec.formPower t
      (fun _ => waveForm n 𝕜 c) u s = 0 := by
    exact congrFun (derivWithin_const (Icc 0 t) (waveForm n 𝕜 c (u s) (u s))) s
  have he' := he.2.2
  change SymmetricHyperbolicSpec.energy (fun _ => waveForm n 𝕜 c) u v t -
    SymmetricHyperbolicSpec.energy (fun _ => waveForm n 𝕜 c) u v r =
      2 * (∫ s in r..t, inner ℝ ((0 : timeLpValue (WholeL2 n 𝕜) 2 t) s) (v s)) +
      ∫ s in r..t, SymmetricHyperbolicSpec.formPower t (fun _ => waveForm n 𝕜 c) u s at he'
  simp only [hi, hp, mul_zero, intervalIntegral.integral_zero, add_zero,
    SymmetricHyperbolicSpec.energy, waveForm_apply, real_inner_self_eq_norm_sq] at he'
  change energy c (u t) (v t) = energy c (u r) (v r)
  rw [energy_eq, energy_eq, gradientSize_sq, gradientSize_sq]
  linarith

end Homogeneous

/-- Square-root energy estimate with merely integrable forcing. The positive
regularization is needed even when the energy vanishes. -/
lemma sqrt_energy_estimate (a b : ℝ) (hab : a ≤ b) (E W F : ℝ → ℝ)
    (hE : ∀ s ∈ Icc a b, 0 ≤ E s)
    (hF : ∀ s ∈ Icc a b, 0 ≤ F s)
    (hWi : IntervalIntegrable W volume a b) (hFi : IntervalIntegrable F volume a b)
    (hinc : ∀ s ∈ Icc a b, E s - E a = ∫ x in a..s, W x)
    (hbound : ∀ s ∈ Icc a b, W s ≤ F s * Real.sqrt (2 * E s)) :
    Real.sqrt (2 * E b) ≤ Real.sqrt (2 * E a) + ∫ s in a..b, F s := by
  open ExpandedFA.Evolution.HyperbolicWeakEnergyExistence in
  have hEac : AbsolutelyContinuousOnInterval E a b :=
    FiniteEnergy.primitive_increment_ac hWi (by simpa only [uIcc_of_le hab] using hinc)
  have hdE := ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy.primitive_increment_ae_deriv hab hWi hinc
  have hreg (δ : ℝ) (hδ : 0 < δ) :
      Real.sqrt (2 * E b + δ) ≤ Real.sqrt (2 * E a + δ) + ∫ s in a..b, F s := by
    let Q : ℝ → ℝ := fun s => 2 * E s + δ
    let R : ℝ → ℝ := fun s => Real.sqrt (Q s)
    have hQac : AbsolutelyContinuousOnInterval Q a b :=
      (hEac.const_mul 2).add (by simpa using
        (contDiff_const : ContDiff ℝ 1 (fun _ : ℝ => δ)).contDiffOn.absolutelyContinuousOnInterval)
    have hQc : ContinuousOn Q (Icc a b) := by
      simpa only [uIcc_of_le hab] using hQac.continuousOn
    obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hQc
    have hsqrt : ContDiffOn ℝ 1 Real.sqrt (Icc δ M) := by
      intro x hx
      exact (Real.contDiffAt_sqrt (by linarith [hx.1] : x ≠ 0)).contDiffWithinAt
    obtain ⟨K, hK⟩ := hsqrt.exists_lipschitzOnWith (by decide) (convex_Icc δ M) isCompact_Icc
    have hmap : MapsTo Q (uIcc a b) (Icc δ M) := by
      intro s hs
      rw [uIcc_of_le hab] at hs
      exact ⟨by dsimp [Q]; linarith [hE s hs], (le_abs_self _).trans (hM s hs)⟩
    have hRac : AbsolutelyContinuousOnInterval R a b :=
      hK.comp_absolutelyContinuousOnInterval hmap hQac
    have hdR : ∀ᵐ s ∂volume, s ∈ Icc a b →
        HasDerivAt R (W s / Real.sqrt (Q s)) s ∧ W s / Real.sqrt (Q s) ≤ F s := by
      filter_upwards [hdE] with s hs hsi
      have hpos : 0 < Q s := by dsimp [Q]; linarith [hE s hsi]
      have hspos : 0 < Real.sqrt (Q s) := Real.sqrt_pos.mpr hpos
      constructor
      · convert (((hs hsi).const_mul 2).add_const δ).sqrt hpos.ne' using 1
        dsimp [R, Q]
        field_simp
      · apply (div_le_iff₀ hspos).mpr
        exact (hbound s hsi).trans (mul_le_mul_of_nonneg_left
          (Real.sqrt_le_sqrt (by dsimp [Q]; linarith)) (hF s hsi))
    have hderiv : deriv R ≤ᵐ[volume.restrict (Icc a b)] F := by
      filter_upwards [ae_restrict_of_ae hdR, ae_restrict_mem measurableSet_Icc] with s hs hsi
      exact ((hs hsi).1.deriv ▸ (hs hsi).2)
    have hi := intervalIntegral.integral_mono_ae_restrict hab
      hRac.intervalIntegrable_deriv hFi hderiv
    rw [hRac.integral_deriv_eq_sub] at hi
    change Real.sqrt (2 * E b + δ) - Real.sqrt (2 * E a + δ) ≤ _ at hi
    linarith
  have hid : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Ioi 0)) (nhds 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hleft : Tendsto (fun δ : ℝ => Real.sqrt (2 * E b + δ))
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E b))) := by
    have hsum : Tendsto (fun δ : ℝ => 2 * E b + δ) (nhdsWithin 0 (Ioi 0))
        (nhds (2 * E b + 0)) := tendsto_const_nhds.add hid
    simpa only [add_zero, Function.comp_def] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsum
  have hright : Tendsto (fun δ : ℝ => Real.sqrt (2 * E a + δ) + ∫ s in a..b, F s)
      (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E a) + ∫ s in a..b, F s)) := by
    have hlim : Tendsto (fun δ : ℝ => Real.sqrt (2 * E a + δ))
        (nhdsWithin 0 (Ioi 0)) (nhds (Real.sqrt (2 * E a))) := by
      have hsum : Tendsto (fun δ : ℝ => 2 * E a + δ) (nhdsWithin 0 (Ioi 0))
          (nhds (2 * E a + 0)) := tendsto_const_nhds.add hid
      simpa only [add_zero, Function.comp_def] using
        Real.continuous_sqrt.continuousAt.tendsto.comp hsum
    exact hlim.add_const _
  have hpos : ∀ᶠ δ : ℝ in nhdsWithin 0 (Ioi 0), 0 < δ := self_mem_nhdsWithin
  exact le_of_tendsto_of_tendsto hleft hright
    (hpos.mono (fun δ hδ => hreg δ hδ))


lemma sqrt_two_energy (c : ℝ) (u : WholeH1 n 𝕜) (v : WholeL2 n 𝕜) :
    Real.sqrt (2 * energy c u v) = magnitude c u v := by
  have he : 2 * energy c u v = magnitude c u v ^ 2 := by
    change 2 * (magnitude c u v ^ 2 / 2) = _
    ring
  rw [he, Real.sqrt_sq (magnitude_nonneg c u v)]

/-- Once the exact balance is available, both sharp inequalities follow
without any time regularity or L²-time assumption on the forcing. -/
theorem estimatesOfBalance : P201Specs.Wave.Energy.estimatesOfBalanceStatement := by
  intro n 𝕜 _ c g h f u v hf hz hb r t hr hrt
  have hfI : IntegrableOn (fun s => ‖f s‖) (Icc r t) :=
    ((hf t (hr.trans hrt)).mono_set (fun s hs => ⟨hr.trans hs.1, hs.2⟩)).norm
  have hwI : IntervalIntegrable (sourceWork f v) volume r t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr
      (workIntegrable f v hf hz.2.1 r t hr hrt)
  have hfII : IntervalIntegrable (fun s => ‖f s‖) volume r t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr hfI
  refine ⟨hfI, magnitude_integrable c u v hz.1 hz.2.1 r t hr, ?_,
    displacementEstimate c g h f u v hz r t hr hrt⟩
  have hinc : ∀ s ∈ Icc r t,
      energy c (u s) (v s) - energy c (u r) (v r) = ∫ x in r..s, sourceWork f v x :=
    fun s hs => (hb.2 r s hr hs.1).2
  have hbound : ∀ s ∈ Icc r t, sourceWork f v s ≤
      ‖f s‖ * Real.sqrt (2 * energy c (u s) (v s)) := by
    intro s hs
    rw [sqrt_two_energy]
    exact (real_inner_le_norm (f s) (v s)).trans
      (mul_le_mul_of_nonneg_left (norm_velocity_le_magnitude c (u s) (v s)) (norm_nonneg _))
  have hg := sqrt_energy_estimate r t hrt (fun s => energy c (u s) (v s))
    (sourceWork f v) (fun s => ‖f s‖)
    (fun s _ => by change 0 ≤ magnitude c (u s) (v s)^2 / 2; positivity)
    (fun _ _ => norm_nonneg _) hwI hfII hinc hbound
  simpa only [sqrt_two_energy] using hg

/-- Source-work integrability makes absolute continuity a consequence of
all interval identities; it is not a separate assumption on the solution. -/
theorem balance_of_identity (c : ℝ) (f : ℝ → WholeL2 n 𝕜)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hf : LocallyIntegrableForcing f) (hv : ContinuousOn v (Ici 0))
    (hid : ∀ r t : ℝ, 0 ≤ r → r ≤ t →
      energy c (u t) (v t) - energy c (u r) (v r) = ∫ s in r..t, sourceWork f v s) :
    EnergyBalance c f u v := by
  constructor
  · intro T hT
    apply ExpandedFA.Evolution.HyperbolicWeakEnergyExistence.FiniteEnergy.primitive_increment_ac
      ((intervalIntegrable_iff_integrableOn_Icc_of_le hT).mpr
        (workIntegrable f v hf hv 0 T le_rfl hT))
    intro t ht
    rw [uIcc_of_le hT] at ht
    exact hid 0 t le_rfl ht.1
  · intro r t hr hrt
    exact ⟨workIntegrable f v hf hv r t hr hrt, hid r t hr hrt⟩

/-- Combining the exact balance with existence, uniqueness, stability,
and both sharp estimates gives the full theorem for a scalar field. -/
theorem energyForField_of_balance (c : ℝ) (hc : 0 < c) (κ : 𝕜 →L[ℝ] ℂ)
    (hC : cauchyForField n 𝕜 c κ) (hb : balanceForField n 𝕜 c) :
    energyForField n 𝕜 c κ := by
  obtain ⟨W, hW, hsol⟩ := hC
  refine ⟨W, hW, uniformStability c κ W hW, ?_⟩
  intro g h f hf
  obtain ⟨hI, hz, huniq⟩ := hsol g h f hf
  have hbal := hb g h f _ _ hf hz
  refine ⟨hI, hz, huniq, hbal, estimatesOfBalance c g h f _ _ hf hz hbal, ?_⟩
  intro hf0 r t hr hrt
  subst f
  exact homogeneousConservation c hc g h _ _ hz r t hr hrt

/-- Assembly of the full theorem from the exact balance for both fields. -/
theorem assemble : P201Specs.Wave.Energy.assemblyStatement := by
  intro hb n hn c hc
  obtain ⟨hreal, hcomplex⟩ := Cauchy.energyWaveCauchy n hn c hc
  exact ⟨energyForField_of_balance c hc Complex.ofRealCLM hreal (hb n hn c hc).1,
    energyForField_of_balance c hc (ContinuousLinearMap.id ℝ ℂ) hcomplex (hb n hn c hc).2⟩

section ForcedBalance
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
open SymmetricHyperbolicEquation Cauchy.Uniqueness
attribute [local instance] Cauchy.Uniqueness.realInnerProductH1

/-- The scalar distributional second equation, retaining the original L¹
forcing term. -/
lemma forced_test_second_identity (c T : ℝ) (hT : 0 ≤ T)
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f)
    (u : ℝ → WholeH1 n 𝕜) (hu : ContinuousOn u (Ici 0))
    (hpde : IsDistributionalWave c f u) (ψ : P102.U4.WholeTests n 𝕜) :
    ∀ η : ℝ → ℝ, testValue T η →
      (∫ t, deriv (deriv η) t *
        inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ))
          ∂timeMeasureValue T) =
      ∫ t, η t * (inner ℝ (f t) (hUnderlying ⊤ 1 (testH1 ψ)) -
        waveForm n 𝕜 c (u t) (testH1 ψ)) ∂timeMeasureValue T := by
  intro η hη
  let ηtest : Cauchy.TestSlices.TimeTest T := ⟨η, hη.1, hη.2.1, hη.2.2⟩
  let φ := Cauchy.TestSlices.tensorTest ηtest (conjugateTest ψ)
  have hIL := Cauchy.TestSlices.integrableOn_solution_test_pairing u hu c φ
  have hIR := Cauchy.TestSlices.integrableOn_forcing_test_pairing f hf φ
  have he := congrArg RCLike.re (hpde φ)
  rw [← integral_re hIL, ← integral_re hIR] at he
  have hforce (t : ℝ) : RCLike.re (∫ x : Space n, f t x * φ (t,x)) =
      η t * inner ℝ (f t) (hUnderlying ⊤ 1 (testH1 ψ)) := by
    simp only [φ, Cauchy.TestSlices.tensorTest_apply, mul_smul_comm, integral_smul,
      RCLike.smul_re]
    rw [testH1_inner_pairing]
    rfl
  simp_rw [φ, tensor_residual_re] at he
  change (∫ t in Ioi (0 : ℝ), deriv (deriv η) t *
    inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)) +
      η t * waveForm n 𝕜 c (u t) (testH1 ψ)) = _ at he
  change (∫ t in Ioi (0 : ℝ), _) =
    ∫ t in Ioi (0 : ℝ), RCLike.re (∫ x : Space n, f t x * φ (t,x)) at he
  simp_rw [hforce] at he
  have hη0 (t : ℝ) (ht : t ∉ Ioo 0 T) : η t = 0 :=
    image_eq_zero_of_notMem_tsupport (fun h => ht (hη.2.2 h))
  have hη20 (t : ℝ) (ht : t ∉ Ioo 0 T) : deriv (deriv η) t = 0 :=
    deriv_of_notMem_tsupport (fun h => ht (hη.2.2 (tsupport_deriv_subset h)))
  have hcut (A : ℝ → ℝ) (hA : ∀ t, t ∉ Ioo 0 T → A t = 0) :
      (∫ t in Ioi (0 : ℝ), A t) = ∫ t in Ioo 0 T, A t := by
    apply setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi
      (fun t ht => ht.1)
    exact fun t ht => hA t ht.2
  rw [hcut _ (fun t ht => by rw [hη0 t ht, hη20 t ht]; simp),
    hcut _ (fun t ht => by rw [hη0 t ht]; simp)] at he
  have huT := hu.mono (show Icc (0 : ℝ) T ⊆ Ici 0 from fun _ ht => ht.1)
  have hη2 : ContDiff ℝ 2 η := hη.1.of_le (by simp)
  have hdη : ContDiff ℝ 1 (deriv η) := hη2.deriv'
  have hddη : Continuous (deriv (deriv η)) := hdη.continuous_deriv (by norm_num)
  have hA : IntegrableOn (fun t => deriv (deriv η) t *
      inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ))) (Ioo 0 T) :=
    (hddη.continuousOn.mul
      (((hUnderlying ⊤ 1).continuous.comp_continuousOn huT).inner continuousOn_const)).integrableOn_Icc.mono_set
      Ioo_subset_Icc_self
  have hB : IntegrableOn (fun t => η t * waveForm n 𝕜 c (u t) (testH1 ψ)) (Ioo 0 T) :=
    ((hη.1.continuous.continuousOn.mul
      (((waveForm n 𝕜 c).flip (testH1 ψ)).continuous.comp_continuousOn huT)).integrableOn_Icc).mono_set
      Ioo_subset_Icc_self
  have hC : IntegrableOn (fun t => η t * inner ℝ (f t)
      (hUnderlying ⊤ 1 (testH1 ψ))) (Ioo 0 T) := by
    have hi := ((innerSL ℝ (E := WholeL2 n 𝕜)).flip
      (hUnderlying ⊤ 1 (testH1 ψ))).integrable_comp (hf T hT)
    exact (IntegrableOn.continuousOn_mul hη.1.continuous.continuousOn hi isCompact_Icc).mono_set
      Ioo_subset_Icc_self
  rw [integral_add hA hB] at he
  simp_rw [mul_sub]
  change (∫ t in Ioo 0 T, _) = ∫ t in Ioo 0 T, _
  rw [integral_sub hC hB]
  linarith

/-- Passing from the prescribed continuous first derivative to its weak
derivative only needs local integrability of the second derivative. -/
lemma scalar_second_to_first_integrable (T : ℝ) (hT : 0 ≤ T) (p r q : ℝ → ℝ)
    (hp : ContinuousOn p (Icc 0 T)) (hr : ContinuousOn r (Icc 0 T))
    (hq : Integrable q (timeMeasureValue T))
    (hd : ∀ t ∈ Ici (0 : ℝ), HasDerivWithinAt p (r t) (Ici 0) t)
    (hsecond : ∀ φ : ℝ → ℝ, testValue T φ →
      (∫ t, deriv (deriv φ) t * p t ∂timeMeasureValue T) =
        ∫ t, φ t * q t ∂timeMeasureValue T) :
    derivativeValue T r q := by
  let j : HilbertTriple ℝ ℝ :=
    ⟨ContinuousLinearMap.id ℝ ℝ, Function.injective_id, denseRange_id⟩
  have hpr := derivativeValue_of_continuous_derivative j T hT p r hp hr hd
  refine ⟨(hr.mono Ioo_subset_Icc_self).locallyIntegrableOn measurableSet_Ioo,
    (show IntegrableOn q (Ioo 0 T) volume from hq).locallyIntegrableOn, ?_⟩
  intro φ hφ
  have hdφ : testValue T (deriv φ) :=
    ⟨hφ.1.deriv', hφ.2.1.deriv, tsupport_deriv_subset.trans hφ.2.2⟩
  have h₁ := hpr.2.2 (deriv φ) hdφ
  have h₂ := hsecond φ hφ
  simp only [smul_eq_mul, j, ContinuousLinearMap.id_apply] at h₁ ⊢
  linarith

lemma forced_test_first_identity (c T : ℝ) (hT : 0 ≤ T)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hz : IsEnergySolution c g h f u v) (ψ : P102.U4.WholeTests n 𝕜) :
    derivativeValue T
      (fun t => inner ℝ (v t) (hUnderlying ⊤ 1 (testH1 ψ)))
      (fun t => inner ℝ (f t) (hUnderlying ⊤ 1 (testH1 ψ)) -
        waveForm n 𝕜 c (u t) (testH1 ψ)) := by
  have hsub : Icc (0 : ℝ) T ⊆ Ici 0 := fun _ ht => ht.1
  have huT := hz.1.mono hsub
  have hvT := hz.2.1.mono hsub
  apply scalar_second_to_first_integrable T hT
    (fun t => inner ℝ (hUnderlying ⊤ 1 (u t)) (hUnderlying ⊤ 1 (testH1 ψ)))
    _ _
  · exact ((hUnderlying ⊤ 1).continuous.comp_continuousOn huT).inner continuousOn_const
  · exact hvT.inner continuousOn_const
  · have hfI := ((innerSL ℝ (E := WholeL2 n 𝕜)).flip
        (hUnderlying ⊤ 1 (testH1 ψ))).integrable_comp (hf T hT)
    have haI : IntegrableOn (fun t => waveForm n 𝕜 c (u t) (testH1 ψ)) (Icc 0 T) :=
      (((waveForm n 𝕜 c).flip (testH1 ψ)).continuous.comp_continuousOn huT).integrableOn_Icc
    exact (show IntegrableOn (fun t => inner ℝ (f t)
      (hUnderlying ⊤ 1 (testH1 ψ)) - waveForm n 𝕜 c (u t) (testH1 ψ))
        (Icc 0 T) volume from hfI.sub haI).mono_set Ioo_subset_Icc_self
  · intro t ht
    simpa only [inner_zero_right, zero_add] using!
      (hz.2.2.1 t ht).inner ℝ (hasDerivWithinAt_const t (Ici (0 : ℝ))
        (hUnderlying ⊤ 1 (testH1 ψ)))
  · exact forced_test_second_identity c T hT f hf u hz.1 hz.2.2.2.2.2 ψ

/-- Dense spatial tests identify the dual velocity primitive for L¹ forces.
This construction is generic to keep the actual Banach structures fixed. -/
lemma dual_increment_of_tests {V H : Type*}
    [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {ι : Type*} (D : ι → V) (hD : DenseRange D)
    (j : HilbertTriple V H) (a : Form V) (T : ℝ) (hT : 0 < T)
    (u : ℝ → V) (v f : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hf : IntegrableOn f (Icc 0 T))
    (hscalar : ∀ ψ, derivativeValue T
      (fun t => inner ℝ (v t) (j.embedding (D ψ)))
      (fun t => inner ℝ (f t) (j.embedding (D ψ)) - a (u t) (D ψ))) :
    ∀ s t : Icc (0 : ℝ) T,
      pivotValue j (v t) - pivotValue j (v s) =
        ∫ r in (s : ℝ)..(t : ℝ), (pivotValue j (f r) - a (u r)) := by
  have hb : Integrable (fun t => pivotValue j (v t)) (timeMeasureValue T) :=
    ((pivotValue j).continuous.comp_continuousOn hv).integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hg : Integrable (fun t => pivotValue j (f t) - a (u t)) (timeMeasureValue T) :=
    (show IntegrableOn (fun t => pivotValue j (f t) - a (u t)) (Icc 0 T) volume from
      ((pivotValue j).integrable_comp hf).sub
        (a.continuous.comp_continuousOn hu).integrableOn_Icc).mono_set Ioo_subset_Icc_self
  have hd : derivativeValue T (fun t => pivotValue j (v t))
      (fun t => pivotValue j (f t) - a (u t)) := by
    apply derivativeValue_of_dense_evaluations D hD T _ _ hb hg
    intro ψ
    simpa only [← pivotInjection_apply, sub_apply] using! hscalar ψ
  exact (primitive_of_weaklyContinuousOn T hT _ _ hb hg hd
    (fun L => L.continuous.comp_continuousOn
      ((pivotValue j).continuous.comp_continuousOn hv))).2

end ForcedBalance
end P201.Wave.Energy


/-! Time averaging for continuous Hilbert-triple states with Bochner L¹ forcing.
The primitive identities are proved from the PDE below, rather than assumed in
the wave theorem. -/
namespace P201.Wave.L1Balance
open scoped Topology
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec SymmetricHyperbolicSpec
open HyperbolicWeakEnergyExistence HyperbolicWeakEnergyUniqueness
open SymmetricHyperbolicEquation

variable {V H : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

lemma forcing_limit (T B : ℝ) (hB : 0 ≤ B) (hBT : B < T)
    (f v : ℝ → H) (hf : IntegrableOn f (Icc 0 T))
    (hv : ContinuousOn v (Icc 0 T)) :
    Tendsto (fun h : ℝ => ∫ r in 0..B,
      inner ℝ (timeAverage f h r) (timeAverage v h r))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in 0..B, inner ℝ (f r) (v r))) := by
  let F : ℝ → H := (Ioo 0 T).indicator f
  have hF : Integrable F volume :=
    (integrable_indicator_iff measurableSet_Ioo).mpr (hf.mono_set Ioo_subset_Icc_self)
  have hlim := forcing_work_tendsto_of_L1_average T B hB hBT F hF v hv
    (timeAverage_L1_tendsto F hF B hB)
  change Tendsto (fun h : ℝ => ∫ r in 0..B,
      inner ℝ (timeAverage ((Ioo 0 T).indicator f) h r) (timeAverage v h r))
      (𝓝[>] (0 : ℝ)) (𝓝 (∫ r in 0..B,
        inner ℝ ((Ioo 0 T).indicator f r) (v r))) at hlim
  rw [forcing_zeroExtension_work T B hB hBT.le f v] at hlim
  exact hlim.congr' (forcing_zeroExtension_average_work T B hB hBT f v)

lemma regularized_balance (j : HilbertTriple V H) (a : Form V)
    (hsym : ∀ x y, a x y = a y x)
    (T B h : ℝ) (hB : 0 < B) (hh : 0 < h) (hBh : B+h ≤ T)
    (u : ℝ → V) (v f : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hf : IntegrableOn f (Icc 0 T))
    (hdu : ∀ s t : Icc (0 : ℝ) T,
      j.embedding (u t) - j.embedding (u s) = ∫ r in (s : ℝ)..(t : ℝ), v r)
    (hdv : ∀ s t : Icc (0 : ℝ) T,
      pivotValue j (v t) - pivotValue j (v s) =
        ∫ r in (s : ℝ)..(t : ℝ), (pivotValue j (f r) - a (u r))) :
    energy (fun _ => a) (timeAverage u h) (timeAverage v h) B -
      energy (fun _ => a) (timeAverage u h) (timeAverage v h) 0 =
      2 * ∫ r in 0..B, inner ℝ (timeAverage f h r) (timeAverage v h r) := by
  have hT : 0 ≤ T := by linarith
  have hBT : B ≤ T := by linarith
  have hsub : Icc 0 B ⊆ Icc 0 T := Icc_subset_Icc le_rfl hBT
  have hth (t : ℝ) (ht : t ∈ Icc 0 B) : t+h ∈ Icc 0 T :=
    ⟨by linarith [ht.1],by linarith [ht.2]⟩
  obtain ⟨hxa,hdx⟩ := timeAverage_regular hT hB.le hh.le hBh hu
  obtain ⟨hya,hdy⟩ := timeAverage_regular hT hB.le hh.le hBh hv
  have hyc : ContinuousOn (timeAverage v h) (Icc 0 B) := by
    simpa only [uIcc_of_le hB.le] using hya.continuousOn
  have hfi : IntervalIntegrable f volume 0 T :=
    (hf.mono_set (by rw [uIcc_of_le hT])).intervalIntegrable
  have hFc := timeAverage_continuousOn hB.le hh.le hBh hfi
  have hkin (r : ℝ) (hr : r ∈ Icc 0 B) :
      j.embedding (h⁻¹ • (u (r+h)-u r)) = timeAverage v h r := by
    simp only [map_smul, map_sub, timeAverage]
    rw [hdu ⟨r,hsub hr⟩ ⟨r+h,hth r hr⟩]
  have heq (r : ℝ) (hr : r ∈ Icc 0 B) :
      pivotValue j (h⁻¹ • (v (r+h)-v r)) + a (timeAverage u h r) =
        pivotValue j (timeAverage f h r) + (0 : StrongDual ℝ V) := by
    have hseg : uIcc r (r+h) ⊆ Icc 0 T := uIcc_subset_Icc (hsub hr) (hth r hr)
    have hfr : IntervalIntegrable f volume r (r+h) :=
      (hf.mono_set hseg).intervalIntegrable
    have hur : IntervalIntegrable u volume r (r+h) :=
      (hu.mono hseg).intervalIntegrable
    have hpfr : IntervalIntegrable (fun s => pivotValue j (f s)) volume r (r+h) :=
      ⟨(pivotValue j).integrable_comp hfr.1, (pivotValue j).integrable_comp hfr.2⟩
    have haur : IntervalIntegrable (fun s => a (u s)) volume r (r+h) :=
      ⟨a.integrable_comp hur.1, a.integrable_comp hur.2⟩
    have hi := hdv ⟨r,hsub hr⟩ ⟨r+h,hth r hr⟩
    rw [intervalIntegral.integral_sub hpfr haur,
      (pivotValue j).intervalIntegral_comp_comm hfr,
      a.intervalIntegral_comp_comm hur] at hi
    have hi' := congrArg (h⁻¹ • ·) hi
    simp only [map_smul, map_sub, timeAverage, smul_sub] at hi' ⊢
    rw [hi']
    abel
  have hbal := regularized_balance_of_graphs j T B hB hBT (fun _ => a)
    (fun _ _ => contDiffOn_const) (fun _ _ => hsym)
    (timeAverage u h) (fun r => h⁻¹ • (u (r+h)-u r))
    (timeAverage v h) (fun r => h⁻¹ • (v (r+h)-v r))
    (timeAverage f h) (fun _ => (0 : StrongDual ℝ V))
    hxa hya hdx hdy hkin heq
    ((hFc.inner hyc).mono (by rw [uIcc_of_le hB.le])).intervalIntegrable
    (by simpa using (intervalIntegrable_const :
      IntervalIntegrable (fun _ : ℝ => (0 : ℝ)) volume 0 B))
  simpa only [formPower, derivWithin_fun_const, Pi.zero_apply, zero_apply,
    intervalIntegral.integral_zero, mul_zero, add_zero] using hbal

lemma interior_balance (j : HilbertTriple V H) (a : Form V)
    (hsym : ∀ x y, a x y = a y x)
    (T B : ℝ) (hB : 0 < B) (hBT : B < T)
    (u : ℝ → V) (v f : ℝ → H)
    (hu : ContinuousOn u (Icc 0 T)) (hv : ContinuousOn v (Icc 0 T))
    (hf : IntegrableOn f (Icc 0 T))
    (hdu : ∀ s t : Icc (0 : ℝ) T,
      j.embedding (u t) - j.embedding (u s) = ∫ r in (s : ℝ)..(t : ℝ), v r)
    (hdv : ∀ s t : Icc (0 : ℝ) T,
      pivotValue j (v t) - pivotValue j (v s) =
        ∫ r in (s : ℝ)..(t : ℝ), (pivotValue j (f r) - a (u r))) :
    energy (fun _ => a) u v B - energy (fun _ => a) u v 0 =
      2 * ∫ r in 0..B, inner ℝ (f r) (v r) := by
  have hleft :=
    (energy_timeAverage_tendsto hBT (show B ∈ Icc 0 B from ⟨hB.le, le_rfl⟩)
      (fun _ => a) hu hv).sub
    (energy_timeAverage_tendsto hBT (show (0 : ℝ) ∈ Icc 0 B from ⟨le_rfl, hB.le⟩)
      (fun _ => a) hu hv)
  have hright := (forcing_limit T B hB.le hBT f v hf hv).const_mul 2
  have heq : (fun h =>
      energy (fun _ => a) (timeAverage u h) (timeAverage v h) B -
      energy (fun _ => a) (timeAverage u h) (timeAverage v h) 0) =ᶠ[𝓝[>] (0 : ℝ)]
      (fun h => 2 * ∫ r in 0..B, inner ℝ (timeAverage f h r) (timeAverage v h r)) := by
    have hpos : ∀ᶠ h : ℝ in 𝓝[>] 0, 0 < h := self_mem_nhdsWithin
    have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < T-B :=
      (eventually_lt_nhds (sub_pos.mpr hBT)).filter_mono nhdsWithin_le_nhds
    filter_upwards [hpos,hsmall] with h hh hs
    exact regularized_balance j a hsym T B h hB hh (by linarith) u v f hu hv hf hdu hdv
  exact tendsto_nhds_unique hleft (hright.congr' heq.symm)

end P201.Wave.L1Balance

namespace P201.Wave.Energy
open ExpandedFA.Evolution
open HilbertTripleSpec HyperbolicFormSpec HyperbolicWeakEnergySpec
open Cauchy.Uniqueness
attribute [local instance] Cauchy.Uniqueness.realInnerProductH1
variable {n : ℕ} {𝕜 : Type} [RCLike 𝕜]

/-- The exact balance from the initial time for the full energy solution class,
with only local Bochner L¹ forcing. -/
lemma energy_identity_from_zero (c : ℝ)
    (g : WholeH1 n 𝕜) (h : WholeL2 n 𝕜)
    (f : ℝ → WholeL2 n 𝕜) (hf : LocallyIntegrableForcing f)
    (u : ℝ → WholeH1 n 𝕜) (v : ℝ → WholeL2 n 𝕜)
    (hz : IsEnergySolution c g h f u v) (B : ℝ) (hB : 0 ≤ B) :
    energy c (u B) (v B) - energy c (u 0) (v 0) =
      ∫ r in 0..B, sourceWork f v r := by
  by_cases hzero : B = 0
  · subst B
    simp
  have hBpos : 0 < B := lt_of_le_of_ne hB (Ne.symm hzero)
  let T := B + 1
  have hT : 0 < T := by dsimp [T]; linarith
  have hBT : B < T := by dsimp [T]; linarith
  have hsub : Icc 0 T ⊆ Ici (0 : ℝ) := fun _ ht => ht.1
  have hu := hz.1.mono hsub
  have hv := hz.2.1.mono hsub
  have hdu : ∀ s t : Icc (0 : ℝ) T,
      (wholeSpaceHilbertTriple n 𝕜).embedding (u t) -
        (wholeSpaceHilbertTriple n 𝕜).embedding (u s) =
        ∫ r in (s : ℝ)..(t : ℝ), v r := by
    intro s t
    change hUnderlying ⊤ 1 (u t) - hUnderlying ⊤ 1 (u s) = _
    rcases le_total (s : ℝ) (t : ℝ) with hst | hts
    · exact displacement_increment c g h f u v hz s t s.property.1 hst
    · have he := displacement_increment c g h f u v hz t s t.property.1 hts
      rw [intervalIntegral.integral_symm, ← he]
      abel
  have hdv := dual_increment_of_tests testH1 testH1_denseRange
    (wholeSpaceHilbertTriple n 𝕜) (waveForm n 𝕜 c) T hT u v f hu hv (hf T hT.le)
    (forced_test_first_identity c T hT.le g h f hf u v hz)
  have hsym : ∀ x y : WholeH1 n 𝕜, waveForm n 𝕜 c x y = waveForm n 𝕜 c y x := by
    intro x y
    simp only [waveForm_apply]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    exact real_inner_comm _ _
  have he := P201.Wave.L1Balance.interior_balance (wholeSpaceHilbertTriple n 𝕜)
    (waveForm n 𝕜 c) hsym T B hBpos hBT u v f hu hv (hf T hT.le) hdu hdv
  change SymmetricHyperbolicSpec.energy (fun _ => waveForm n 𝕜 c) u v B -
    SymmetricHyperbolicSpec.energy (fun _ => waveForm n 𝕜 c) u v 0 =
      2 * (∫ r in 0..B, inner ℝ (f r) (v r)) at he
  simp only [SymmetricHyperbolicSpec.energy, waveForm_apply,
    real_inner_self_eq_norm_sq] at he
  rw [energy_eq, energy_eq, gradientSize_sq, gradientSize_sq]
  change _ = ∫ r in 0..B, inner ℝ (f r) (v r)
  linarith

/-- The exact energy balance, including absolute continuity, holds for every
energy solution at the original L¹ regularity. -/
theorem balance (c : ℝ) : balanceForField n 𝕜 c := by
  intro g h f u v hf hz
  apply balance_of_identity c f u v hf hz.2.1
  intro r t hr hrt
  have ht := energy_identity_from_zero c g h f hf u v hz t (hr.trans hrt)
  have hr' := energy_identity_from_zero c g h f hf u v hz r hr
  have hi0r : IntervalIntegrable (sourceWork f v) volume 0 r :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hr).mpr
      (workIntegrable f v hf hz.2.1 0 r le_rfl hr)
  have hirt : IntervalIntegrable (sourceWork f v) volume r t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hrt).mpr
      (workIntegrable f v hf hz.2.1 r t hr hrt)
  have hi := intervalIntegral.integral_add_adjacent_intervals hi0r hirt
  linarith

/-- The complete source theorem: existence and uniqueness in the original
energy class, all three formulas, conservation, and continuous dependence. -/
theorem waveEnergy : P201Specs.Wave.Energy.waveEnergyStatement := by
  apply assemble
  intro n hn c hc
  exact ⟨balance (n := n) (𝕜 := ℝ) c, balance (n := n) (𝕜 := ℂ) c⟩

end P201.Wave.Energy
