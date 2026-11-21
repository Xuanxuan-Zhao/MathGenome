import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.RoydenGeneralVitali
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import Mathlib.MeasureTheory.Function.UniformIntegrable

/-!
General-measure Royden Vitali theorem, paper.tex:5282–5293.
We use the native finite-measure Vitali theorem only after proving that the
shared small-set control implies its `UnifIntegrable` hypothesis at p = 1.
Restriction to a finite-measure tail set then gives local L1 convergence.
Fatou bounds the limit's outside integral, and the triangle inequality joins
the three errors. Integrability of the limit remains an explicit hypothesis.
-/

open Set Filter MeasureTheory
open scoped Topology ENNReal
universe u v
noncomputable section
namespace D11.Ch17.RoydenGeneralVitali
open D11.Ch17.UniformControls D11.Ch06.ScalarIntegral

/-- The source absolute integral is the native L1 lower integral. -/
theorem absoluteIntegral_eq_lintegral_enorm
    {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (A : Set X) :
    absoluteIntegral μ f A = ∫⁻ x in A, ‖f x‖ₑ ∂μ := by
  simp only [absoluteIntegral_formula, ofReal_norm]

/-- At exponent one, the native small-set predicate follows from the shared
source predicate. The half-delta handles its strict measure bound. -/
theorem unifIntegrable_of_uiSmall
    {X : Type u} {ι : Type v} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ι → X → 𝕜) (h : uiSmall μ F) :
    UnifIntegrable F 1 μ := by
  apply unifIntegrable_iff'.mpr
  intro ε hε
  by_cases htop : ε = ∞
  · exact ⟨1, by simp, fun _ _ _ _ => by simp [htop]⟩
  have hεr : 0 < ε.toReal := ENNReal.toReal_pos hε.ne' htop
  obtain ⟨δ, hδ, hbound⟩ := h.2 ε.toReal hεr
  refine ⟨ENNReal.ofReal (δ / 2), ENNReal.ofReal_pos.mpr (half_pos hδ), ?_⟩
  intro i A hA hμA
  have hμA' : μ A < ENNReal.ofReal δ :=
    hμA.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hδ).mpr (half_lt_self hδ))
  have hi : Measurable (F i) := (h.1 i).1
  rw [eLpNorm_one_eq_lintegral_enorm hi.aestronglyMeasurable.restrict]
  calc
    (∫⁻ x in A, ‖F i x‖ₑ ∂μ) = absoluteIntegral μ (F i) A :=
      (absoluteIntegral_eq_lintegral_enorm μ (F i) A).symm
    _ ≤ integralSup μ F A := le_iSup (fun j => absoluteIntegral μ (F j) A) i
    _ ≤ ENNReal.ofReal ε.toReal := (hbound A hA hμA').le
    _ = ε := ENNReal.ofReal_toReal htop

/-- Local L1 convergence on any measurable set of finite measure. -/
theorem tendsto_absoluteIntegral_on_finite
    {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜)
    (h : uiSmall μ F) (hf : scalarIntegrable μ f)
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (E : Set X) (_hE : MeasurableSet E) (hfinite : μ E < ∞) :
    Tendsto (fun n => absoluteIntegral μ (fun x => F n x - f x) E)
      atTop (𝓝 0) := by
  let : IsFiniteMeasure (μ.restrict E) := ⟨by simpa using hfinite⟩
  have hfn : Integrable f μ := (scalarIntegrable_iff μ f).mp hf |>.2
  have hm : ∀ n, Measurable (F n) := fun n => (h.1 n).1
  have hc := tendsto_Lp_finite_of_tendsto_ae (μ := μ.restrict E)
    (p := 1) (by rfl) (by simp)
    (fun n => (hm n).aestronglyMeasurable.restrict)
    (memLp_one_iff_integrable.mpr hfn.restrict)
    ((unifIntegrable_of_uiSmall μ F h).restrict E)
    (ae_of_all _ hlim)
  simpa only [absoluteIntegral_eq_lintegral_enorm,
    eLpNorm_one_eq_lintegral_enorm
      (((hm _).sub hf.1).aestronglyMeasurable.restrict), Pi.sub_apply] using hc

/-- Fatou transfers a common absolute-integral bound to the pointwise limit,
on any fixed measurable domain (and in fact on every restricted measure). -/
theorem absoluteIntegral_limit_le
    {X : Type u} [MeasurableSpace X] {𝕜 : Type} [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ℕ → X → 𝕜) (f : X → 𝕜)
    (hF : ∀ n, Measurable (F n))
    (hlim : ∀ x, Tendsto (fun n => F n x) atTop (𝓝 (f x)))
    (A : Set X) (b : ℝ≥0∞) (hb : ∀ n, absoluteIntegral μ (F n) A ≤ b) :
    absoluteIntegral μ f A ≤ b := by
  simp only [absoluteIntegral_eq_lintegral_enorm] at hb ⊢
  calc
    (∫⁻ x in A, ‖f x‖ₑ ∂μ) =
        ∫⁻ x in A, liminf (fun n => ‖F n x‖ₑ) atTop ∂μ := by
      apply lintegral_congr
      intro x
      exact (hlim x).enorm.liminf_eq.symm
    _ ≤ liminf (fun n => ∫⁻ x in A, ‖F n x‖ₑ ∂μ) atTop :=
      lintegral_liminf_le (fun n => (hF n).enorm)
    _ ≤ liminf (fun _ : ℕ => b) atTop :=
      liminf_le_liminf (Eventually.of_forall hb)
    _ = b := liminf_const _

/-- Royden's general-measure Vitali conclusion, including L1 convergence.
The integrability of the proposed limit is retained verbatim. -/
theorem general_vitali : Specs.D11.Ch17.RoydenGeneralVitali.general_vitali := by
  intro X _ 𝕜 _ _ _ μ F f hF hf hsmall htails hlim
  change ∀ n, scalarIntegrable μ (F n) at hF
  change scalarIntegrable μ f at hf
  change uiSmall μ F at hsmall
  change spatialTails μ F at htails
  change Tendsto (fun n => absoluteIntegral μ (fun x => F n x - f x) univ)
      atTop (𝓝 0) ∧ Tendsto (fun n => scalarIntegral μ (F n) (hF n))
      atTop (𝓝 (scalarIntegral μ f hf))
  have hm : ∀ n, Measurable (F n) := fun n => (hF n).1
  have hnative : ∀ n, Integrable (F n) μ :=
    fun n => (scalarIntegrable_iff μ (F n)).mp (hF n) |>.2
  have hfnative : Integrable f μ := (scalarIntegrable_iff μ f).mp hf |>.2
  have hL1 : Tendsto (fun n => absoluteIntegral μ (fun x => F n x - f x) univ)
      atTop (𝓝 0) := by
    apply ENNReal.tendsto_atTop_zero.mpr
    intro ε hε
    by_cases htop : ε = ∞
    · exact ⟨0, fun _ _ => by simp [htop]⟩
    have hεr : 0 < ε.toReal / 3 := div_pos (ENNReal.toReal_pos hε.ne' htop) (by norm_num)
    let b : ℝ≥0∞ := ENNReal.ofReal (ε.toReal / 3)
    have hb : 0 < b := ENNReal.ofReal_pos.mpr hεr
    obtain ⟨E, hE, hfinite, htail⟩ := htails.2 (ε.toReal / 3) hεr
    have hFt : ∀ n, absoluteIntegral μ (F n) Eᶜ ≤ b := fun n =>
      (le_iSup (fun n => absoluteIntegral μ (F n) Eᶜ) n).trans htail.le
    have hft : absoluteIntegral μ f Eᶜ ≤ b :=
      absoluteIntegral_limit_le μ F f hm hlim Eᶜ b hFt
    obtain ⟨N, hN⟩ := ENNReal.tendsto_atTop_zero.mp
      (tendsto_absoluteIntegral_on_finite μ F f hsmall hf hlim E hE hfinite) b hb
    refine ⟨N, fun n hn => ?_⟩
    have hdiff : (∫⁻ x in Eᶜ, ‖F n x - f x‖ₑ ∂μ) ≤
        absoluteIntegral μ (F n) Eᶜ + absoluteIntegral μ f Eᶜ := by
      simp only [absoluteIntegral_eq_lintegral_enorm]
      calc
        (∫⁻ x in Eᶜ, ‖F n x - f x‖ₑ ∂μ) ≤
            ∫⁻ x in Eᶜ, ‖F n x‖ₑ + ‖f x‖ₑ ∂μ := by
          apply lintegral_mono
          intro x
          simpa only [← ofReal_norm, ← ENNReal.ofReal_add (norm_nonneg _) (norm_nonneg _)]
            using ENNReal.ofReal_le_ofReal (norm_sub_le (F n x) (f x))
        _ = _ := lintegral_add_left (hm n).enorm _
    calc
      absoluteIntegral μ (fun x => F n x - f x) univ =
          absoluteIntegral μ (fun x => F n x - f x) E +
            (∫⁻ x in Eᶜ, ‖F n x - f x‖ₑ ∂μ) := by
        simp only [absoluteIntegral_eq_lintegral_enorm, Measure.restrict_univ]
        exact (lintegral_add_compl _ hE).symm
      _ ≤ b + (b + b) := add_le_add (hN n hn) (hdiff.trans (add_le_add (hFt n) hft))
      _ = ε := by
        dsimp [b]
        rw [← ENNReal.ofReal_add hεr.le hεr.le,
          ← ENNReal.ofReal_add hεr.le (add_nonneg hεr.le hεr.le)]
        rw [show ε.toReal / 3 + (ε.toReal / 3 + ε.toReal / 3) = ε.toReal by ring]
        exact ENNReal.ofReal_toReal htop
  refine ⟨hL1, ?_⟩
  change Tendsto (fun n => ∫ x, F n x ∂μ) atTop (𝓝 (∫ x, f x ∂μ))
  apply tendsto_integral_of_L1 f hfnative.aestronglyMeasurable
    (Eventually.of_forall hnative)
  simpa only [absoluteIntegral_eq_lintegral_enorm, Measure.restrict_univ] using hL1

end D11.Ch17.RoydenGeneralVitali
