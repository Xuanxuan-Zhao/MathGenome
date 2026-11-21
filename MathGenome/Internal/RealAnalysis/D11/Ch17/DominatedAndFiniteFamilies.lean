import MathGenome.Internal.RealAnalysis.Specs.D11.Ch17.DominatedAndFiniteFamilies
import MathGenome.Internal.RealAnalysis.D11.Ch17.UniformControls
import MathGenome.Internal.RealAnalysis.D11.Ch06.AbsoluteContinuityTails

/-!
Both controls follow from the corresponding estimates for a single majorant.
For finite families the sum of the absolute values is such a majorant; the
empty sum is zero. No global finiteness or sigma-finiteness is used.
-/
open Set MeasureTheory
open scoped ENNReal
universe u v
noncomputable section
namespace D11.Ch17.DominatedAndFiniteFamilies
open D11.Ch17.UniformControls D11.Ch06.ScalarIntegral
open D11.Ch05.NonnegativeIntegral

/-- Integral domination remains valid on every restriction, with a separate
exceptional null set allowed for each member. -/
theorem absoluteIntegral_le_of_ae_norm_le
    {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (g : X → ℝ) (A : Set X)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ ≤ g x) :
    absoluteIntegral μ f A ≤ absoluteIntegral μ g A := by
  rw [absoluteIntegral_formula, absoluteIntegral_formula]
  apply lintegral_mono_ae
  exact (ae_restrict_of_ae hfg).mono fun x hx =>
    ENNReal.ofReal_le_ofReal (hx.trans (le_abs_self (g x)))

/-- The earlier indicator convention agrees with the canonical set integral. -/
private theorem absoluteIntegral_eq_indicator
    {X : Type u} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (f : X → 𝕜) (A : Set X) (hA : MeasurableSet A) :
    absoluteIntegral μ f A =
      nonnegativeIntegral μ (A.indicator (fun x => ENNReal.ofReal ‖f x‖)) := by
  rw [absoluteIntegral_formula, integral_eq_lintegral, lintegral_indicator hA]

/-- Taking a supremum preserves the bound by one majorant's integral. -/
theorem integralSup_le_majorant
    {X : Type u} {ι : Type v} {𝕜 : Type} [MeasurableSpace X] [RCLike 𝕜]
    [MeasurableSpace 𝕜] [BorelSpace 𝕜]
    (μ : Measure X) (F : ι → X → 𝕜) (g : X → ℝ) (A : Set X)
    (hFg : ∀ i, ∀ᵐ x ∂μ, ‖F i x‖ ≤ g x) :
    integralSup μ F A ≤ absoluteIntegral μ g A := by
  exact iSup_le fun i => absoluteIntegral_le_of_ae_norm_le μ (F i) g A (hFg i)

theorem dominated_controls :
    Specs.D11.Ch17.DominatedAndFiniteFamilies.dominated_controls.{u,v} := by
  intro X ι 𝕜 _ _ _ _ μ F g hFm hg _hg0 hFg
  have hgi : Integrable g μ := (scalarIntegrable_iff μ g).mp hg |>.2
  have hFi : integrableFamily μ F := by
    intro i
    exact (scalarIntegrable_iff μ (F i)).mpr
      ⟨hFm i, hgi.mono' (hFm i).aestronglyMeasurable (hFg i)⟩
  constructor
  · refine ⟨hFi, ?_⟩
    intro ε hε
    obtain ⟨δ, hδ, hsmall⟩ :=
      D11.Ch06.AbsoluteContinuityTails.small_sets μ g hg ε hε
    refine ⟨δ, hδ, ?_⟩
    intro A hA hmass
    apply (integralSup_le_majorant μ F g A hFg).trans_lt
    rw [absoluteIntegral_eq_indicator μ g A hA]
    exact hsmall A hA hmass
  · refine ⟨hFi, ?_⟩
    intro ε hε
    obtain ⟨E, hE, hmass, htail⟩ :=
      D11.Ch06.AbsoluteContinuityTails.finite_measure_tail μ g hg ε hε
    refine ⟨E, hE, hmass, ?_⟩
    apply (integralSup_le_majorant μ F g Eᶜ hFg).trans_lt
    rw [absoluteIntegral_eq_indicator μ g Eᶜ hE.compl]
    exact htail

theorem finite_controls :
    Specs.D11.Ch17.DominatedAndFiniteFamilies.finite_controls.{u,v} := by
  intro X ι 𝕜 _ _ _ _ _ μ F hF
  letI := Fintype.ofFinite ι
  let g : X → ℝ := fun x => ∑ i, ‖F i x‖
  have hFm : ∀ i, Measurable (F i) := fun i => (hF i).1
  have hFi : ∀ i, Integrable (F i) μ := fun i =>
    (scalarIntegrable_iff μ (F i)).mp (hF i) |>.2
  have hg : scalarIntegrable μ g := by
    apply (scalarIntegrable_iff μ g).mpr
    constructor
    · exact Finset.measurable_sum _ fun i _ => (hFm i).norm
    · exact integrable_finsetSum _ fun i _ => (hFi i).norm
  apply dominated_controls μ F g hFm hg
  · exact Filter.Eventually.of_forall fun x => Finset.sum_nonneg fun i _ => norm_nonneg _
  · intro i
    exact Filter.Eventually.of_forall fun x =>
      Finset.single_le_sum (fun j _ => norm_nonneg (F j x)) (Finset.mem_univ i)

end D11.Ch17.DominatedAndFiniteFamilies
