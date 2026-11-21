import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerIntegral
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerDominatedConvergence

/-!
Dominated convergence for the Bochner integral, paper.tex:17026–17068.
The extended integral of the norm error tends to zero by scalar dominated
convergence with the bound `2 * g`. Taking its real value gives the stated
L¹ convergence; continuity of integration in L¹ gives convergence in the
Banach-space norm topology. Accepted identification theorems connect all
measurability and integrability claims to the paper's simple approximations.
-/

noncomputable section
open Filter MeasureTheory
open scoped ENNReal Topology
universe u v

namespace ExpandedFA.FunctionSpaces

theorem bochner_dominated_convergence :
    BochnerDominatedConvergenceSpec.DominatedConvergence.{u,v} := by
  intro X E _ _ _ _ μ F f g hF hg hbound hlim
  have hFm : ∀ n, AEStronglyMeasurable (F n) μ := fun n =>
    (strongMeasurable_identification μ (F n)).mp (hF n)
  have hgi : Integrable g μ := (bochnerIntegrable_identification μ g).mp hg
  have hlim' : ∀ᵐ x ∂μ, Tendsto (fun n => F n x) atTop (𝓝 (f x)) :=
    hlim.mono fun _ hx => tendsto_iff_norm_sub_tendsto_zero.mpr hx
  have hfm : AEStronglyMeasurable f μ :=
    aestronglyMeasurable_of_tendsto_ae atTop hFm hlim'
  have hFi : ∀ n, Integrable (F n) μ := fun n => hgi.mono' (hFm n) (hbound n)
  have hfi : Integrable f μ :=
    ⟨hfm, hasFiniteIntegral_of_dominated_convergence hgi.hasFiniteIntegral hbound hlim'⟩
  have hdiff : ∀ n, Integrable (fun x => F n x - f x) μ := fun n => (hFi n).sub hfi
  have herror :
      Tendsto (fun n => ∫⁻ x, ‖F n x - f x‖ₑ ∂μ) atTop (𝓝 0) := by
    simpa only [ofReal_norm] using
      tendsto_lintegral_norm_of_dominated_convergence hFm hgi.hasFiniteIntegral hbound hlim'
  have herror_real :
      Tendsto (fun n => ∫ x, ‖F n x - f x‖ ∂μ) atTop (𝓝 0) := by
    have ht := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp herror
    simpa only [Function.comp_def, ENNReal.toReal_zero,
      ← integral_norm_eq_lintegral_enorm (hdiff _).aestronglyMeasurable] using ht
  exact ⟨(strongMeasurable_identification μ f).mpr hfm,
    fun n => (bochnerIntegrable_identification μ (F n)).mpr (hFi n),
    (bochnerIntegrable_identification μ f).mpr hfi,
    fun n => (bochnerIntegrable_identification μ (fun x => ‖F n x - f x‖)).mpr
      (hdiff n).norm,
    herror_real, tendsto_integral_of_L1 f hfm (Eventually.of_forall hFi) herror⟩

end ExpandedFA.FunctionSpaces
