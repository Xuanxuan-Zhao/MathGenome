import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.CompositionIsometry
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeanErgodic
import Mathlib.Tactic.Positivity

/-! Composition on Lᵖ and its Cesàro averages. No inverse of T is used. -/
namespace D13Unified.Ch19.CompositionIsometry
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
universe u v

abbrev composition : Specs.D13Unified.Ch19.CompositionIsometry.compositionType.{u,v} :=
  Specs.D13Unified.Ch19.CompositionIsometry.composition

abbrev average : Specs.D13Unified.Ch19.CompositionIsometry.averageType.{u,v} :=
  Specs.D13Unified.Ch19.CompositionIsometry.average

theorem integration : Specs.D13Unified.Ch19.CompositionIsometry.integrationStatement.{u,v} := by
  intro X _ T μ _ hT
  refine ⟨fun h hh => hT.lintegral_comp hh, ?_⟩
  intro 𝕜 _ h hh
  refine ⟨hT.integrable_comp_of_integrable hh, ?_⟩
  have hm : AEStronglyMeasurable h (Measure.map T μ) := hT.map_eq.symm ▸ hh.aestronglyMeasurable
  exact (hT.map_eq ▸ integral_map hT.aemeasurable hm).symm

section Lp
variable {X : Type u} [MeasurableSpace X] (𝕜 : Type v) [RCLike 𝕜]
  (p : ℝ≥0∞) [Fact (1 ≤ p)] (T : X → X) (μ : Measure X)
  (hT : MeasureDefinitions.PreservesMeasure T μ)

theorem composition_ae (h : Lp 𝕜 p μ) :
    composition 𝕜 p T μ hT h =ᵐ[μ] h ∘ T :=
  Lp.coeFn_compMeasurePreserving h hT

theorem composition_pow_ae (n : ℕ) (h : Lp 𝕜 p μ) :
    (composition 𝕜 p T μ hT ^ n) h =ᵐ[μ] h ∘ T^[n] := by
  have hi : (composition 𝕜 p T μ hT ^ n) h =
      Lp.compMeasurePreserving T^[n] (hT.iterate n) h := by
    rw [LinearIsometry.coe_pow]
    exact congrFun (Lp.compMeasurePreserving_iterate (E := 𝕜) (p := p) hT n) h
  rw [hi]
  exact Lp.coeFn_compMeasurePreserving h (hT.iterate n)

@[simp] theorem average_apply (n : ℕ) (h : Lp 𝕜 p μ) :
    average 𝕜 p T μ hT n h =
      (n : 𝕜)⁻¹ • ∑ j ∈ Finset.range n, (composition 𝕜 p T μ hT ^ j) h := by
  simp [average, Specs.D13Unified.Ch19.CompositionIsometry.average]

theorem average_norm_le (n : ℕ) (h : Lp 𝕜 p μ) :
    ‖average 𝕜 p T μ hT n h‖ ≤ ‖h‖ := by
  rw [average_apply, norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    (n : ℝ)⁻¹ * ‖∑ j ∈ Finset.range n, (composition 𝕜 p T μ hT ^ j) h‖ ≤
        (n : ℝ)⁻¹ * ∑ j ∈ Finset.range n, ‖(composition 𝕜 p T μ hT ^ j) h‖ :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ = (n : ℝ)⁻¹ * ((n : ℝ) * ‖h‖) := by simp
    _ ≤ ‖h‖ := by
      by_cases hn : n = 0
      · simp [hn]
      · rw [← mul_assoc, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hn), one_mul]

theorem average_ae (n : ℕ) (h : Lp 𝕜 p μ) :
    average 𝕜 p T μ hT n h =ᵐ[μ]
      MeasureDefinitions.ergodicAverage T (h : X → 𝕜) n := by
  rw [average_apply]
  have hs : (∑ j ∈ Finset.range n, (composition 𝕜 p T μ hT ^ j) h : Lp 𝕜 p μ) =ᵐ[μ]
      fun x => ∑ j ∈ Finset.range n, h (T^[j] x) := by
    apply (Lp.coeFn_finsetSum _ _).trans
    filter_upwards [eventuallyEq_sum (s := Finset.range n)
      fun j _ => composition_pow_ae 𝕜 p T μ hT j h] with x hx
    simpa only [Finset.sum_apply, Function.comp_apply] using hx
  apply (Lp.coeFn_smul _ _).trans
  filter_upwards [hs] with x hx
  simp only [Pi.smul_apply, hx, MeasureDefinitions.ergodicAverage,
    Specs.D13Unified.Ch19.MeasureDefinitions.ergodicAverage,
    birkhoffAverage, birkhoffSum]
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  simp
end Lp

theorem composition_isometry :
    Specs.D13Unified.Ch19.CompositionIsometry.compositionStatement.{u,v} := by
  intro X _ 𝕜 _ p _ T μ _ hT
  exact ⟨fun _ _ hfg => hT.quasiMeasurePreserving.ae_eq_comp hfg,
    fun _ hh => hh.comp_measurePreserving hT,
    fun h => ⟨composition_ae 𝕜 p T μ hT h, (composition 𝕜 p T μ hT).norm_map h⟩,
    composition_pow_ae 𝕜 p T μ hT⟩

theorem essentialSupremum_preserved :
    Specs.D13Unified.Ch19.CompositionIsometry.essentialSupremumStatement.{u,v} := by
  intro X _ 𝕜 _ T μ _ hT h hh
  have hm : AEStronglyMeasurable h (Measure.map T μ) := hT.map_eq.symm ▸ hh
  exact (hT.map_eq ▸ eLpNormEssSup_map_measure hm hT.aemeasurable).symm

theorem averages : Specs.D13Unified.Ch19.CompositionIsometry.averageStatement.{u,v} := by
  intro X _ 𝕜 _ p _ T μ _ hT n _
  refine ⟨?_, average_ae 𝕜 p T μ hT n⟩
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro h
  simpa only [one_mul] using average_norm_le 𝕜 p T μ hT n h

theorem l2_mean_ergodic :
    Specs.D13Unified.Ch19.CompositionIsometry.l2MeanErgodicStatement.{u,v} := by
  intro X _ 𝕜 _ T μ _ hT
  constructor
  · intro h
    rw [MeanErgodic.mem_fixedSpace]
    constructor
    · intro hh
      exact hh ▸ composition_ae 𝕜 2 T μ hT h |>.symm
    · intro hh
      exact Lp.ext ((composition_ae 𝕜 2 T μ hT h).trans hh)
  · intro h
    exact MeanErgodic.average_tendsto_projection (composition 𝕜 2 T μ hT) h

end
end D13Unified.Ch19.CompositionIsometry
