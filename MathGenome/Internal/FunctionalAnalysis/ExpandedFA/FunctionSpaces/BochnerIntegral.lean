import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerDefinitions
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.FunctionSpaces.BochnerIntegral

/-!
Construction of Bochner integration (paper.tex:17026–17066).
The native integral is constructed by continuous extension of simple integration;
the proofs below identify its domain with the accepted L¹-approximation definition
and establish the extension's universal property for arbitrary positive measures.
-/

noncomputable section
open Filter MeasureTheory ENNReal
open scoped ENNReal Topology
universe u v w z

namespace ExpandedFA.FunctionSpaces
open BochnerIntegralSpec

/-- The approximation definition is exactly native Bochner integrability.
No completeness or scalar structure is needed for this identification. -/
theorem bochnerIntegrable_identification : BochnerIntegrableIdentification.{u,v} := by
  intro X E _ _ μ f
  constructor
  · rintro ⟨s, hs, ht⟩
    obtain ⟨n, hn⟩ := ((tendsto_order.1 ht).2 1 zero_lt_one).exists
    have hd : Integrable (f - ⇑(s n)) μ :=
      memLp_one_iff_integrable.mp (hn.trans one_lt_top)
    have hs' : Integrable (s n) μ :=
      (integrableSimple_identification μ (s n)).mp (hs n)
    convert hd.add hs' using 1
    ext x
    simp
  · intro hf
    have hmem : MemLp f 1 μ := memLp_one_iff_integrable.mpr hf
    have hε (n : ℕ) : (((n + 1 : ℕ) : ℝ≥0∞)⁻¹) ≠ 0 := by simp
    choose s hs hsmem using fun n =>
      hmem.exists_simpleFunc_eLpNorm_sub_lt one_ne_top (hε n)
    refine ⟨s, fun n => (integrableSimple_identification μ (s n)).mpr
      (memLp_one_iff_integrable.mp (hsmem n)), ?_⟩
    have hlim : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ≥0∞)⁻¹) atTop (𝓝 0) :=
      (tendsto_add_atTop_iff_nat 1).2 ENNReal.tendsto_inv_nat_nhds_zero
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
      (fun _ => bot_le) (fun n => (hs n).le)

/-- The paper's integrability criterion, retaining the extended integral. -/
theorem bochner_integrability_criterion : IntegrabilityCriterion.{u,v} := by
  intro X E _ _ μ f hf
  rw [bochnerIntegrable_identification]
  have hfm := (strongMeasurable_identification μ f).mp hf
  simp only [Integrable, hfm, true_and, hasFiniteIntegral_iff_enorm]

/-- The Bochner integral, totalized by zero outside its natural domain. -/
def bochnerIntegral : IntegralType.{u,v} := fun μ f => ∫ x, f x ∂μ

/-- Integration on the strongly measurable L¹ a.e. quotient, as a bounded map. -/
def bochnerIntegralL1 : IntegralL1Type.{u,v} := fun _ => L1.integralCLM

theorem bochnerIntegral_onL1 : IntegralOnL1.{u,v} := by
  intro X E _ _ _ _ μ f hf
  exact (MeasureTheory.integral_eq f hf).trans (L1.integral_eq _)

theorem bochnerIntegral_simple : IntegralSimple.{u,v} := by
  intro X E _ _ _ _ μ s hs
  exact s.integral_eq_sum ((integrableSimple_identification μ s).mp hs)

/-- The continuous extension is unique even without assuming its linearity. -/
theorem bochnerIntegral_extension : IntegralExtension.{u,v} := by
  intro X E _ _ _ _ μ
  have hs (s : Lp.simpleFunc E 1 μ) :
      IntegralL1Value μ (s : Lp E 1 μ) =
        BochnerDefinitionsSpec.SimpleIntegralValue μ (Lp.simpleFunc.toSimpleFunc s) := by
    change L1.integralCLM (s : Lp E 1 μ) = _
    rw [← L1.integral_eq, L1.SimpleFunc.integral_L1_eq_integral]
    exact SimpleFunc.integral_eq μ (Lp.simpleFunc.toSimpleFunc s)
  refine ⟨L1.integralCLM.continuous, hs, ?_⟩
  intro J hJ hJs
  apply (Lp.simpleFunc.denseRange (E := E) (μ := μ) one_ne_top).equalizer hJ
    L1.integralCLM.continuous
  funext s
  exact (hJs s).trans (hs s).symm

/-- All integrable-simple L¹ approximations converge to this same integral. -/
theorem bochnerIntegral_approximation : IntegralApproximation.{u,v} := by
  intro X E _ _ _ _ μ f s hs ht
  have hsi : ∀ n, Integrable (s n) μ := fun n =>
    (integrableSimple_identification μ (s n)).mp (hs n)
  have ht' : Tendsto (fun n => eLpNorm (⇑(s n) - f) 1 μ) atTop (𝓝 0) := by
    simpa only [eLpNorm_sub_comm] using ht
  have hi := tendsto_integral_of_L1' f (Eventually.of_forall hsi) ht'
  change Tendsto _ atTop (𝓝 (∫ x, f x ∂μ))
  convert hi using 1
  funext n
  exact (bochnerIntegral_simple μ (s n) (hs n)).symm

theorem bochnerIntegral_norm_bound : IntegralNormBound.{u,v} := by
  intro X E _ _ _ _ μ f _hf
  exact norm_integral_le_integral_norm f

theorem bochnerIntegralL1_norm_bound : IntegralL1NormBound.{u,v} := by
  intro X E _ _ _ _ μ
  exact L1.norm_Integral_le_one

/-- Closure under addition and additivity of the integral. -/
theorem bochnerIntegral_add : IntegralAdd.{u,v} := by
  intro X E _ _ _ _ μ f g hf hg
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  have hgi := (bochnerIntegrable_identification μ g).mp hg
  exact ⟨(bochnerIntegrable_identification μ (f + g)).mpr (hfi.add hgi),
    integral_add hfi hgi⟩

/-- Both real and complex scalar linearity with their canonical real structures. -/
theorem bochnerIntegral_smul {𝕜 : Type w} [RCLike 𝕜] {X : Type u} {E : Type v}
    [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    (μ : Measure X) (c : 𝕜) (f : X → E) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    BochnerIntegrable μ f → BochnerIntegrable μ (c • f) ∧
      bochnerIntegral μ (c • f) = c • bochnerIntegral μ f := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  intro hf
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  exact ⟨(bochnerIntegrable_identification μ (c • f)).mpr (hfi.smul c),
    integral_smul c f⟩

/-- Every bounded real or complex linear map preserves integrability and integration. -/
theorem bochnerIntegral_continuousLinearMap {𝕜 : Type w} [RCLike 𝕜]
    {X : Type u} {E : Type v} {F : Type z} [MeasurableSpace X]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] [CompleteSpace F]
    (μ : Measure X) (T : E →L[𝕜] F) (f : X → E) :
    letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
    letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
    BochnerIntegrable μ f → BochnerIntegrable μ (fun x => T (f x)) ∧
      T (bochnerIntegral μ f) = bochnerIntegral μ (fun x => T (f x)) := by
  letI : NormedSpace ℝ E := NormedSpace.restrictScalars ℝ 𝕜 E
  letI : NormedSpace ℝ F := NormedSpace.restrictScalars ℝ 𝕜 F
  intro hf
  have hfi := (bochnerIntegrable_identification μ f).mp hf
  exact ⟨(bochnerIntegrable_identification μ (fun x => T (f x))).mpr (T.integrable_comp hfi),
    (T.integral_comp_comm hfi).symm⟩

end ExpandedFA.FunctionSpaces
