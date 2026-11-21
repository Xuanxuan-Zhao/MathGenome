import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.PartIV.KreinSpectralKernel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinSymmetricOperator
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinRealSpectralModel
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinHilbertSchmidtBridge
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.PartIV.KreinFiberAmplitudes

noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace ExpandedFA.PartIV.KreinSpectralKernel

/-- Continuous test pairings are equal simultaneously outside one null set.
No measurability assumption on the family of pairings is needed for this
quantifier exchange. This also covers the empty test space. -/
theorem common_null_set : Spec.CommonNullSet := by
  intro Ω E Y _ μ _ _ _ _ L R hcont heq
  obtain ⟨D, hD, hdense⟩ := TopologicalSpace.exists_countable_dense E
  have hall : ∀ᵐ ω ∂μ, ∀ x ∈ D, L ω x = R ω x :=
    (ae_ball_iff hD).2 (fun x _ => heq x)
  filter_upwards [hcont, hall] with ω hω hDω
  have hfun : L ω = R ω := Continuous.ext_on hdense hω.1 hω.2 hDω
  intro x
  exact congrFun hfun x

theorem spectral_test_identity : Spec.SpectralTestIdentity := by
  intro H _ _ _ p F G S M haction f
  exact (M.graph_iff _ _).mp (haction f)

/-- Tonelli's nonnegative energy is unchanged after extracting the amplitude
into the measure. The scalar kernel need not itself be measurable for this
identity; all integrals here are lower integrals. -/
theorem amplitude_energy_transfer : Spec.AmplitudeEnergyTransfer := by
  intro μ τ c hc h Z hfactor
  rw [amplitudeMeasure,
    lintegral_withDensity_eq_lintegral_mul_non_measurable₀ μ
      (hc.enorm.pow_const 2) (ae_of_all _ fun ξ => by finiteness)]
  apply lintegral_congr_ae
  filter_upwards [hfactor] with ξ hξ
  calc
    (∫⁻ t, ‖h ξ t‖ₑ ^ 2 ∂τ) = ∫⁻ t, ‖Z ξ t • c ξ‖ₑ ^ 2 ∂τ :=
      lintegral_congr_ae (hξ.mono fun t ht => by
        change ‖h ξ t‖ₑ ^ 2 = ‖Z ξ t • c ξ‖ₑ ^ 2
        rw [ht])
    _ = ∫⁻ t, ‖c ξ‖ₑ ^ 2 * ‖Z ξ t‖ₑ ^ 2 ∂τ := by
      simp_rw [enorm_smul, mul_pow, mul_comm (‖Z ξ _‖ₑ ^ 2)]
    _ = ‖c ξ‖ₑ ^ 2 * ∫⁻ t, ‖Z ξ t‖ₑ ^ 2 ∂τ :=
      lintegral_const_mul' _ _ (by finiteness)

theorem factored_local_energy : Spec.FactoredLocalEnergy := by
  intro H _ _ _ p F G S M K c hc hfactor R hR
  have heq := amplitude_energy_transfer M.μ (intervalMeasure R) c hc K.h
    (fun ξ t => (solution p ξ t : ℂ))
    (hfactor.mono fun _ hξ => ae_restrict_of_ae hξ)
  have hnorm (ξ t : ℝ) : ‖(solution p ξ t : ℂ)‖ₑ ^ 2 =
      ENNReal.ofReal (|solution p ξ t| ^ 2) := by
    rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _)]
  simp_rw [hnorm] at heq
  rw [← heq, K.energy R hR]
  exact ENNReal.ofReal_lt_top

/-- A strictly positive continuous weight with finite integral controls the
measure on a neighborhood of every point. This is the exact local-finiteness
step needed after proving continuity and positivity of the solution energy. -/
theorem locally_finite_of_positive_weight : Spec.LocalFinitenessCriterion := by
  intro X _ _ _ ν q hq hpos hint
  constructor
  intro x
  have hε : 0 < q x / 2 := half_pos (hpos x)
  have hε0 : ENNReal.ofReal (q x / 2) ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  refine ⟨{y | q x / 2 < q y},
    (isOpen_lt continuous_const hq).mem_nhds (by exact half_lt_self (hpos x)), ?_⟩
  apply lt_of_le_of_lt (measure_mono ?_)
    ((meas_ge_le_lintegral_div hq.measurable.ennreal_ofReal.aemeasurable
      hε0 ENNReal.ofReal_ne_top).trans_lt (ENNReal.div_lt_top hint.ne hε0))
  intro y hy
  exact ENNReal.ofReal_le_ofReal hy.le

/-- The complete spectral-kernel construction from the original positivity
hypothesis, with no spectral-model, kernel, or amplitude assumption. -/
theorem spectral_kernel : Spec.Main := by
  intro p F hF he hpos
  obtain ⟨H, hnorm, hinner, hcomplete, hsep, G,
    S₀, hdom, haction, hsym, hreal, hclose, S, hext, hself⟩ :=
    KreinSymmetricOperator.krein_symmetric_operator p F hF he hpos
  letI := hnorm
  letI := hinner
  letI := hcomplete
  letI := hsep
  have hle : S₀ ≤ S := S₀.le_closure.trans hext
  have hactionS : ∀ f : KreinSymmetricOperator.Spec.SmoothTest p,
      ∃ hf : KreinSymmetricOperator.Spec.testIntegral G.vectors f.val ∈ S.domain,
        S ⟨KreinSymmetricOperator.Spec.testIntegral G.vectors f.val, hf⟩ =
          KreinSymmetricOperator.Spec.testIntegral G.vectors (deriv (deriv f.val)) := by
    intro f
    obtain ⟨hf, hvalue⟩ := haction f
    exact ⟨hle.1 hf, (hle.2 rfl).symm.trans hvalue⟩
  obtain ⟨M⟩ := KreinRealSpectralModel.exists_model H S hself
  obtain ⟨K⟩ := KreinHilbertSchmidtBridge.exists_kernel G S M hactionS
  exact ⟨H, hnorm, hinner, hcomplete, hsep, G, S₀, S,
    hdom, haction, hsym, hreal, hclose, hext, hself,
    M, K, KreinFiberAmplitudes.exists_amplitude K⟩

end ExpandedFA.PartIV.KreinSpectralKernel
