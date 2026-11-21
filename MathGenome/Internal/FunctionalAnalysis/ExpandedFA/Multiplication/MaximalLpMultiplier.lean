import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Unbounded.OperatorDomains
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.FunctionSpaces.BochnerLpCompleteness
import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Multiplication.MaximalLpMultiplier
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology

namespace ExpandedFA.Multiplication

abbrev multiplierDomain : MaximalLpMultiplierSpec.DomainType :=
  MaximalLpMultiplierSpec.domainValue
abbrev maximalLpMultiplier : MaximalLpMultiplierSpec.MultiplierType :=
  MaximalLpMultiplierSpec.multiplierValue
abbrev supportedSubspace : MaximalLpMultiplierSpec.SupportedType :=
  MaximalLpMultiplierSpec.supportedValue
abbrev multiplierZeroSet : MaximalLpMultiplierSpec.ZeroSetType :=
  MaximalLpMultiplierSpec.zeroSetValue

theorem mem_multiplier_domain_iff : MaximalLpMultiplierSpec.DomainLaw := by
  intro Ω 𝕜 _ _ μ p a f
  rfl

theorem maximalLpMultiplier_apply : MaximalLpMultiplierSpec.ApplyLaw := by
  intro Ω 𝕜 _ _ μ p a f
  exact MemLp.coeFn_toLp f.2

theorem mem_supportedSubspace_iff : MaximalLpMultiplierSpec.SupportedLaw := by
  intro Ω 𝕜 _ _ μ r E f
  rfl

theorem multiplier_representatives : MaximalLpMultiplierSpec.RepresentativesLaw := by
  intro Ω 𝕜 _ _ μ p a b f g hab hfg
  apply memLp_congr_ae
  filter_upwards [hab, hfg] with x hx hy
  rw [hx, hy]

theorem maximalLpMultiplier_congr : MaximalLpMultiplierSpec.OperatorCongrLaw := by
  intro Ω 𝕜 _ _ μ p a b hab
  apply LinearPMap.ext
  · ext f
    exact multiplier_representatives μ p a b f f hab Filter.EventuallyEq.rfl
  · intro x hx hy
    apply Lp.ext
    filter_upwards [maximalLpMultiplier_apply μ p a ⟨x, hx⟩,
      maximalLpMultiplier_apply μ p b ⟨x, hy⟩, hab] with t ht hu hv
    rw [ht, hu, hv]

theorem maximalLpMultiplier_apply_representative :
    MaximalLpMultiplierSpec.ApplyRepresentativeLaw := by
  intro Ω 𝕜 _ _ μ p a f g hfg
  filter_upwards [maximalLpMultiplier_apply μ p a f, hfg] with x hx hy
  exact hx.trans (congrArg (a x * ·) hy)

/-- The graph equation in the a.e. quotient. -/
theorem mem_maximalMultiplier_graph_iff {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (μ : Measure Ω) (p : ℝ≥0∞) (a : Ω → 𝕜) (f g : Lp 𝕜 p μ) :
    (f, g) ∈ (maximalMultiplier μ p a).graph ↔
      (g : Ω → 𝕜) =ᵐ[μ] fun x => a x * f x := by
  constructor
  · intro h
    obtain ⟨x, hx, hy⟩ := (maximalMultiplier μ p a).mem_graph_iff.mp h
    dsimp at hx hy
    subst f
    rw [← hy]
    exact maximalLpMultiplier_apply μ p a x
  · intro h
    have hf : f ∈ maximalDomain μ p a := (Lp.memLp g).ae_eq h
    refine (maximalMultiplier μ p a).mem_graph_iff.mpr ⟨⟨f, hf⟩, rfl, ?_⟩
    exact Lp.ext ((maximalLpMultiplier_apply μ p a ⟨f, hf⟩).trans h.symm)

theorem maximalLpMultiplier_isClosed : MaximalLpMultiplierSpec.ClosedLaw := by
  intro Ω 𝕜 _ _ μ p _ a
  apply IsSeqClosed.isClosed
  intro u v hu huv
  have hf := (continuous_fst.tendsto v).comp huv
  have hg := (continuous_snd.tendsto v).comp huv
  obtain ⟨s, hs, hsf⟩ := (tendstoInMeasure_of_tendsto_Lp hf).exists_seq_tendsto_ae
  obtain ⟨t, ht, htg⟩ :=
    (tendstoInMeasure_of_tendsto_Lp (hg.comp hs.tendsto_atTop)).exists_seq_tendsto_ae
  apply (mem_maximalMultiplier_graph_iff μ p a v.1 v.2).mpr
  have heq : ∀ᵐ x ∂μ, ∀ n, (u (s (t n))).2 x = a x * (u (s (t n))).1 x :=
    ae_all_iff.mpr fun n => (mem_maximalMultiplier_graph_iff μ p a _ _).mp (hu _)
  filter_upwards [hsf, htg, heq] with x hfx hgx heqx
  exact tendsto_nhds_unique hgx
    (((tendsto_const_nhds.mul (hfx.comp ht.tendsto_atTop))).congr fun n => (heqx n).symm)

/-- Dominated convergence for indicators of an eventually exhaustive family.
This proof uses only the finite p-integral of f, never finiteness of μ. -/
theorem tendsto_indicator_toLp {Ω 𝕜 : Type*} [MeasurableSpace Ω] [RCLike 𝕜]
    (μ : Measure Ω) (p : ℝ≥0∞) [hp₁ : Fact (1 ≤ p)] (hp : p ≠ ∞)
    (f : Lp 𝕜 p μ) (E : ℕ → Set Ω) (hE : ∀ n, MeasurableSet (E n))
    (hcover : ∀ x, ∀ᶠ n : ℕ in atTop, x ∈ E n) :
    Tendsto (fun n => ((Lp.memLp f).indicator (hE n).nullMeasurableSet).toLp ((E n).indicator f))
      atTop (𝓝 f) := by
  have hp₀ : p ≠ 0 := (zero_lt_one.trans_le hp₁.out).ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp₀ hp
  let d : ℕ → Ω → 𝕜 := fun n => (E n).indicator f - f
  have hd (n) : AEStronglyMeasurable (d n) μ :=
    ((Lp.aestronglyMeasurable f).indicator (hE n)).sub (Lp.aestronglyMeasurable f)
  have hbound (n) : ∀ x, ‖d n x‖ₑ ≤ ‖f x‖ₑ := by
    intro x
    by_cases hx : x ∈ E n
    · simp [d, Set.indicator_of_mem hx]
    · simp [d, Set.indicator_of_notMem hx]
  have hI : Tendsto (fun n => ∫⁻ x, ‖d n x‖ₑ ^ p.toReal ∂μ) atTop (𝓝 0) := by
    have hfin : (∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ) ≠ ∞ :=
      (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp₀ hp (Lp.memLp f)).ne
    have hlim : ∀ᵐ x ∂μ,
        Tendsto (fun n => ‖d n x‖ₑ ^ p.toReal) atTop (𝓝 (0 : ℝ≥0∞)) := by
      apply Filter.Eventually.of_forall
      intro x
      apply tendsto_const_nhds.congr'
      filter_upwards [hcover x] with n hn
      simp [d, Set.indicator_of_mem hn, ENNReal.zero_rpow_of_pos hpr]
    simpa using tendsto_lintegral_of_dominated_convergence'
      (fun x => ‖f x‖ₑ ^ p.toReal) (fun n => (hd n).enorm.pow_const _)
      (fun n => Filter.Eventually.of_forall fun x => ENNReal.rpow_le_rpow (hbound n x) hpr.le)
      hfin hlim
  have hnorm : Tendsto (fun n => eLpNorm (d n) p μ) atTop (𝓝 0) := by
    simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp₀ hp (hd _)]
    simpa only [Function.comp_def, ENNReal.zero_rpow_of_pos (one_div_pos.mpr hpr)] using
      (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).continuousAt.tendsto.comp hI
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm' _ f).mpr
  convert hnorm using 1
  funext n
  apply eLpNorm_congr_ae
  filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).indicator (hE n).nullMeasurableSet)] with x hx
  exact congrArg (· - f x) hx

/-- Truncation of the multiplier gives a norm-dense maximal domain. -/
theorem maximalLpMultiplier_denselyDefined : MaximalLpMultiplierSpec.DenseLaw := by
  intro Ω 𝕜 _ _ _ _ μ p _ hp a ha
  let E : ℕ → Set Ω := fun n => {x | ‖a x‖ ≤ (n : ℝ)}
  have hE (n) : MeasurableSet (E n) := measurableSet_le ha.norm measurable_const
  intro f
  let fn (n : ℕ) : Lp 𝕜 p μ :=
    ((Lp.memLp f).indicator (hE n).nullMeasurableSet).toLp ((E n).indicator f)
  have hfn (n) : fn n ∈ (maximalMultiplier μ p a).domain := by
    apply (Lp.memLp f).of_le_mul
      (ha.aestronglyMeasurable.mul (Lp.aestronglyMeasurable (fn n)))
    filter_upwards [MemLp.coeFn_toLp ((Lp.memLp f).indicator (hE n).nullMeasurableSet)] with x hx
    change ‖a x * fn n x‖ ≤ (n : ℝ) * ‖f x‖
    rw [hx]
    by_cases h : x ∈ E n
    · rw [Set.indicator_of_mem h, norm_mul]
      exact mul_le_mul_of_nonneg_right h (norm_nonneg _)
    · rw [Set.indicator_of_notMem h, mul_zero, norm_zero]
      positivity
  apply mem_closure_of_tendsto (f := fn) (b := atTop) ?_ (Filter.Eventually.of_forall hfn)
  apply tendsto_indicator_toLp μ p hp f E hE
  intro x
  obtain ⟨N, hN⟩ := exists_nat_ge ‖a x‖
  filter_upwards [eventually_ge_atTop N] with n hn
  exact hN.trans (by exact_mod_cast hn)

end ExpandedFA.Multiplication
