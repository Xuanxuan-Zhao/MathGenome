import MathGenome.Internal.ODEDynamics.Specs.D13Unified.Ch19.UniqueErgodicUniform
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.ProbabilityCompactness
import MathGenome.Internal.ODEDynamics.D13Unified.Ch19.MeasureDefinitions
import Mathlib.Dynamics.Ergodic.EmpiricalMeasure

/-!
Unique ergodicity implies uniform convergence of real continuous orbit averages.
The key estimate is uniform in the initial point, so weak limits of empirical
measures along varying initial points are invariant. Weak compactness and
uniqueness then imply convergence along every such sequence. Failure of a
uniform bound would supply a sequence contradicting that conclusion. Finally,
compactness bounds the real supremum and the uniform bounds force it to zero.
-/

open Filter MeasureTheory
open scoped Topology

namespace D13Unified.Ch19

noncomputable section

variable {K : Type*} [MetricSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

/-- The telescoping estimate remains valid when the initial point varies. -/
lemma empirical_integral_difference_tendsto (T : K → K) (g : K → ℝ)
    (hg : Continuous g) (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (x : ℕ → K) :
    Tendsto (fun k =>
      (∫ y, (g ∘ T) y ∂empiricalMeasure T (x k) (m k)) -
        ∫ y, g y ∂empiricalMeasure T (x k) (m k)) atTop (𝓝 0) := by
  obtain ⟨C, hC⟩ := Metric.isBounded_range_iff.mp (isCompact_range hg).isBounded
  have hlim : Tendsto (fun k => C / ((m k + 1 : ℕ) : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop
      (tendsto_natCast_atTop_atTop.comp (tendsto_atTop_mono (fun k => Nat.le_succ (m k)) hm))
  apply squeeze_zero_norm _ hlim
  intro k
  simp only [integral_empiricalMeasure_eq_birkhoffaverage,
    birkhoffAverage_apply_congr_ring NNReal ℝ, birkhoffAverage_comp_apply,
    ← dist_eq_norm, dist_birkhoffAverage_apply_birkhoffAverage]
  gcongr
  exact hC _ _

/-- Every weak empirical limit is invariant, including for varying initial points. -/
lemma empirical_limit_preserves (T : K → K) (hT : Continuous T)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (x : ℕ → K)
    (μ : ProbabilityMeasure K)
    (hμ : ∀ g : K → ℝ, Continuous g →
      Tendsto (fun k => ∫ y, g y ∂empiricalMeasure T (x k) (m k)) atTop
        (𝓝 (∫ y, g y ∂(μ : Measure K)))) :
    MeasureDefinitions.PreservesMeasure T (μ : Measure K) := by
  refine ⟨hT.measurable, ?_⟩
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro g
  rw [integral_map hT.aemeasurable g.continuous.aestronglyMeasurable]
  apply sub_eq_zero.mp
  exact tendsto_nhds_unique
    ((hμ (g ∘ T) (g.continuous.comp hT)).sub (hμ g g.continuous))
    (empirical_integral_difference_tendsto T g g.continuous m hm x)

variable [Nonempty K]

/-- Under uniqueness, averages converge even along arbitrary varying initial points. -/
lemma averages_varying_points (T : K → K) (hT : Continuous T)
    (ν : ProbabilityMeasure K)
    (hunique : ∀ η : ProbabilityMeasure K,
      MeasureDefinitions.PreservesMeasure T (η : Measure K) → η = ν)
    (g : K → ℝ) (hg : Continuous g)
    (m : ℕ → ℕ) (hm : Tendsto m atTop atTop) (x : ℕ → K) :
    Tendsto (fun k => birkhoffAverage ℝ T g (m k + 1) (x k)) atTop
      (𝓝 (∫ y, g y ∂(ν : Measure K))) := by
  apply tendsto_of_subseq_tendsto
  intro ns hns
  obtain ⟨ms, hms, μ, hμ⟩ := probability_compactness K
    (fun k => (empiricalMeasure T (x (ns k)) (m (ns k))).toProbabilityMeasure)
  have hpres : MeasureDefinitions.PreservesMeasure T (μ : Measure K) :=
    empirical_limit_preserves T hT (fun k => m (ns (ms k)))
      (hm.comp (hns.comp hms.tendsto_atTop)) (fun k => x (ns (ms k))) μ hμ
  have heq := hunique μ hpres
  subst μ
  refine ⟨ms, ?_⟩
  simpa only [Measure.coe_toProbabilityMeasure,
    integral_empiricalMeasure_eq_birkhoffaverage,
    birkhoffAverage_apply_congr_ring NNReal ℝ] using hμ g hg

/-- The varying-point conclusion forces a single bound valid at every point. -/
lemma averages_uniform_bound (T : K → K) (hT : Continuous T)
    (ν : ProbabilityMeasure K)
    (hunique : ∀ η : ProbabilityMeasure K,
      MeasureDefinitions.PreservesMeasure T (η : Measure K) → η = ν)
    (g : K → ℝ) (hg : Continuous g) :
    ∀ ε > 0, ∀ᶠ n : ℕ in atTop, ∀ x : K,
      |birkhoffAverage ℝ T g (n + 1) x - ∫ y, g y ∂(ν : Measure K)| < ε := by
  intro ε hε
  by_contra h
  have hfreq : ∃ᶠ n : ℕ in atTop, ∃ x : K,
      ε ≤ |birkhoffAverage ℝ T g (n + 1) x - ∫ y, g y ∂(ν : Measure K)| := by
    simpa only [not_eventually, not_forall, not_lt] using h
  obtain ⟨m, hm, hbad⟩ := exists_seq_forall_of_frequently hfreq
  choose x hx using hbad
  have hlim := averages_varying_points T hT ν hunique g hg m hm x
  have hsmall : ∀ᶠ k in atTop,
      |birkhoffAverage ℝ T g (m k + 1) (x k) - ∫ y, g y ∂(ν : Measure K)| < ε := by
    simpa only [Metric.mem_ball, Real.dist_eq] using
      hlim.eventually (Metric.ball_mem_nhds _ hε)
  obtain ⟨k, hk⟩ := hsmall.exists
  exact (not_lt_of_ge (hx k)) hk

/-- `paper.tex`, Theorem `d13:19:unique-ergodic-uniform`. -/
theorem unique_ergodic_uniform : Specs.D13Unified.Ch19.UniqueErgodicUniform := by
  intro K _ _ _ _ _ T hT ν _ hν g hg
  have hbdd (n : ℕ) : BddAbove (Set.range (fun x : K =>
      |birkhoffAverage ℝ T g n x - ∫ y, g y ∂(ν : Measure K)|)) := by
    have havg : Continuous (fun x : K => birkhoffAverage ℝ T g n x) := by
      unfold birkhoffAverage birkhoffSum
      exact (show Continuous (fun _ : K => (n : ℝ)⁻¹) from continuous_const).smul
        (continuous_finsetSum _ (fun j _ => hg.comp (hT.iterate j)))
    exact (isCompact_range ((havg.sub continuous_const).abs)).bddAbove
  have hpos (n : ℕ) : 0 ≤ ⨆ x : K,
      |birkhoffAverage ℝ T g n x - ∫ y, g y ∂(ν : Measure K)| :=
    (abs_nonneg _).trans (le_ciSup (hbdd n) (Classical.arbitrary K))
  have hlim : Tendsto (fun n : ℕ => ⨆ x : K,
      |birkhoffAverage ℝ T g (n + 1) x - ∫ y, g y ∂(ν : Measure K)|)
      atTop (𝓝 0) := by
    apply Metric.tendsto_atTop.mpr
    intro ε hε
    obtain ⟨N, hN⟩ := eventually_atTop.mp
      (averages_uniform_bound T hT ν hν g hg (ε / 2) (half_pos hε))
    refine ⟨N, fun n hn => ?_⟩
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (hpos (n + 1))]
    exact lt_of_le_of_lt (ciSup_le (fun x => (hN n hn x).le)) (half_lt_self hε)
  exact (tendsto_add_atTop_iff_nat 1).mp hlim

end
end D13Unified.Ch19
