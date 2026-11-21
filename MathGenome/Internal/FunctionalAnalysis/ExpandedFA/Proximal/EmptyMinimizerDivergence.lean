import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Proximal.EmptyMinimizerDivergence
import MathGenome.Internal.FunctionalAnalysis.ExpandedFA.Proximal.LargeParameterMinimizers
import Mathlib.Topology.Order.MonotoneConvergence

/-! Large parameters when the original function has no minimizer.

The ordered-parameter estimate from the prerequisite shows that a path with
bounded squared distance to the datum is Cauchy. Nondivergence of the norms
would give such a bound, hence a strong limit. Energy comparison and the closed
epigraph place that limit below every finite competitor. This directly produces
a minimizer without any assumption that the infimum is finite or attained.
For a finite unattained infimum it contradicts nonattainment; for infimum −∞
the resulting finite global lower bound contradicts unboundedness below.
-/
noncomputable section
open Set Filter
open scoped Topology
namespace ExpandedFA.Proximal
open P1.ExtendedConvexFunctions
universe u

section Path
variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
variable (φ : ExtendedFunction H) (hp : Proper H φ) (hc : ExtendedConvex H φ)
  (hl : LowerSemicontinuous H φ) (f : H)
include hp hc hl

/-- A bounded squared radius suffices for the whole path to be Cauchy;
no prior minimizer is needed. -/
lemma proximalPath_cauchy_of_bounded_radius
    (hb : BddAbove ((fun μ : ℝ => ‖f - proximalMap H φ μ f‖ ^ 2) '' Ioi 0)) :
    CauchySeq (fun μ : ℝ => proximalMap H φ μ f) := by
  -- Clamp parameters below 1 so that the radius is monotone on all of ℝ.
  let q : ℝ → ℝ := fun μ => ‖f - proximalMap H φ (max 1 μ) f‖ ^ 2
  have hmono : Monotone q := by
    intro μ ν hμν
    have hh := (proximalPath_order_estimate φ hp hc hl f (max 1 μ) (max 1 ν)
      (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) (max_le_max_left 1 hμν)).2
    dsimp [q]
    nlinarith [sq_nonneg
      ‖proximalMap H φ (max 1 μ) f - proximalMap H φ (max 1 ν) f‖]
  have hbq : BddAbove (range q) := by
    obtain ⟨B, hB⟩ := hb
    refine ⟨B, ?_⟩
    rintro r ⟨μ, rfl⟩
    exact hB ⟨max 1 μ, lt_of_lt_of_le zero_lt_one (le_max_left 1 μ), rfl⟩
  have hqc := (tendsto_atTop_ciSup hmono hbq).cauchySeq
  rw [Metric.cauchySeq_iff'] at hqc
  rw [Metric.cauchySeq_iff']
  intro ε hε
  obtain ⟨N, hN⟩ := hqc (ε ^ 2) (sq_pos_of_pos hε)
  refine ⟨max 1 N, ?_⟩
  intro ν hν
  have hν1 : 1 ≤ ν := (le_max_left 1 N).trans hν
  have hdiff := hN ν ((le_max_right 1 N).trans hν)
  simp only [Real.dist_eq, q, max_eq_right hν1] at hdiff
  have hdiff' := lt_of_le_of_lt (le_abs_self _) hdiff
  have hh := (proximalPath_order_estimate φ hp hc hl f (max 1 N) ν
    (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hν).2
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (proximalMap H φ (max 1 N) f - proximalMap H φ ν f)]

/-- Any strong limit of the path minimizes φ, even when the infimum is not
known in advance to be finite. -/
lemma proximalPath_limit_minimizes (z : H)
    (hz : Tendsto (fun μ : ℝ => proximalMap H φ μ f) atTop (𝓝 z)) :
    z ∈ argmin H φ := by
  intro v
  by_cases hv : φ v = ⊤
  · rw [hv]
    exact le_top
  obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hv
  have ht : Tendsto (fun μ : ℝ => m + ‖f - v‖ ^ 2 / (2 * μ)) atTop (𝓝 m) := by
    have hh : Tendsto (fun μ : ℝ => (‖f - v‖ ^ 2 / 2) / μ) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    have heq (μ : ℝ) : ‖f - v‖ ^ 2 / (2 * μ) = (‖f - v‖ ^ 2 / 2) / μ := by ring
    simpa only [heq, add_zero] using tendsto_const_nhds.add hh
  have hepi := (lowerSemicontinuous_iff_closed_epigraph H φ).mp hl
  have hzval : φ z ≤ (m : WithTop ℝ) :=
    hepi.mem_of_tendsto (hz.prodMk_nhds ht) (by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with μ hμ
      exact proximalPath_value_bound φ hp hc hl f v m hm.symm μ hμ)
  exact hzval.trans hm.le

end Path

/-- Empty argmin forces norm divergence for every datum, including when φ is
unbounded below. -/
theorem proximalMap_norm_tendsto_atTop_of_argmin_empty :
    EmptyMinimizerSpec.EmptyMinimizerDivergence.{u} := by
  intro H _ _ _ φ hp hc hl hempty f
  by_contra hn
  rw [tendsto_atTop_atTop] at hn
  push Not at hn
  obtain ⟨R, hR⟩ := hn
  have hb : BddAbove ((fun μ : ℝ => ‖f - proximalMap H φ μ f‖ ^ 2) '' Ioi 0) := by
    refine ⟨(‖f‖ + |R|) ^ 2, ?_⟩
    rintro r ⟨μ, hμ, rfl⟩
    obtain ⟨ν, hμν, hν⟩ := hR μ
    have horder := (proximalPath_order_estimate φ hp hc hl f μ ν hμ hμν).2
    have hbound : ‖f - proximalMap H φ ν f‖ ≤ ‖f‖ + |R| :=
      (norm_sub_le _ _).trans (add_le_add_right (hν.le.trans (le_abs_self R)) _)
    nlinarith [sq_nonneg ‖proximalMap H φ μ f - proximalMap H φ ν f‖,
      norm_nonneg (f - proximalMap H φ ν f)]
  obtain ⟨z, hz⟩ := cauchySeq_tendsto_of_complete
    (proximalPath_cauchy_of_bounded_radius φ hp hc hl f hb)
  have hzM := proximalPath_limit_minimizes φ hp hc hl f z hz
  rw [show argmin H φ = ∅ from hempty] at hzM
  exact hzM

/-- The full large-parameter theorem, with the nonempty-minimizer projection
limit supplied by the accepted prerequisite. -/
theorem proximalMap_largeParameter_theorem : EmptyMinimizerSpec.LargeParameterTheorem.{u} :=
  ⟨proximalMap_largeParameter_limit, proximalMap_norm_tendsto_atTop_of_argmin_empty⟩

end ExpandedFA.Proximal
