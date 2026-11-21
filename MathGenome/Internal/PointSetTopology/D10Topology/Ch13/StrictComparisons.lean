import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.StrictComparisons
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.TopologyComparison
import Mathlib.Topology.UniformSpace.UniformApproximation
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

noncomputable section
open Set Filter
open scoped Topology
namespace D10Topology.Ch13.StrictComparisons
abbrev Interval := Specs.D10Topology.Ch13.StrictComparisons.Interval
abbrev powers := Specs.D10Topology.Ch13.StrictComparisons.powers
abbrev powerLimit := Specs.D10Topology.Ch13.StrictComparisons.powerLimit
abbrev tents := Specs.D10Topology.Ch13.StrictComparisons.tents
abbrev dilations := Specs.D10Topology.Ch13.StrictComparisons.dilations

lemma powers_continuous (n : ℕ) : Continuous (powers n) :=
  continuous_subtype_val.pow (n + 1)
lemma tents_continuous (n : ℕ) : Continuous (tents n) := by
  unfold tents Specs.D10Topology.Ch13.StrictComparisons.tents
  fun_prop
lemma dilations_continuous (n : ℕ) : Continuous (dilations n) := by
  unfold dilations Specs.D10Topology.Ch13.StrictComparisons.dilations
  fun_prop

lemma powers_pointwise (x : Interval) :
    Tendsto (fun n => powers n x) atTop (𝓝 (powerLimit x)) := by
  by_cases hx : (x : ℝ) = 1
  · simp [powers, powerLimit, Specs.D10Topology.Ch13.StrictComparisons.powers,
      Specs.D10Topology.Ch13.StrictComparisons.powerLimit, hx]
  · simpa [powers, powerLimit, Specs.D10Topology.Ch13.StrictComparisons.powers,
      Specs.D10Topology.Ch13.StrictComparisons.powerLimit, hx, Function.comp_def] using
      (tendsto_pow_atTop_nhds_zero_of_lt_one x.property.1
        (lt_of_le_of_ne x.property.2 hx)).comp (tendsto_add_atTop_nat 1)

lemma tents_pointwise (x : Interval) :
    Tendsto (fun n => tents n x) atTop (𝓝 0) := by
  by_cases hx : (x : ℝ) = 0
  · simp [tents, Specs.D10Topology.Ch13.StrictComparisons.tents, hx]
  · have hp : 0 < (x : ℝ) := lt_of_le_of_ne x.property.1 (Ne.symm hx)
    have ht : Tendsto (fun n : ℕ => (n + 1 : ℝ) * (x : ℝ)) atTop atTop :=
      (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds).atTop_mul_const hp
    have he : ∀ᶠ n : ℕ in atTop, tents n x = 0 := by
      filter_upwards [ht.eventually_ge_atTop 2] with n hn
      simp only [tents, Specs.D10Topology.Ch13.StrictComparisons.tents]
      rw [abs_of_nonneg (by linarith), max_eq_left (by linarith)]
    exact tendsto_const_nhds.congr' (he.mono fun _ hn => hn.symm)

lemma tents_peak (n : ℕ) (x : Interval) (hx : (x : ℝ) = 1 / (n + 1 : ℝ)) :
    tents n x = 1 := by
  have hp : (n + 1 : ℝ) ≠ 0 := by positivity
  simp [tents, Specs.D10Topology.Ch13.StrictComparisons.tents, hx, hp]

/-- Points approaching the right endpoint from below. -/
private def approachingOne (n : ℕ) : Interval :=
  ⟨1 - 1 / (n + 2 : ℝ), by
    constructor
    · have : 1 / (n + 2 : ℝ) ≤ 1 := (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
      linarith
    · have : 0 ≤ 1 / (n + 2 : ℝ) := by positivity
      linarith⟩

lemma powerLimit_not_continuous : ¬ Continuous powerLimit := by
  intro hc
  let one : Interval := ⟨1, by norm_num⟩
  have ht : Tendsto approachingOne atTop (𝓝 one) := by
    rw [nhds_subtype, tendsto_comap_iff]
    have hi : Tendsto (fun n : ℕ => 1 / (n + 2 : ℝ)) atTop (𝓝 (0 : ℝ)) := by
      simpa [Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (tendsto_add_atTop_nat 1)
    simpa [approachingOne, one, Function.comp_def] using tendsto_const_nhds.sub hi
  have hz : ∀ n, powerLimit (approachingOne n) = 0 := by
    intro n
    have hp : 0 < 1 / (n + 2 : ℝ) := by positivity
    change (if 1 - 1 / (n + 2 : ℝ) = 1 then (1 : ℝ) else 0) = 0
    rw [ite_eq_right (ne_of_lt (by linarith))]
  have hh := (hc.tendsto one).comp ht
  rw [show powerLimit ∘ approachingOne = (fun _ : ℕ => (0 : ℝ)) from funext hz] at hh
  have : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (1 : ℝ)) := by
    convert hh using 1; norm_num [powerLimit,
      Specs.D10Topology.Ch13.StrictComparisons.powerLimit, one]
  exact zero_ne_one (tendsto_nhds_unique tendsto_const_nhds this)

lemma powers_not_uniform : ¬ TendstoUniformly powers powerLimit atTop := by
  intro h
  exact powerLimit_not_continuous
    (h.continuous (Filter.Eventually.of_forall powers_continuous).frequently)

private def peakPoint (n : ℕ) : Interval :=
  ⟨1 / (n + 1 : ℝ), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by have := Nat.cast_nonneg (α := ℝ) n; linarith)⟩

lemma tents_not_uniform : ¬ TendstoUniformly tents (fun _ => 0) atTop := by
  intro h
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp h (1 / 2) (by norm_num)).exists
  have hp := hn (peakPoint n)
  rw [tents_peak n (peakPoint n) rfl] at hp
  norm_num at hp

lemma dilations_compact (K : Set ℝ) (hK : IsCompact K) :
    TendstoUniformlyOn dilations (fun _ => 0) atTop K := by
  obtain ⟨M, hM⟩ := hK.isBounded.exists_norm_le
  apply Metric.tendstoUniformlyOn_iff.mpr
  intro ε hε
  have ht : Tendsto (fun n : ℕ => M / (n + 1 : ℝ)) atTop (𝓝 0) := by
    simpa [div_eq_mul_inv] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul M
  filter_upwards [ht.eventually (gt_mem_nhds hε)] with n hn x hx
  have hb : |x| ≤ M := by simpa [Real.norm_eq_abs] using hM x hx
  simpa [dilations, Specs.D10Topology.Ch13.StrictComparisons.dilations,
    Real.dist_eq, abs_div, abs_of_pos (show (0 : ℝ) < n + 1 by positivity)] using
    lt_of_le_of_lt (div_le_div_of_nonneg_right hb (by positivity)) hn

lemma dilations_not_uniform : ¬ TendstoUniformly dilations (fun _ => 0) atTop := by
  intro h
  obtain ⟨n, hn⟩ := (Metric.tendstoUniformly_iff.mp h (1 / 2) (by norm_num)).exists
  have hp := hn (n + 1 : ℝ)
  have hne : (n + 1 : ℝ) ≠ 0 := by positivity
  norm_num [dilations, Specs.D10Topology.Ch13.StrictComparisons.dilations, hne] at hp

lemma dilation_supremum (n : ℕ) :
    (⨆ x : ℝ, min 1 (|x| / (n + 1 : ℝ))) = 1 := by
  have hn : (n + 1 : ℝ) ≠ 0 := by positivity
  apply le_antisymm
  · exact ciSup_le (fun x => min_le_left _ _)
  · have hh := le_ciSup (show BddAbove (range (fun x : ℝ => min 1 (|x| / (n + 1 : ℝ))))
        from ⟨1, by rintro _ ⟨x, rfl⟩; exact min_le_left _ _⟩) (n + 1 : ℝ)
    simpa [abs_of_pos (show (0 : ℝ) < n + 1 by positivity), hn] using hh


/-- Bridge from the named uniform topology to the epsilon definition. -/
lemma uniform_tendsto_iff {X ι : Type*} {F : ι → X → ℝ} {f : X → ℝ} {p : Filter ι} :
    Tendsto F p (@nhds (X → ℝ) uniformTopology f) ↔ TendstoUniformly F f p := by
  change Tendsto F p (@nhds _ (TopologicalSpace.induced UniformFun.ofFun _) f) ↔ _
  rw [nhds_induced, tendsto_comap_iff, UniformFun.tendsto_iff_tendstoUniformly]
  rfl

lemma compact_tendsto_iff {X ι : Type*} [TopologicalSpace X]
    {F : ι → X → ℝ} {f : X → ℝ} {p : Filter ι} :
    Tendsto F p (@nhds (X → ℝ) compactConvergenceTopology f) ↔
      ∀ K : Set X, IsCompact K → TendstoUniformlyOn F f p K := by
  change Tendsto F p (@nhds _ (TopologicalSpace.induced
    (UniformOnFun.ofFun {K : Set X | IsCompact K}) _) f) ↔ _
  rw [nhds_induced, tendsto_comap_iff, UniformOnFun.tendsto_iff_tendstoUniformlyOn]
  rfl

lemma tents_not_compact : ¬ Tendsto tents atTop
    (@nhds (Interval → ℝ) compactConvergenceTopology (fun _ => 0)) := by
  intro h
  apply tents_not_uniform
  exact tendstoUniformlyOn_univ.mp ((compact_tendsto_iff.mp h) univ isCompact_univ)

theorem power_example : Specs.D10Topology.Ch13.StrictComparisons.power_example :=
  ⟨powers_continuous, powers_pointwise, powerLimit_not_continuous, powers_not_uniform⟩

theorem tent_example : Specs.D10Topology.Ch13.StrictComparisons.tent_example :=
  ⟨tents_continuous, continuous_const, tents_pointwise, tents_peak,
    tents_not_uniform, tents_not_compact⟩

theorem dilation_example : Specs.D10Topology.Ch13.StrictComparisons.dilation_example :=
  ⟨dilations_continuous, dilations_compact, dilations_not_uniform, dilation_supremum⟩


/-- The moving peaks distinguish pointwise and compact convergence within C([0,1],ℝ). -/
lemma compact_pointwise_strict :
    compactConvergenceContinuousTopology (X := Interval) (Y := ℝ) <
      pointwiseContinuousTopology := by
  refine lt_of_le_of_ne (continuous_topology_comparisons (X := Interval) (Y := ℝ)).2 ?_
  intro he
  let H (n : ℕ) : ContinuousMap Interval ℝ := ⟨tents n, tents_continuous n⟩
  let z : ContinuousMap Interval ℝ := ContinuousMap.const Interval 0
  have hp : Tendsto H atTop (@nhds _ pointwiseContinuousTopology z) := by
    change Tendsto H atTop (@nhds _ (TopologicalSpace.induced
      (fun f : ContinuousMap Interval ℝ => (f : Interval → ℝ)) _) z)
    rw [nhds_induced, tendsto_comap_iff]
    exact tendsto_pi_nhds.mpr tents_pointwise
  rw [← he, compactConvergenceContinuousTopology_eq_induced,
    @nhds_induced (Interval → ℝ) (ContinuousMap Interval ℝ) compactConvergenceTopology,
    tendsto_comap_iff] at hp
  exact tents_not_compact hp

/-- Bounded compact subsets allow dilation convergence; the whole real line does not. -/
lemma uniform_compact_strict :
    uniformContinuousTopology (X := ℝ) (Y := ℝ) <
      compactConvergenceContinuousTopology := by
  refine lt_of_le_of_ne (continuous_topology_comparisons (X := ℝ) (Y := ℝ)).1 ?_
  intro he
  let G (n : ℕ) : ContinuousMap ℝ ℝ := ⟨dilations n, dilations_continuous n⟩
  let z : ContinuousMap ℝ ℝ := ContinuousMap.const ℝ 0
  have hc : Tendsto G atTop (@nhds _ compactConvergenceContinuousTopology z) := by
    rw [compactConvergenceContinuousTopology_eq_induced,
      @nhds_induced (ℝ → ℝ) (ContinuousMap ℝ ℝ) compactConvergenceTopology,
      tendsto_comap_iff]
    exact compact_tendsto_iff.mpr dilations_compact
  rw [← he] at hc
  change Tendsto G atTop (@nhds _ (TopologicalSpace.induced
    (fun f : ContinuousMap ℝ ℝ => (f : ℝ → ℝ)) _) z) at hc
  rw [@nhds_induced (ℝ → ℝ) (ContinuousMap ℝ ℝ) uniformTopology,
    tendsto_comap_iff] at hc
  exact dilations_not_uniform (uniform_tendsto_iff.mp hc)

theorem strict_continuous_topologies :
    Specs.D10Topology.Ch13.StrictComparisons.strict_continuous_topologies :=
  ⟨compact_pointwise_strict, uniform_compact_strict⟩

end D10Topology.Ch13.StrictComparisons
