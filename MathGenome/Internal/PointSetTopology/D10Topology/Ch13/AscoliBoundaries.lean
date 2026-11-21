import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch13.AscoliBoundaries
import MathGenome.Internal.PointSetTopology.D10Topology.Ch13.AscoliConverseClassical
import Mathlib.Tactic.FieldSimp

noncomputable section
open Set Filter
open scoped Topology
universe u
namespace D10Topology.Ch13.AscoliBoundaries
open Specs.D10Topology.Ch13.AscoliBoundaries

/-- Evaluation of all constants fills the infinite discrete target; its compact
closure would therefore force that target to be finite. -/
theorem discrete_constants : Specs.D10Topology.Ch13.AscoliBoundaries.discrete_constants := by
  classical
  intro Y hY
  letI : MetricSpace Y := discreteMetric Y
  have hd (y z : Y) : dist y z = if y = z then 0 else 1 := rfl
  have hle (y z : Y) : dist y z ≤ 1 := by
    rw [hd]
    split_ifs <;> norm_num
  have hi (x : Unit) : (fun f : ContinuousMaps Unit Y => f x) '' constantFamily Y = univ := by
    ext y
    simp only [mem_image, mem_univ, iff_true]
    exact ⟨ContinuousMap.const Unit y, mem_range_self y, rfl⟩
  have he : Equicontinuous (constantFamily Y) := by
    intro x ε hε
    refine ⟨univ, univ_mem, ?_⟩
    rintro y _ f ⟨z, rfl⟩
    simpa using hε
  have hb : ∀ x : Unit, Bornology.IsBounded
      ((fun f : ContinuousMaps Unit Y => f x) '' constantFamily Y) := by
    intro x
    rw [hi x]
    exact Metric.isBounded_iff.mpr ⟨1, fun y _ z _ => hle y z⟩
  haveI : DiscreteTopology Y := discreteTopology_iff_isOpen_singleton.mpr fun y => by
    have hball : Metric.ball y 1 = {y} := by
      ext z
      classical
      simp only [Metric.mem_ball, hd, mem_singleton_iff]
      by_cases h : z = y <;> simp [h]
    rw [← hball]
    exact Metric.isOpen_ball
  have hp : ¬ PointwiseRelativelyCompact (constantFamily Y) := by
    intro h
    have hc := h ()
    rw [hi (), closure_univ] at hc
    exact Set.infinite_univ.not_finite (isCompact_iff_finite.mp hc)
  exact ⟨he, hb, hp, fun hc => hp ((compactDomain_ascoli_iff _).mp hc).2⟩

theorem sine_bound : Specs.D10Topology.Ch13.AscoliBoundaries.sine_bound := by
  rintro f ⟨n, rfl⟩ x
  exact Real.abs_sin_le_one _

theorem sine_pointwise_bounded :
    Specs.D10Topology.Ch13.AscoliBoundaries.sine_pointwise_bounded := by
  intro x
  apply isBounded_iff_forall_norm_le.mpr
  refine ⟨1, ?_⟩
  rintro y ⟨f, hf, rfl⟩
  simpa only [Real.norm_eq_abs] using sine_bound f hf x

theorem sine_witness : Specs.D10Topology.Ch13.AscoliBoundaries.sine_witness := by
  constructor
  · apply tendsto_subtype_rng.mpr
    change Tendsto (fun n : ℕ => Real.pi / (2 * ((n : ℝ) + 1))) atTop (𝓝 (0 : ℝ))
    convert (tendsto_const_nhds (x := Real.pi / 2)).mul
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)) using 1
    · funext n
      field_simp
    · simp
  · intro n
    constructor
    · change Real.sin (((n : ℝ) + 1) * (Real.pi / (2 * ((n : ℝ) + 1)))) = 1
      have hn : (n : ℝ) + 1 ≠ 0 := by positivity
      have heq : ((n : ℝ) + 1) * (Real.pi / (2 * ((n : ℝ) + 1))) = Real.pi / 2 := by
        field_simp
      rw [heq, Real.sin_pi_div_two]
    · simp [sineMap, sineZero]

/-- A single neighborhood for tolerance 1/2 would eventually contain x_n,
but the n-th map changes from 0 to 1 there. -/
theorem sine_not_equicontinuous : Specs.D10Topology.Ch13.AscoliBoundaries.sine_not_equicontinuous := by
  intro h
  obtain ⟨U, hU, hh⟩ := h (1 / 2) (by norm_num)
  have he := sine_witness.1.eventually hU
  obtain ⟨n, hn⟩ := he.exists
  have hf := hh (sineSample n) hn (sineMap n) (mem_range_self n)
  rw [sine_witness.2 n |>.1, sine_witness.2 n |>.2] at hf
  norm_num at hf

theorem sine_not_compact_uniform_closure :
    Specs.D10Topology.Ch13.AscoliBoundaries.sine_not_compact_uniform_closure := by
  intro hc
  exact sine_not_equicontinuous (((compactMetric_ascoli_iff sineFamily).mp hc).1 sineZero)

end D10Topology.Ch13.AscoliBoundaries
