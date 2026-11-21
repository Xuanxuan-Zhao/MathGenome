import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch10.CompleteGdeltaNecessary
import MathGenome.Internal.PointSetTopology.D10Topology.Ch09.MetricConventions
import Mathlib.Topology.GDelta.MetrizableSpace
import Mathlib.Topology.Sequences

/-! The necessary direction of paper.tex, d10:10:complete-gdelta.
We first prove the result for the range of a topological embedding of a
complete metric space. Small-diameter inverse images give open sets; a
sequence approaching a point of the range closure is Cauchy in the complete
source whenever the point belongs to all these open sets. This argument
requires neither ambient completeness nor uniform continuity of the embedding. -/

open Set Filter Topology
open scoped Topology
universe u v
namespace D10Topology.Ch10

/-- A complete metric space has G_delta image under any topological embedding
in a metric space. The two metrics need not be uniformly related. -/
theorem isGdelta_range_of_complete
    {X : Type u} {Y : Type v} [MetricSpace X] [MetricSpace Y] [CompleteSpace Y]
    {f : Y → X} (hf : IsEmbedding f) : IsGδ (range f) := by
  classical
  let r : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hr (n : ℕ) : 0 < r n := by dsimp [r]; positivity
  let G : ℕ → Set X := fun n => ⋃₀ {U : Set X | IsOpen U ∧
    ∀ a b : Y, f a ∈ U → f b ∈ U → dist a b < r n}
  have hGopen (n : ℕ) : IsOpen (G n) := isOpen_sUnion fun _ hU => hU.1
  have hGrange (n : ℕ) : range f ⊆ G n := by
    rintro _ ⟨y, rfl⟩
    obtain ⟨U, hUopen, hUeq⟩ :=
      hf.isInducing.isOpen_iff.mp (Metric.isOpen_ball (x := y) (ε := r n / 2))
    apply mem_sUnion.mpr
    refine ⟨U, ⟨hUopen, ?_⟩, ?_⟩
    · intro a b ha hb
      have ha' : dist a y < r n / 2 := by
        have : a ∈ f ⁻¹' U := ha
        rw [hUeq] at this
        exact this
      have hb' : dist b y < r n / 2 := by
        have : b ∈ f ⁻¹' U := hb
        rw [hUeq] at this
        exact this
      calc dist a b ≤ dist a y + dist b y := dist_triangle_right a b y
           _ < r n / 2 + r n / 2 := add_lt_add ha' hb'
           _ = r n := add_halves _
    · change y ∈ f ⁻¹' U
      rw [hUeq]
      exact Metric.mem_ball_self (half_pos (hr n))
  have heq : range f = closure (range f) ∩ ⋂ n, G n := by
    apply subset_antisymm
    · intro x hx
      exact ⟨subset_closure hx, mem_iInter.mpr fun n => hGrange n hx⟩
    · intro x hx
      obtain ⟨s, hs, hsx⟩ := mem_closure_iff_seq_limit.mp hx.1
      choose a ha using hs
      have hax : Tendsto (fun n => f (a n)) atTop (𝓝 x) := by
        convert hsx using 1
        exact funext ha
      have hc : CauchySeq a := by
        apply Metric.cauchySeq_iff.mpr
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        obtain ⟨U, hU, hxU⟩ := mem_sUnion.mp (mem_iInter.mp hx.2 k)
        have hevent : ∀ᶠ n in atTop, f (a n) ∈ U := hax (hU.1.mem_nhds hxU)
        obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
        refine ⟨N, fun m hm n hn => ?_⟩
        exact (hU.2 (a m) (a n) (hN m hm) (hN n hn)).trans hk
      obtain ⟨y, hy⟩ := cauchySeq_tendsto_of_complete hc
      have hfy : Tendsto (fun n => f (a n)) atTop (𝓝 (f y)) :=
        hf.continuous.continuousAt.tendsto.comp hy
      exact ⟨y, tendsto_nhds_unique hfy hax⟩
  rw [heq]
  exact isClosed_closure.isGδ.inter (IsGδ.iInter_of_isOpen hGopen)

/-- Complete metrizability of the subspace topology implies that the subset
is G_delta in every ambient metric space, including an incomplete one. -/
theorem complete_subspace_is_gdelta {X : Type u} (d : MetricSpace X) (A : Set X)
    (hA : Ch09.CompletelyMetrizable
      (TopologicalSpace.induced (Subtype.val : A → X)
        (Ch09.metricTopology d.toPseudoMetricSpace))) :
    @IsGδ X (Ch09.metricTopology d.toPseudoMetricSpace) A := by
  let := d
  let : TopologicalSpace.IsCompletelyMetrizableSpace A :=
    (Ch09.completelyMetrizable_iff_mathlib _).mp hA
  let m := TopologicalSpace.completelyMetrizableMetric A
  simpa only [Subtype.range_coe_subtype, ofPred_mem_eq] using
    (@isGdelta_range_of_complete X A d m
      (TopologicalSpace.complete_completelyMetrizableMetric A)
      (Subtype.val : A → X) IsEmbedding.subtypeVal)

end D10Topology.Ch10
