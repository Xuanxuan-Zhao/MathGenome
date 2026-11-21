import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch18.TwoOriginsParacompact
import MathGenome.Internal.PointSetTopology.D10Topology.Ch18.TwoOriginsTopology
import MathGenome.Internal.PointSetTopology.D10Topology.Ch15.StandardParacompactness

/-! Paracompactness of the actual quotient line with two origins.

For each real coordinate y, select original cover members containing both
chart points above y. Their inverse images in the two charts have an open
intersection W(y) containing y. Refine this cover of the ordinary real line
locally finitely. Pull the refinement back by the continuous coordinate map
and intersect with the two selected original cover members. These two families
cover the quotient and are locally finite. This argument uses no Hausdorff
assumption on the quotient, and no local metrization theorem. -/

open Set Topology TopologicalSpace
open scoped Topology

namespace D10Topology.Ch18.TwoOrigins

/-- The doubled-origin quotient is paracompact, with no implicit Hausdorffness. -/
theorem paracompact : ParacompactSpace Line := by
  classical
  let : ParacompactSpace ℝ := Ch15.metric_paracompact (inferInstance : MetricSpace ℝ)
  constructor
  intro I U hUo hUc
  have hc : ∀ (b : Bool) (y : ℝ), ∃ i : I, chart b y ∈ U i :=
    fun b y => iUnion_eq_univ_iff.mp hUc (chart b y)
  choose c hc using hc
  let W : ℝ → Set ℝ := fun y =>
    (chart false ⁻¹' U (c false y)) ∩ (chart true ⁻¹' U (c true y))
  have hWo : ∀ y, IsOpen (W y) := fun y =>
    ((hUo _).preimage (chart_continuous false)).inter
      ((hUo _).preimage (chart_continuous true))
  have hWc : (⋃ y, W y) = univ :=
    iUnion_eq_univ_iff.mpr (fun y => ⟨y, hc false y, hc true y⟩)
  obtain ⟨V, hVo, hVc, hVf, hVW⟩ := precise_refinement W hWo hWc
  let A : Bool → ℝ → Set Line := fun b y =>
    (coordinate ⁻¹' V y) ∩ U (c b y)
  have hAo : ∀ b y, IsOpen (A b y) := fun b y =>
    ((hVo y).preimage coordinate_continuous).inter (hUo _)
  have hAf : ∀ b, LocallyFinite (A b) := fun b =>
    (hVf.preimage_continuous coordinate_continuous).subset (fun _ => inter_subset_left)
  refine ⟨ℝ ⊕ ℝ, Sum.elim (A false) (A true), ?_, ?_,
    (hAf false).sumElim (hAf true), ?_⟩
  · intro j
    cases j with
    | inl y => exact hAo false y
    | inr y => exact hAo true y
  · apply iUnion_eq_univ_iff.mpr
    intro q
    obtain ⟨b, x, rfl⟩ := exists_chart q
    obtain ⟨y, hy⟩ := iUnion_eq_univ_iff.mp hVc x
    have hx := hVW y hy
    have hv : coordinate (chart b x) ∈ V y := by simpa only [coordinate_chart] using hy
    cases b
    · exact ⟨Sum.inl y, hv, hx.1⟩
    · exact ⟨Sum.inr y, hv, hx.2⟩
  · intro j
    cases j with
    | inl y => exact ⟨c false y, inter_subset_right⟩
    | inr y => exact ⟨c true y, inter_subset_right⟩

/-- The example witnesses the need for Hausdorffness in Smirnov's theorem. -/
theorem smirnov_counterexample :
    ParacompactSpace Line ∧
      (∀ q : Line, ∃ U : Set Line, IsOpen U ∧ q ∈ U ∧ MetrizableSpace U) ∧
      SecondCountableTopology Line ∧ ¬ T2Space Line ∧ ¬ MetrizableSpace Line :=
  ⟨paracompact, locally_metrizable, second_countable, not_hausdorff, not_metrizable⟩

end D10Topology.Ch18.TwoOrigins
