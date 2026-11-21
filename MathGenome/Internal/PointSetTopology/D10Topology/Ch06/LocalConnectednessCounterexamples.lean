import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.LocalConnectednessCounterexamples
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.LocalConnectedness
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.SineCurvePathComponents
import Mathlib.Topology.Instances.Irrational
import Mathlib.Topology.Order.DenselyOrdered
import Batteries.Tactic.OpenPrivate

/-! Counterexamples separating local and global connectedness, and showing
failure of arbitrary-subspace heredity. The sine-curve argument uses connected
sets and the intermediate value theorem, rather than path components. -/

open Set Filter Topology

namespace D10Topology.Ch06
open LocalCounterexamplesData
open private small_graph_heights from MathGenome.Internal.PointSetTopology.D10Topology.Ch06.SineCurvePathComponents

theorem twoPoint_locallyConnected : LocallyConnected Bool :=
  (locallyConnected_iff_mathlib Bool).mpr inferInstance

theorem twoPoint_disconnected : ¬ Connected Bool := by
  intro h
  have hm := (connected_iff_bool_maps Bool).mp h id continuous_id false true
  exact Bool.false_ne_true hm

/-- A connected set in the narrow horizontal strip cannot contain both the
origin and a graph point: its first-coordinate image would have to pass
through a graph coordinate whose height exceeds 3/4. -/
private theorem connected_strip_no_graph (V : Set sineCurve)
    (hV : IsPreconnected V) (h0 : sineOrigin ∈ V)
    (hstrip : ∀ z ∈ V, z.val.2 < (1 / 2 : ℝ)) :
    ∀ b ∈ V, b.val ∉ sineGraph := by
  intro b hb hbG
  obtain ⟨⟨p, hpG, hpc, hpH⟩, _⟩ := small_graph_heights hbG.1
  have hf : Continuous (fun z : sineCurve => z.val.1) :=
    continuous_fst.comp continuous_subtype_val
  obtain ⟨z, hz, hzp⟩ := hV.intermediate_value h0 hb hf.continuousOn
    (show p.1 ∈ Icc sineOrigin.val.1 b.val.1 from ⟨hpG.1.le, hpc.le⟩)
  change z.val.1 = p.1 at hzp
  have hzG : z.val ∈ sineGraph := by
    rcases z.property with hg | hv
    · exact hg
    · exfalso
      have := hpG.1
      rw [← hzp, hv.1] at this
      exact lt_irrefl _ this
  have hheight : z.val.2 = p.2 :=
    hzG.2.2.trans (by rw [hzp]; exact hpG.2.2.symm)
  have := hstrip z hz
  rw [hheight] at this
  linarith

theorem sineCurve_connectedNeighborhood_obstruction :
    ∃ N : Set sineCurve, N ∈ 𝓝 sineOrigin ∧
      ∀ V : Set sineCurve, V ∈ 𝓝 sineOrigin → V ⊆ N → ¬ ConnectedSubset V := by
  let N : Set sineCurve := {z | z.val.2 < (1 / 2 : ℝ)}
  have hN : N ∈ 𝓝 sineOrigin :=
    (isOpen_lt (continuous_snd.comp continuous_subtype_val) continuous_const).mem_nhds
      (by norm_num [N, sineOrigin])
  refine ⟨N, hN, ?_⟩
  intro V hV hVN hconn
  have h0 : sineOrigin ∈ V := mem_of_mem_nhds hV
  obtain ⟨U, hU, hUV⟩ := (mem_nhds_subtype sineCurve sineOrigin V).mp hV
  have hcl : sineOrigin.val ∈ closure sineGraph := by
    rw [sineGraph_closure]
    exact sineOrigin.property
  obtain ⟨p, hpU, hpG⟩ := mem_closure_iff_nhds.mp hcl U hU
  let b : sineCurve := ⟨p, Or.inl hpG⟩
  have hb : b ∈ V := hUV hpU
  exact connected_strip_no_graph V ((connectedSubset_iff_isPreconnected V).mp hconn)
    h0 (fun z hz => hVN hz) b hb hpG

theorem sineCurve_not_locallyConnectedAt_origin : ¬ LocallyConnectedAt sineOrigin := by
  intro h
  obtain ⟨N, hN, hbad⟩ := sineCurve_connectedNeighborhood_obstruction
  obtain ⟨V, hV, hc, hVN⟩ := (locallyConnectedAt_iff_nhds sineOrigin).mp h N hN
  exact hbad V hV hVN ((connectedSubset_iff_isPreconnected V).mpr hc)

theorem sineCurve_connected_not_locallyConnected :
    ConnectedSubset sineCurve ∧ ¬ LocallyConnected sineCurve := by
  exact ⟨sineCurve_connected, fun h => sineCurve_not_locallyConnectedAt_origin (h sineOrigin)⟩

/-- Cutting the real image at an irrational between two distinct rationals
contradicts the interval property of a connected real subset. -/
theorem rational_connected_subsingleton (A : Set ℚ) (hA : ConnectedSubset A) :
    A.Subsingleton := by
  have hc := (connectedSubset_iff_isPreconnected A).mp hA
  have hi := hc.image ((↑) : ℚ → ℝ) Rat.continuous_coe_real.continuousOn
  have ho := isPreconnected_iff_ordConnected.mp hi
  have hnotlt {x y : ℚ} (hx : x ∈ A) (hy : y ∈ A) (hlt : x < y) : False := by
    obtain ⟨z, hz, hxz, hzy⟩ := exists_irrational_btwn (Rat.cast_lt.mpr hlt)
    have hzin : z ∈ ((↑) : ℚ → ℝ) '' A :=
      ho.out (mem_image_of_mem _ hx) (mem_image_of_mem _ hy) ⟨hxz.le, hzy.le⟩
    exact hz (image_subset_range _ _ hzin)
  intro x hx y hy
  by_contra hne
  exact (lt_or_gt_of_ne hne).elim (hnotlt hx hy) (hnotlt hy hx)

theorem rational_connected_singleton (A : Set ℚ) (hne : A.Nonempty)
    (hA : ConnectedSubset A) : ∃ q : ℚ, A = {q} := by
  obtain ⟨q, hq⟩ := hne
  exact ⟨q, (rational_connected_subsingleton A hA).eq_singleton_of_mem hq⟩

theorem rational_component_singleton (q : ℚ) : Component q = {q} :=
  (rational_connected_subsingleton _ (component_connected q)).eq_singleton_of_mem
    (component_self q)

theorem rational_not_discrete : ¬ DiscreteTopology ℚ := by
  intro h
  exact not_isOpen_singleton (0 : ℚ) (@isOpen_discrete ℚ _ h _)

theorem rational_not_locallyConnected : ¬ LocallyConnected ℚ := by
  intro h
  have hs : ∀ q : ℚ, IsOpen ({q} : Set ℚ) := by
    intro q
    obtain ⟨V, hV, hc, hVU⟩ :=
      (locallyConnectedAt_iff_nhds q).mp (h q) univ univ_mem
    have hq : q ∈ V := mem_of_mem_nhds hV
    have heq : V = {q} :=
      (rational_connected_subsingleton V
        ((connectedSubset_iff_isPreconnected V).mpr hc)).eq_singleton_of_mem hq
    rw [heq] at hV
    exact isOpen_iff_mem_nhds.mpr (fun x hx => by simpa only [mem_singleton_iff.mp hx] using hV)
  exact rational_not_discrete (discreteTopology_iff_isOpen_singleton.mpr hs)

theorem real_locallyConnected : LocallyConnected ℝ := by
  intro x
  apply (locallyConnectedAt_iff_nhds x).mpr
  intro N hN
  obtain ⟨a, b, hx, hsub⟩ := mem_nhds_iff_exists_Ioo_subset.mp hN
  exact ⟨Ioo a b, Ioo_mem_nhds hx.1 hx.2, isPreconnected_Ioo, hsub⟩

theorem locallyConnected_not_hereditary :
    LocallyConnected ℝ ∧ IsEmbedding ((↑) : ℚ → ℝ) ∧ ¬ LocallyConnected ℚ :=
  ⟨real_locallyConnected, Rat.isEmbedding_coe_real, rational_not_locallyConnected⟩

end D10Topology.Ch06
