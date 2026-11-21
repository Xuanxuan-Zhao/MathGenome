import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.SineCurveClosure
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.ComponentsAndPaths
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Sequences

open Set Filter Topology

namespace D10Topology.Ch06

noncomputable def sineGraph : Set (ℝ × ℝ) := SineCurveData.graph

def sineVertical : Set (ℝ × ℝ) := SineCurveData.vertical

noncomputable def sineCurve : Set (ℝ × ℝ) := SineCurveData.curve

private theorem graph_image :
    sineGraph = (fun t : ℝ => (t, Real.sin (1 / t))) '' Ioc 0 1 := by
  ext p
  constructor
  · rintro ⟨h0, h1, hy⟩
    exact ⟨p.1, ⟨h0, h1⟩, Prod.ext rfl hy.symm⟩
  · rintro ⟨t, ht, rfl⟩
    exact ⟨ht.1, ht.2, rfl⟩

private theorem graphMap_continuous :
    ContinuousOn (fun t : ℝ => (t, Real.sin (1 / t))) (Ioc 0 1) := by
  apply continuousOn_id.prodMk
  apply Real.continuous_sin.comp_continuousOn
  exact continuousOn_const.div continuousOn_id (fun t ht => ne_of_gt ht.1)

theorem sineGraph_pathConnected : PathConnectedSubset sineGraph := by
  rw [graph_image]
  exact (convex_Ioc (0 : ℝ) 1).isPathConnected (nonempty_Ioc.mpr zero_lt_one)
    |>.image' graphMap_continuous |>.joinedIn

theorem sineGraph_connected : ConnectedSubset sineGraph :=
  pathConnectedSubset_connected _ sineGraph_pathConnected

private theorem vertical_image :
    sineVertical = (fun y : ℝ => ((0 : ℝ), y)) '' Icc (-1) 1 := by
  ext p
  constructor
  · rintro ⟨hx, h0, h1⟩
    exact ⟨p.2, ⟨h0, h1⟩, Prod.ext hx.symm rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨rfl, hy.1, hy.2⟩

theorem sineVertical_pathConnected : PathConnectedSubset sineVertical := by
  rw [vertical_image]
  exact (convex_Icc (-1 : ℝ) 1).isPathConnected (nonempty_Icc.mpr (by norm_num))
    |>.image (continuous_const.prodMk continuous_id) |>.joinedIn

/-- No closure point can leave the strip, and away from the vertical axis
continuity of the graph function determines its second coordinate. -/
private theorem closure_subset_curve : closure sineGraph ⊆ sineCurve := by
  intro p hp
  obtain ⟨f, hf, hlim⟩ := mem_closure_iff_seq_limit.mp hp
  have hx := hlim.fst_nhds
  have hy := hlim.snd_nhds
  have h0 : 0 ≤ p.1 := ge_of_tendsto hx (Eventually.of_forall (fun n => (hf n).1.le))
  have h1 : p.1 ≤ 1 := le_of_tendsto hx (Eventually.of_forall (fun n => (hf n).2.1))
  have hlo : -1 ≤ p.2 := ge_of_tendsto hy (Eventually.of_forall (fun n => by
    rw [(hf n).2.2]
    exact Real.neg_one_le_sin _))
  have hhi : p.2 ≤ 1 := le_of_tendsto hy (Eventually.of_forall (fun n => by
    rw [(hf n).2.2]
    exact Real.sin_le_one _))
  by_cases hz : p.1 = 0
  · exact Or.inr ⟨hz, hlo, hhi⟩
  · left
    refine ⟨lt_of_le_of_ne h0 (Ne.symm hz), h1, ?_⟩
    have hfun : ContinuousAt (fun t : ℝ => Real.sin (1 / t)) p.1 :=
      Real.continuous_sin.continuousAt.comp (continuousAt_const.div continuousAt_id hz)
    exact tendsto_nhds_unique hy ((hfun.tendsto.comp hx).congr (fun n => (hf n).2.2.symm))

/-- For each allowed height, periodicity supplies graph points with that exact
height and with positive first coordinates tending to zero. -/
private theorem vertical_subset_closure : sineVertical ⊆ closure sineGraph := by
  rintro ⟨x, y⟩ ⟨hx, hy0, hy1⟩
  dsimp at hx hy0 hy1
  subst x
  obtain ⟨a, _, ha⟩ := Real.surjOn_sin ⟨hy0, hy1⟩
  let u : ℕ → ℝ := fun n => a + (n : ℝ) * (2 * Real.pi)
  have hu : Tendsto u atTop atTop := by
    exact tendsto_atTop_add_const_left atTop a
      (Tendsto.atTop_mul_const (by positivity) tendsto_natCast_atTop_atTop)
  have hu1 : ∀ᶠ n in atTop, 1 ≤ u n := hu.eventually (eventually_ge_atTop 1)
  have hlim : Tendsto (fun n => ((u n)⁻¹, y)) atTop (𝓝 ((0 : ℝ), y)) :=
    (tendsto_inv_atTop_zero.comp hu).prodMk_nhds tendsto_const_nhds
  apply mem_closure_of_tendsto hlim
  filter_upwards [hu1] with n hn
  have hpos : 0 < u n := lt_of_lt_of_le zero_lt_one hn
  refine ⟨inv_pos.mpr hpos, inv_le_one_of_one_le₀ hn, ?_⟩
  dsimp
  rw [one_div, inv_inv, Real.sin_add_nat_mul_two_pi, ha]

theorem sineGraph_closure : closure sineGraph = sineCurve := by
  apply Subset.antisymm closure_subset_curve
  intro p hp
  rcases hp with hg | hv
  · exact subset_closure hg
  · exact vertical_subset_closure hv

theorem sineCurve_connected : ConnectedSubset sineCurve := by
  rw [← sineGraph_closure]
  exact connectedSubset_closure _ sineGraph_connected

end D10Topology.Ch06
