import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch06.SineCurvePathComponents
import MathGenome.Internal.PointSetTopology.D10Topology.Ch06.SineCurveClosure
import Mathlib.Topology.Connected.Clopen
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.Linarith

open Set Filter Topology
namespace D10Topology.Ch06

/-- The already proved closure supplies both large and small heights at
arbitrarily small positive first coordinates. -/
private theorem small_graph_heights {c : ℝ} (hc : 0 < c) :
    (∃ p ∈ sineGraph, p.1 < c ∧ (3 / 4 : ℝ) < p.2) ∧
    (∃ p ∈ sineGraph, p.1 < c ∧ p.2 < (-3 / 4 : ℝ)) := by
  have hp : ((0, 1) : ℝ × ℝ) ∈ closure sineGraph := by
    rw [sineGraph_closure]
    exact Or.inr ⟨rfl, by norm_num, le_rfl⟩
  have hm : ((0, -1) : ℝ × ℝ) ∈ closure sineGraph := by
    rw [sineGraph_closure]
    exact Or.inr ⟨rfl, le_rfl, by norm_num⟩
  constructor
  · obtain ⟨p, hpO, hpG⟩ := mem_closure_iff.mp hp
      (Iio c ×ˢ Ioi (3 / 4 : ℝ)) (isOpen_Iio.prod isOpen_Ioi) ⟨hc, by norm_num⟩
    exact ⟨p, hpG, hpO⟩
  · obtain ⟨p, hpO, hpG⟩ := mem_closure_iff.mp hm
      (Iio c ×ˢ Iio (-3 / 4 : ℝ)) (isOpen_Iio.prod isOpen_Iio) ⟨hc, by norm_num⟩
    exact ⟨p, hpG, hpO⟩

/-- Along any continuous real-parameter curve in S, touching the axis is
an open condition. The IVT forces both graph heights in any connected
parameter neighborhood containing an axis point and a positive point. -/
private theorem axis_preimage_open (f : ℝ → ℝ × ℝ) (hf : Continuous f)
    (hS : ∀ t, f t ∈ sineCurve) : IsOpen {t | (f t).1 = 0} := by
  rw [isOpen_iff_mem_nhds]
  intro a ha
  obtain ⟨δ, hδ, hcont⟩ := Metric.continuousAt_iff.mp hf.snd.continuousAt
    (1 / 2) (by norm_num)
  let U := Ioo (a - δ) (a + δ)
  have haU : a ∈ U := ⟨by linarith, by linarith⟩
  have hv : ∀ t ∈ U, |(f t).2 - (f a).2| < (1 / 2 : ℝ) := by
    intro t ht
    apply hcont
    rw [Real.dist_eq, abs_lt]
    exact ⟨by linarith [ht.1], by linarith [ht.2]⟩
  refine mem_of_superset (isOpen_Ioo.mem_nhds haU) ?_
  intro b hb
  by_contra hne
  have hbpos : 0 < (f b).1 := by
    rcases hS b with hg | hv
    · exact hg.1
    · exact False.elim (hne hv.1)
  obtain ⟨⟨p, hpG, hpc, hpH⟩, ⟨q, hqG, hqc, hqH⟩⟩ := small_graph_heights hbpos
  have hit : ∀ r ∈ sineGraph, r.1 < (f b).1 → ∃ t ∈ U, (f t).2 = r.2 := by
    intro r hr hrc
    obtain ⟨t, ht, htr⟩ := isPreconnected_Ioo.intermediate_value haU hb
      hf.fst.continuousOn (show r.1 ∈ Icc (f a).1 (f b).1 from ⟨by rw [ha]; exact hr.1.le, hrc.le⟩)
    change (f t).1 = r.1 at htr
    have htg : f t ∈ sineGraph := by
      rcases hS t with hg | hv
      · exact hg
      · exfalso
        have := hr.1
        rw [← htr, hv.1] at this
        exact lt_irrefl _ this
    exact ⟨t, ht, htg.2.2.trans (by rw [htr]; exact hr.2.2.symm)⟩
  obtain ⟨s, hs, hsp⟩ := hit p hpG hpc
  obtain ⟨t, ht, htq⟩ := hit q hqG hqc
  have hs' := (abs_lt.mp (hv s hs)).2
  have ht' := (abs_lt.mp (hv t ht)).1
  rw [hsp] at hs'
  rw [htq] at ht'
  linarith

/-- No path in the specified subspace can cross from the graph to the segment. -/
theorem sineCurve_no_path :
    ∀ x ∈ sineGraph, ∀ y ∈ sineVertical, ¬ JoinedIn sineCurve x y := by
  intro x hx y hy h
  obtain ⟨p⟩ := h.joined_subtype
  let f : ℝ → ℝ × ℝ := fun t => (p.extend t).val
  have hf : Continuous f := continuous_subtype_val.comp p.continuous_extend
  have hS : ∀ t, f t ∈ sineCurve := fun t => (p.extend t).property
  have ho := axis_preimage_open f hf hS
  have hc : IsClosed {t | (f t).1 = 0} := isClosed_eq hf.fst continuous_const
  have h1 : (1 : ℝ) ∈ {t | (f t).1 = 0} := by
    simpa only [mem_ofPred_eq, f, p.extend_one] using hy.1
  have he := (show IsClopen {t | (f t).1 = 0} from ⟨hc, ho⟩).eq_univ ⟨1, h1⟩
  have h0 : (f 0).1 = 0 := (Set.ext_iff.mp he 0).mpr (mem_univ 0)
  have hx0 : x.1 = 0 := by simpa only [f, p.extend_zero] using h0
  exact (ne_of_gt hx.1) hx0

theorem sineGraph_pathComponent (x : sineCurve) (hx : x.val ∈ sineGraph) :
    PathComponent x = {y : sineCurve | y.val ∈ sineGraph} := by
  ext y
  constructor
  · intro h
    rcases y.property with hg | hv
    · exact hg
    · exact False.elim (sineCurve_no_path x.val hx y.val hv
        ((joinedIn_iff_joined x.property y.property).mpr h))
  · intro hy
    exact ((sineGraph_pathConnected x.val hx y.val hy).mono
      (show sineGraph ⊆ sineCurve from subset_union_left)).joined_subtype

theorem sineVertical_pathComponent (x : sineCurve) (hx : x.val ∈ sineVertical) :
    PathComponent x = {y : sineCurve | y.val ∈ sineVertical} := by
  ext y
  constructor
  · intro h
    rcases y.property with hg | hv
    · exact False.elim (sineCurve_no_path y.val hg x.val hx
        ((joinedIn_iff_joined y.property x.property).mpr (show Joined x y from h).symm))
    · exact hv
  · intro hy
    exact ((sineVertical_pathConnected x.val hx y.val hy).mono
      (show sineVertical ⊆ sineCurve from subset_union_right)).joined_subtype

private theorem graph_point : ((1, Real.sin 1) : ℝ × ℝ) ∈ sineGraph := by
  exact ⟨zero_lt_one, le_rfl, by norm_num⟩

private theorem vertical_point : ((0, 0) : ℝ × ℝ) ∈ sineVertical :=
  ⟨rfl, by norm_num, by norm_num⟩

theorem sineCurve_exactly_two_pathComponents :
    {A : Set sineCurve | ∃ x : sineCurve, PathComponent x = A} =
      {{y : sineCurve | y.val ∈ sineGraph}, {y : sineCurve | y.val ∈ sineVertical}} ∧
      ({y : sineCurve | y.val ∈ sineGraph} : Set sineCurve) ≠
        {y : sineCurve | y.val ∈ sineVertical} := by
  constructor
  · ext A
    constructor
    · rintro ⟨x, rfl⟩
      rcases x.property with hg | hv
      · simp only [sineGraph_pathComponent x hg, mem_insert_iff, mem_singleton_iff, true_or]
      · simp only [sineVertical_pathComponent x hv, mem_insert_iff, mem_singleton_iff, or_true]
    · intro h
      rcases mem_insert_iff.mp h with rfl | h
      · exact ⟨⟨_, Or.inl graph_point⟩, sineGraph_pathComponent _ graph_point⟩
      · rw [mem_singleton_iff] at h
        subst A
        exact ⟨⟨_, Or.inr vertical_point⟩, sineVertical_pathComponent _ vertical_point⟩
  · intro h
    have hg : (⟨_, Or.inl graph_point⟩ : sineCurve) ∈
        {y : sineCurve | y.val ∈ sineGraph} := graph_point
    rw [h] at hg
    have hz : (1 : ℝ) = 0 := hg.1
    norm_num at hz

theorem sineGraph_not_closed_in_curve :
    ¬ IsClosed ({y : sineCurve | y.val ∈ sineGraph} : Set sineCurve) := by
  intro hc
  have himage : Subtype.val '' ({y : sineCurve | y.val ∈ sineGraph} : Set sineCurve) =
      sineGraph := by
    ext p
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hp
      exact ⟨⟨p, Or.inl hp⟩, hp, rfl⟩
  have hcl := Topology.IsEmbedding.subtypeVal.closure_eq_preimage_closure_image
    ({y : sineCurve | y.val ∈ sineGraph} : Set sineCurve)
  rw [himage, sineGraph_closure, hc.closure_eq] at hcl
  have hz : (⟨_, Or.inr vertical_point⟩ : sineCurve) ∈
      {y : sineCurve | y.val ∈ sineGraph} :=
    (Set.ext_iff.mp hcl _).mpr (Or.inr vertical_point)
  exact (lt_irrefl (0 : ℝ)) hz.1

theorem sineCurve_complete_result :
    Specs.D10Topology.Ch06.SineCurvePathComponents.complete_result :=
  ⟨sineGraph_closure, sineCurve_connected,
    sineCurve_exactly_two_pathComponents, sineGraph_not_closed_in_curve⟩

end D10Topology.Ch06
