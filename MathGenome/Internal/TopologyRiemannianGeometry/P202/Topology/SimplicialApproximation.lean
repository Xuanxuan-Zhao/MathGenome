import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.SimplicialApproximation
import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.CellTopology
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.DiscreteSubset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.Linarith
import Mathlib.Geometry.Convex.ConvexSpace.Module
import Mathlib.Geometry.Convex.ConvexSpace.Prod
import Mathlib.Analysis.Convex.MetricSpace
import Mathlib.Tactic.FieldSimp

import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CellTopology
noncomputable section
open Set Topology Classical Convexity
universe u v

namespace P202.Topology
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

variable {V : Type u} {W : Type v}

/-- The topology in the independent interface is final for the closed simplices. -/
theorem realization_continuous_iff (K : AbstractSimplicialComplex V)
    {Y : Type*} [TopologicalSpace Y] (f : K.Realization → Y) :
    Continuous f ↔ ∀ s : K.Simplex, Continuous (f ∘ K.simplexChart s) := by
  change @Continuous _ _ (⨆ s : K.Simplex,
    TopologicalSpace.coinduced (K.simplexChart s) inferInstance) _ f ↔ _
  simp only [continuous_iSup_dom, continuous_coinduced_dom]

theorem continuous_simplexChart (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    Continuous (K.simplexChart s) := by
  rw [continuous_iff_coinduced_le]
  exact le_iSup (fun s : K.Simplex =>
    TopologicalSpace.coinduced (K.simplexChart s) inferInstance) s

theorem continuous_realization_weight (K : AbstractSimplicialComplex V) (v : V) :
    Continuous (fun x : K.Realization => x.1.weights v) := by
  rw [realization_continuous_iff]
  intro s
  exact (Convexity.StdSimplex.continuous_weights_apply ℝ v).comp
    (Convexity.StdSimplex.continuous_map ℝ (Subtype.val : s.1 → V))

theorem continuous_realization_coordinates (K : AbstractSimplicialComplex V) :
    Continuous (fun x : K.Realization => x.1) := by
  rw [realization_continuous_iff]
  intro s
  exact Convexity.StdSimplex.continuous_map ℝ (Subtype.val : s.1 → V)

theorem activeCoordinates_map_val (K : AbstractSimplicialComplex V) (p : K.Realization) :
    (K.activeCoordinates p).map (Subtype.val : K.Vertex → V) = p.1 := by
  ext v
  simp only [Convexity.StdSimplex.weights_map]
  by_cases hv : ({v} : Finset V) ∈ K.simplices
  · change (Finsupp.mapDomain (Subtype.val : K.Vertex → V)
      (p.1.weights.subtypeDomain _)) v = _
    simpa using Finsupp.mapDomain_apply_of_injective Subtype.val_injective
      (p.1.weights.subtypeDomain _) (⟨v, hv⟩ : K.Vertex)
  · have hz : p.1.weights v = 0 := by
      by_contra hn
      exact hv (vertex_mem_of_mem p.2 (Finsupp.mem_support_iff.mpr hn))
    rw [hz]
    apply Finsupp.mapDomain_of_notMem_range
    simpa using hv

theorem activeCoordinates_simplexChart (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (p : K.GeometricSimplex s) :
    K.activeCoordinates (K.simplexChart s p) =
      p.map (fun v : s.1 => (⟨v.1, vertex_mem_of_mem s.2 v.2⟩ : K.Vertex)) := by
  have h : (K.activeCoordinates (K.simplexChart s p)).map
      (Subtype.val : K.Vertex → V) =
      (p.map (fun v : s.1 => (⟨v.1, vertex_mem_of_mem s.2 v.2⟩ : K.Vertex))).map
        (Subtype.val : K.Vertex → V) := by
    rw [activeCoordinates_map_val, Convexity.StdSimplex.map_map]
    rfl
  ext v
  have hv := congrArg (fun q : Convexity.StdSimplex ℝ V => q.weights v.1) h
  simpa only [Convexity.StdSimplex.weights_map,
    Finsupp.mapDomain_apply_of_injective Subtype.val_injective] using hv

theorem simplexChart_factor_map {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W} (g : SimplicialMap K L) (s : K.Simplex) :
    g.realization ∘ K.simplexChart s =
      L.simplexChart ⟨(K.simplexVertices s).image g.vertex, g.map_simplex s⟩ ∘
        Convexity.StdSimplex.map (fun v : s.1 =>
          (⟨g.vertex ⟨v.1, vertex_mem_of_mem s.2 v.2⟩, by
            apply Finset.mem_image.mpr
            refine ⟨⟨v.1, vertex_mem_of_mem s.2 v.2⟩, ?_, rfl⟩
            simp [simplexVertices]
            exact ⟨v, by simp, rfl⟩⟩ :
              ↥((K.simplexVertices s).image g.vertex))) := by
  funext p
  apply Subtype.ext
  change (K.activeCoordinates (K.simplexChart s p)).map g.vertex =
    (p.map _).map Subtype.val
  rw [activeCoordinates_simplexChart, Convexity.StdSimplex.map_map,
    Convexity.StdSimplex.map_map]

theorem simplicialMap_continuous {K : AbstractSimplicialComplex V}
    {L : AbstractSimplicialComplex W} (g : SimplicialMap K L) : Continuous g.realization := by
  rw [realization_continuous_iff]
  intro s
  rw [simplexChart_factor_map]
  exact (continuous_simplexChart L _).comp (Convexity.StdSimplex.continuous_map ℝ _)

theorem openStar_isOpen (K : AbstractSimplicialComplex V) (v : K.Vertex) :
    IsOpen (K.openStar v) :=
  isOpen_lt continuous_const (continuous_realization_weight K v.1)

theorem openStars_cover (K : AbstractSimplicialComplex V) :
    (⋃ v : K.Vertex, K.openStar v) = univ := by
  apply eq_univ_of_forall
  intro x
  obtain ⟨v, hv⟩ := x.1.support_weights_nonempty
  have hpos : 0 < x.1.weights v :=
    lt_of_le_of_ne (x.1.weights_nonneg v) (Ne.symm (Finsupp.mem_support_iff.mp hv))
  exact mem_iUnion.mpr ⟨⟨v, vertex_mem_of_mem x.2 hv⟩, hpos⟩

theorem subBarycenter_support (s : Finset V) (hs : s.Nonempty) :
    (Convexity.StdSimplex.subBarycenter (K := ℝ) s hs).weights.support = s := by
  ext v
  by_cases hv : v ∈ s
  · simp only [Finsupp.mem_support_iff]
    have hcard : (s.card : ℝ) ≠ 0 := by exact_mod_cast hs.card_pos.ne'
    have hw : (Convexity.StdSimplex.subBarycenter (K := ℝ) s hs).weights v =
        (s.card : ℝ)⁻¹ := by
      simp only [Convexity.StdSimplex.weights_subBarycenter,
        Finsupp.coe_finsetSum, Finset.sum_apply]
      rw [Finset.sum_eq_single v]
      · simp
      · intro b hb hne
        exact Finsupp.single_eq_of_ne hne.symm
      · exact fun h => (h hv).elim
    simp [hw, hcard, hv]
  · simp [Finsupp.mem_support_iff,
      Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero s hs v hv, hv]

theorem exists_simplex_interior_point (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    ∃ x : K.Realization, ∀ v ∈ s.1, 0 < x.1.weights v := by
  let p := Convexity.StdSimplex.subBarycenter (K := ℝ) s.1 (K.nonempty _ s.2)
  have hs : p.weights.support = s.1 := subBarycenter_support _ _
  refine ⟨⟨p, hs.symm ▸ s.2⟩, fun v hv => ?_⟩
  exact lt_of_le_of_ne (p.weights_nonneg v)
    (Ne.symm (Finsupp.mem_support_iff.mp (hs.symm ▸ hv)))

theorem starCriterion_map (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (f : K.Realization → L.Realization)
    (a : K.Vertex → W)
    (ha : ∀ v x, x ∈ K.openStar v → 0 < (f x).1.weights (a v)) :
    ∃ g : SimplicialMap K L, g.vertex = a ∧
      ∀ x, (g.realization x).1.weights.support ⊆ (f x).1.weights.support := by
  have hg : ∀ s : K.Simplex, (K.simplexVertices s).image a ∈ L.simplices := by
    intro s
    obtain ⟨x, hx⟩ := exists_simplex_interior_point K s
    apply L.face (f x).2 _
      (Finset.Nonempty.image ((K.nonempty s.1 s.2).attach.map) a)
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have hvs : v.1 ∈ s.1 := by
      rcases Finset.mem_map.mp hv with ⟨z, hz, heq⟩
      have heq' := congrArg Subtype.val heq
      change z.1 = v.1 at heq'
      exact heq' ▸ z.2
    exact Finsupp.mem_support_iff.mpr (ha v x (hx v.1 hvs)).ne'
  refine ⟨⟨a, hg⟩, rfl, ?_⟩
  intro x w hw
  rw [SimplicialMap.realization, Convexity.StdSimplex.weights_map,
    Finsupp.support_mapDomain_of_nonneg (K.activeCoordinates x).nonneg] at hw
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
  have hvne : x.1.weights v.1 ≠ 0 := by
    simpa only [activeCoordinates, Finsupp.subtypeDomain_apply] using
      (Finsupp.mem_support_iff.mp hv)
  have hv' : 0 < x.1.weights v.1 :=
    lt_of_le_of_ne (x.1.weights_nonneg v.1) hvne.symm
  exact Finsupp.mem_support_iff.mpr (ha v x hv').ne' 

theorem subdivision_face_compatibility {K L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) (x : K.barycentricSubdivision.Realization) :
    L.subdivisionMap (subdivisionInclusion h x) = inclusionRealization h (K.subdivisionMap x) := by
  apply Subtype.ext
  change (x.1.map (fun s : K.Simplex => (⟨s.1, h s.2⟩ : L.Simplex))).iConvexComb
    L.simplexBarycenter = x.1.iConvexComb K.simplexBarycenter
  rw [Convexity.iConvexComb_map]
  rfl

/-- Restrict a distribution to a finite set containing its support. -/
private def simplexCoordinates (p : Convexity.StdSimplex ℝ V) (s : Finset V)
    (h : p.weights.support ⊆ s) : Convexity.StdSimplex ℝ s where
  weights := p.weights.subtypeDomain (· ∈ s)
  nonneg v := p.weights_nonneg v.1
  total := by
    calc
      _ = p.weights.sum (fun (_ : V) r => r) :=
        Finsupp.sum_subtypeDomain_index (h := fun (_ : V) (r : ℝ) => r) h
      _ = 1 := p.total

private theorem simplexCoordinates_map_val (p : Convexity.StdSimplex ℝ V) (s : Finset V)
    (h : p.weights.support ⊆ s) :
    (simplexCoordinates p s h).map (Subtype.val : s → V) = p := by
  ext v
  simp only [Convexity.StdSimplex.weights_map]
  by_cases hv : v ∈ s
  · simpa only [Finsupp.mapDomain_apply_of_injective Subtype.val_injective,
      simplexCoordinates, Finsupp.subtypeDomain_apply] using
      Finsupp.mapDomain_apply_of_injective Subtype.val_injective
        (p.weights.subtypeDomain (· ∈ s)) (⟨v, hv⟩ : s)
  · have hz : p.weights v = 0 := Finsupp.notMem_support_iff.mp (fun hv' => hv (h hv'))
    rw [hz]
    apply Finsupp.mapDomain_of_notMem_range
    simpa using hv

theorem simplexCharts_cover (K : AbstractSimplicialComplex V) :
    (⋃ s : K.Simplex, range (K.simplexChart s)) = univ := by
  apply eq_univ_of_forall
  intro p
  refine mem_iUnion.mpr ⟨⟨p.1.weights.support, p.2⟩, ?_⟩
  refine ⟨simplexCoordinates p.1 p.1.weights.support (fun _ h => h), ?_⟩
  apply Subtype.ext
  exact simplexCoordinates_map_val _ _ _

theorem finiteRealization_compact (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    IsCompact (univ : Set K.Realization) := by
  let : Finite K.Simplex := hK.to_subtype
  rw [← simplexCharts_cover K]
  exact isCompact_iUnion (fun s => isCompact_range (continuous_simplexChart K s))

theorem finite_vertex (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    Finite K.Vertex := by
  let : Finite K.Simplex := hK.to_subtype
  apply Finite.of_injective (fun v : K.Vertex => (⟨{v.1}, v.2⟩ : K.Simplex))
  intro a b h
  apply Subtype.ext
  exact Finset.singleton_injective (congrArg Subtype.val h)

theorem finite_subdivision (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    K.barycentricSubdivision.IsFinite := by
  let : Finite K.Simplex := hK.to_subtype
  exact Set.toFinite _

theorem finite_iteratedSubdivision (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    ∀ n, (K.Subdivision n).IsFinite
  | 0 => hK
  | n + 1 => finite_subdivision _ (finite_iteratedSubdivision K hK n)

theorem subdivision_chain_card_le {K : AbstractSimplicialComplex V}
    {c : Finset K.Simplex} (hc : c ∈ K.barycentricSubdivision.simplices)
    {s : K.Simplex} (hs : ∀ t ∈ c, t.1 ⊆ s.1) : c.card ≤ s.1.card := by
  classical
  have hinj : Set.InjOn (fun t : K.Simplex => t.1.card) c := by
    intro a ha b hb hab
    apply Subtype.ext
    rcases hc.2 a ha b hb with h | h
    · exact Finset.eq_of_subset_of_card_le h (le_of_eq hab.symm)
    · exact (Finset.eq_of_subset_of_card_le h (le_of_eq hab)).symm
  calc
    c.card = (c.image (fun t : K.Simplex => t.1.card)).card :=
      (Finset.card_image_of_injOn hinj).symm
    _ ≤ (Finset.Icc 1 s.1.card).card := by
      apply Finset.card_le_card
      intro m hm
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hm
      exact Finset.mem_Icc.mpr ⟨(K.nonempty t.1 t.2).card_pos,
        Finset.card_le_card (hs t ht)⟩
    _ = s.1.card := by simp

theorem subdivision_simplex_card_bound (K : AbstractSimplicialComplex V)
    (D : ℕ) (hK : ∀ s : K.Simplex, s.1.card ≤ D) :
    ∀ s : K.barycentricSubdivision.Simplex, s.1.card ≤ D := by
  intro c
  obtain ⟨s, hs, htop⟩ := chain_has_largest c.2
  exact (subdivision_chain_card_le c.2 htop).trans (hK s)

theorem iteratedSubdivision_simplex_card_bound (K : AbstractSimplicialComplex V)
    (D : ℕ) (hK : ∀ s : K.Simplex, s.1.card ≤ D) :
    ∀ n, ∀ s : (K.Subdivision n).Simplex, s.1.card ≤ D
  | 0 => hK
  | n + 1 => subdivision_simplex_card_bound _ D
      (iteratedSubdivision_simplex_card_bound K D hK n)

end P202.Topology

namespace P202.Topology
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

theorem finite_complex_simplex_card_bound {V : Type u}
    (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    ∃ D : ℕ, ∀ n, ∀ s : (K.Subdivision n).Simplex, s.1.card ≤ D := by
  classical
  refine ⟨hK.toFinset.sup Finset.card, ?_⟩
  apply iteratedSubdivision_simplex_card_bound
  intro s
  exact Finset.le_sup (f := Finset.card) (hK.mem_toFinset.mpr s.2)

theorem finite_realization_metric (K : AbstractSimplicialComplex V) (hK : K.IsFinite) :
    ∃ d : MetricSpace K.Realization,
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
        (inferInstance : TopologicalSpace K.Realization) ∧
      @D10Topology.Ch05.CoverCompact K.Realization
        (D10Topology.Ch09.metricTopology d.toPseudoMetricSpace) := by
  let : Finite K.Vertex := finite_vertex K hK
  let : Fintype K.Vertex := Fintype.ofFinite _
  let : CompactSpace K.Realization := ⟨finiteRealization_compact K hK⟩
  let c : K.Realization → K.Vertex → ℝ := fun p v => p.1.weights v.1
  have hc : Continuous c := continuous_pi (fun v => continuous_realization_weight K v.1)
  have hinj : Function.Injective c := by
    intro p q h
    apply Subtype.ext
    ext v
    by_cases hv : ({v} : Finset V) ∈ K.simplices
    · exact congrFun h ⟨v, hv⟩
    · have hp : p.1.weights v = 0 := by
        by_contra h'
        exact hv (vertex_mem_of_mem p.2 (Finsupp.mem_support_iff.mpr h'))
      have hq : q.1.weights v = 0 := by
        by_contra h'
        exact hv (vertex_mem_of_mem q.2 (Finsupp.mem_support_iff.mpr h'))
      rw [hp, hq]
  let d : MetricSpace K.Realization := (hc.isClosedEmbedding hinj).isEmbedding.comapMetricSpace c
  refine ⟨d, rfl, ?_⟩
  exact (D10Topology.Ch05.coverCompact_iff_isCompact_univ K.Realization).mpr
    (finiteRealization_compact K hK)

/-- On a compact space, compatible metrics give the same uniform control
of the extended diameters of arbitrary subsets, including empty ones. -/
theorem compact_metric_diameter_control {X : Type u} (d₀ d : MetricSpace X)
    (hc : @D10Topology.Ch05.CoverCompact X
      (D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace))
    (ht : D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace =
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set X,
      D10Topology.Ch09.diameter d₀.toPseudoMetricSpace A < ENNReal.ofReal δ →
      D10Topology.Ch09.diameter d.toPseudoMetricSpace A < ENNReal.ofReal ε := by
  have hid : @Continuous X X
      (D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace)
      (D10Topology.Ch09.metricTopology d.toPseudoMetricSpace) id := by
    rw [← ht]
    exact @continuous_id X (D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace)
  have hu := D10Topology.Ch09.compact_continuous_uniformlyContinuous d₀ d hc id hid
  obtain ⟨δ, hδ, hsmall⟩ := hu (ε / 2) (half_pos hε)
  refine ⟨δ, hδ, fun A hA => ?_⟩
  have hle : D10Topology.Ch09.diameter d.toPseudoMetricSpace A ≤
      ENNReal.ofReal (ε / 2) := by
    apply (D10Topology.Ch09.diameter_le_iff _ _ _).mpr
    intro x hx y hy
    have hxy : ENNReal.ofReal (D10Topology.Ch09.distance d₀.toPseudoMetricSpace x y) ≤
        D10Topology.Ch09.diameter d₀.toPseudoMetricSpace A :=
      le_iSup_of_le x (le_iSup_of_le hx (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))
    have hdist : D10Topology.Ch09.distance d₀.toPseudoMetricSpace x y < δ :=
      (ENNReal.ofReal_lt_ofReal_iff hδ).mp (hxy.trans_lt hA)
    exact ENNReal.ofReal_le_ofReal (le_of_lt (hsmall x y hdist))
  exact hle.trans_lt ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (half_lt_self hε))

/-- Uniform shrinking of arbitrary varying families of subsets transfers
between compatible metrics on a compact space. -/
theorem compact_metric_shrinking_transfer {X : Type u} (d₀ d : MetricSpace X)
    (hc : @D10Topology.Ch05.CoverCompact X
      (D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace))
    (ht : D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace =
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace)
    {I : ℕ → Type v} (A : ∀ n, I n → Set X)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ i,
      D10Topology.Ch09.diameter d₀.toPseudoMetricSpace (A n i) < ENNReal.ofReal ε) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ i,
      D10Topology.Ch09.diameter d.toPseudoMetricSpace (A n i) < ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨δ, hδ, hsmall⟩ := compact_metric_diameter_control d₀ d hc ht ε hε
  obtain ⟨N, hN⟩ := hA δ hδ
  exact ⟨N, fun n hn i => hsmall _ (hN n hn i)⟩

theorem finiteRealization_metric_diameter_control {V : Type u}
    (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (d₀ d : MetricSpace K.Realization)
    (h₀ : D10Topology.Ch09.metricTopology d₀.toPseudoMetricSpace =
      (inferInstance : TopologicalSpace K.Realization))
    (hd : D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
      (inferInstance : TopologicalSpace K.Realization))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ A : Set K.Realization,
      D10Topology.Ch09.diameter d₀.toPseudoMetricSpace A < ENNReal.ofReal δ →
      D10Topology.Ch09.diameter d.toPseudoMetricSpace A < ENNReal.ofReal ε := by
  apply compact_metric_diameter_control d₀ d _ (h₀.trans hd.symm) ε hε
  rw [h₀]
  exact (D10Topology.Ch05.coverCompact_iff_isCompact_univ K.Realization).mpr
    (finiteRealization_compact K hK)

private theorem iConvexComb_weights {I J : Type*} (p : Convexity.StdSimplex ℝ I)
    (a : I → Convexity.StdSimplex ℝ J) :
    (p.iConvexComb a).weights = p.weights.sum (fun i r => r • (a i).weights) := by
  change ((p.map a).weights.sum (fun d r => r • d.weights)) = _
  rw [Convexity.StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index
      (h := fun (d : Convexity.StdSimplex ℝ J) (r : ℝ) => r • d.weights)
      (fun d => zero_smul ℝ d.weights) (fun d r s => add_smul r s d.weights)]

private theorem continuous_iConvexComb_finite {I J : Type*} [Finite I] [Finite J]
    (a : I → Convexity.StdSimplex ℝ J) :
    Continuous (fun p : Convexity.StdSimplex ℝ I => p.iConvexComb a) := by
  let := Fintype.ofFinite I
  apply (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ J).continuous_iff.mpr
  apply continuous_pi
  intro j
  have heq (p : Convexity.StdSimplex ℝ I) :
      (p.iConvexComb a).weights j = ∑ i : I, p.weights i * (a i).weights j := by
    rw [iConvexComb_weights, Finsupp.sum_apply]
    simp only [Finsupp.smul_apply, smul_eq_mul]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_mul _)
  simp only [Function.comp_def, heq]
  exact continuous_finsetSum _ (fun i _ =>
    (Convexity.StdSimplex.continuous_weights_apply ℝ i).mul continuous_const)

theorem subdivisionMap_continuous (K : AbstractSimplicialComplex V) :
    Continuous K.subdivisionMap := by
  rw [realization_continuous_iff]
  intro c
  obtain ⟨s, hs, htop⟩ := chain_has_largest c.2
  let b : c.1 → Convexity.StdSimplex ℝ s.1 := fun t =>
    simplexCoordinates (K.simplexBarycenter t.1) s.1 (by
      rw [simplexBarycenter, subBarycenter_support]
      exact htop t.1 t.2)
  have hfac : K.subdivisionMap ∘ K.barycentricSubdivision.simplexChart c =
      K.simplexChart s ∘ (fun p : Convexity.StdSimplex ℝ c.1 => p.iConvexComb b) := by
    funext p
    apply Subtype.ext
    change (p.map (Subtype.val : c.1 → K.Simplex)).iConvexComb K.simplexBarycenter =
      (p.iConvexComb b).map (Subtype.val : s.1 → V)
    rw [Convexity.iConvexComb_map]
    simp only [Convexity.iConvexComb, Convexity.StdSimplex.map_sConvexComb,
      Convexity.StdSimplex.map_map]
    congr 2
    funext t
    exact (simplexCoordinates_map_val _ _ _).symm
  rw [hfac]
  exact (continuous_simplexChart K s).comp (continuous_iConvexComb_finite b)

theorem iteratedSubdivisionMap_continuous (K : AbstractSimplicialComplex V) :
    ∀ n, Continuous (K.iteratedSubdivisionMap n)
  | 0 => continuous_id
  | n + 1 => (iteratedSubdivisionMap_continuous K n).comp (subdivisionMap_continuous _)

def subdivisionVertexImages (K : AbstractSimplicialComplex V) :
    ∀ n, (K.iteratedComplex n).1 → Convexity.StdSimplex ℝ V
  | 0 => Convexity.StdSimplex.single
  | n + 1 => fun s => ((K.Subdivision n).simplexBarycenter s).iConvexComb
      (subdivisionVertexImages K n)

theorem iteratedSubdivisionMap_coordinates (K : AbstractSimplicialComplex V) :
    ∀ n (p : (K.Subdivision n).Realization),
      (K.iteratedSubdivisionMap n p).1 = p.1.iConvexComb (subdivisionVertexImages K n)
  | 0, p => by
      change p.1 = p.1.iConvexComb Convexity.StdSimplex.single
      exact (Convexity.StdSimplex.iConvexComb_single p.1).symm
  | n + 1, p => by
      change (K.iteratedSubdivisionMap n ((K.Subdivision n).subdivisionMap p)).1 = _
      rw [iteratedSubdivisionMap_coordinates]
      exact (Convexity.iConvexComb_assoc p.1 (K.Subdivision n).simplexBarycenter
        (subdivisionVertexImages K n)).symm

def coordinateVector (K : AbstractSimplicialComplex V) (p : Convexity.StdSimplex ℝ V) :
    K.Vertex → ℝ := fun v => p.weights v.1

theorem coordinateVector_iConvexComb (K : AbstractSimplicialComplex V)
    {I : Type*} (p : Convexity.StdSimplex ℝ I) (a : I → Convexity.StdSimplex ℝ V) :
    coordinateVector K (p.iConvexComb a) =
      p.iConvexComb (fun i => coordinateVector K (a i)) := by
  funext v
  simp only [coordinateVector, iConvexComb_weights, Finsupp.sum_apply, Finsupp.sum_apply',
    Finsupp.smul_apply, Convexity.iConvexComb_eq_sum, Pi.smul_apply, smul_eq_mul]

theorem finiteRealization_activeCoordinateEmbedding (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) :
    IsEmbedding (fun x : K.Realization => coordinateVector K x.1) := by
  let : CompactSpace K.Realization := ⟨finiteRealization_compact K hK⟩
  apply IsClosedEmbedding.isEmbedding
  apply Continuous.isClosedEmbedding
  · exact continuous_pi (fun v => continuous_realization_weight K v.1)
  · intro p q h
    apply Subtype.ext
    ext v
    by_cases hv : ({v} : Finset V) ∈ K.simplices
    · exact congrFun h ⟨v, hv⟩
    · have hp : p.1.weights v = 0 := by
        by_contra h'
        exact hv (vertex_mem_of_mem p.2 (Finsupp.mem_support_iff.mpr h'))
      have hq : q.1.weights v = 0 := by
        by_contra h'
        exact hv (vertex_mem_of_mem q.2 (Finsupp.mem_support_iff.mpr h'))
      rw [hp, hq]

/-- The finite coordinate metric has exactly the weak topology and its
specified distance is the sup distance of the active coordinates. -/
theorem finite_realization_coordinate_metric (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) [Fintype K.Vertex] :
    ∃ d : MetricSpace K.Realization,
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
        (inferInstance : TopologicalSpace K.Realization) ∧
      @D10Topology.Ch05.CoverCompact K.Realization
        (D10Topology.Ch09.metricTopology d.toPseudoMetricSpace) ∧
      ∀ x y, D10Topology.Ch09.distance d.toPseudoMetricSpace x y =
        dist (coordinateVector K x.1) (coordinateVector K y.1) := by
  let d := (finiteRealization_activeCoordinateEmbedding K hK).comapMetricSpace
    (fun x : K.Realization => coordinateVector K x.1)
  refine ⟨d, rfl, ?_, fun _ _ => rfl⟩
  exact (D10Topology.Ch05.coverCompact_iff_isCompact_univ K.Realization).mpr
    (finiteRealization_compact K hK)

theorem coordinateVector_dist_le_one (K : AbstractSimplicialComplex V)
    [Fintype K.Vertex] (p q : Convexity.StdSimplex ℝ V) :
    dist (coordinateVector K p) (coordinateVector K q) ≤ 1 := by
  apply (dist_pi_le_iff (by norm_num : (0 : ℝ) ≤ 1)).mpr
  intro v
  change dist (p.weights v.1) (q.weights v.1) ≤ 1
  rw [Real.dist_eq, abs_sub_le_iff]
  constructor <;> linarith [p.weights_nonneg v.1, q.weights_nonneg v.1,
    p.weights_apply_le_one v.1, q.weights_apply_le_one v.1]

theorem real_iConvexComb_le {I : Type*} (p : StdSimplex ℝ I)
    (a : I → ℝ) (r : ℝ) (ha : ∀ i ∈ p.weights.support, a i ≤ r) :
    p.iConvexComb a ≤ r := by
  rw [iConvexComb_eq_sum]
  change p.weights.sum (fun i t => t * a i) ≤ r
  calc
    p.weights.sum (fun i t => t * a i) ≤ p.weights.sum (fun _ t => t * r) :=
      Finsupp.sum_le_sum (h₁ := fun i t => t * a i) (h₂ := fun _ t => t * r)
        (fun i hi => mul_le_mul_of_nonneg_left (ha i hi) (p.nonneg i))
    _ = r := by rw [← Finsupp.sum_mul, p.total, one_mul]

theorem dist_iConvexComb_le_of_pairwise {I J X : Type*}
    [ConvexSpace ℝ X] [MetricSpace X] [IsConvexDist X]
    (p : StdSimplex ℝ I) (q : StdSimplex ℝ J)
    (a : I → X) (b : J → X) (r : ℝ)
    (h : ∀ i ∈ p.weights.support, ∀ j ∈ q.weights.support, dist (a i) (b j) ≤ r) :
    dist (p.iConvexComb a) (q.iConvexComb b) ≤ r := by
  apply (dist_iConvexComb_left_le p a _).trans
  apply real_iConvexComb_le
  intro i hi
  apply (dist_iConvexComb_right_le (a i) q b).trans
  exact real_iConvexComb_le q _ r (h i hi)

theorem subBarycenter_weight_of_mem {I : Type*}
    (s : Finset I) (hs : s.Nonempty) {i : I} (hi : i ∈ s) :
    (StdSimplex.subBarycenter (K := ℝ) s hs).weights i = (s.card : ℝ)⁻¹ := by
  simp only [StdSimplex.weights_subBarycenter, Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hne
    exact Finsupp.single_eq_of_ne hne.symm
  · exact fun h => (h hi).elim

/-- A uniform distribution on a face splits into the uniform distributions on
that face's chosen subface and its complementary vertices. -/
theorem subBarycenter_split {I : Type*} (F G : Finset I)
    (hF : F.Nonempty) (hFG : F ⊆ G) (hC : (G \ F).Nonempty) :
    StdSimplex.subBarycenter (K := ℝ) G (hF.mono hFG) =
      convexCombPair ((F.card : ℝ) / G.card) ((G \ F).card / (G.card : ℝ))
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
        (by rw [← add_div, ← Nat.cast_add, (by simpa [add_comm] using Finset.card_sdiff_add_card_eq_card hFG : F.card + (G \ F).card = G.card),
          div_self (by exact_mod_cast (hF.mono hFG).card_pos.ne')])
        (StdSimplex.subBarycenter F hF) (StdSimplex.subBarycenter (K := ℝ) (G \ F) hC) := by
  ext i
  simp only [StdSimplex.weights_convexCombPair, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul]
  have hFn : (F.card : ℝ) ≠ 0 := by exact_mod_cast hF.card_pos.ne'
  have hGn : (G.card : ℝ) ≠ 0 := by exact_mod_cast (hF.mono hFG).card_pos.ne'
  have hCn : ((G \ F).card : ℝ) ≠ 0 := by exact_mod_cast hC.card_pos.ne'
  by_cases hiF : i ∈ F
  · rw [subBarycenter_weight_of_mem _ _ (hFG hiF),
      subBarycenter_weight_of_mem _ _ hiF,
      StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i (by simp [hiF])]
    field_simp
    ring
  · by_cases hiG : i ∈ G
    · rw [subBarycenter_weight_of_mem _ _ hiG,
        StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i hiF,
        subBarycenter_weight_of_mem _ _ (Finset.mem_sdiff.mpr ⟨hiG, hiF⟩)]
      field_simp
      ring
    · rw [StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i hiG,
        StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i hiF,
        StdSimplex.subBarycenter_weights_apply_eq_zero _ _ i (by simp [hiG])]
      simp

/-- The contraction between nested face barycenters holds in any convex metric
space, with the exact ratio of the two face cardinalities. -/
theorem nested_barycenter_dist_le {I X : Type*}
    [ConvexSpace ℝ X] [MetricSpace X] [IsConvexDist X]
    (F G : Finset I) (hF : F.Nonempty) (hFG : F ⊆ G)
    (a : I → X) (r : ℝ) (_hr : 0 ≤ r)
    (h : ∀ i ∈ G, ∀ j ∈ G, dist (a i) (a j) ≤ r) :
    dist ((StdSimplex.subBarycenter (K := ℝ) F hF).iConvexComb a)
      ((StdSimplex.subBarycenter (K := ℝ) G (hF.mono hFG)).iConvexComb a) ≤
      (1 - (F.card : ℝ) / G.card) * r := by
  by_cases hEq : F = G
  · subst G
    simp [div_self (show (F.card : ℝ) ≠ 0 by exact_mod_cast hF.card_pos.ne')]
  have hC : (G \ F).Nonempty :=
    Finset.sdiff_nonempty.mpr (fun hGF => hEq (Finset.Subset.antisymm hFG hGF))
  rw [subBarycenter_split F G hF hFG hC]
  have heval {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (hst : s + t = 1)
      (p q : StdSimplex ℝ I) :
      (convexCombPair s t hs ht hst p q).iConvexComb a =
        convexCombPair s t hs ht hst (p.iConvexComb a) (q.iConvexComb a) :=
    (StdSimplex.affineMapMk a).isAffineMap.map_convexCombPair hs ht hst p q
  rw [heval]
  rw [dist_left_convexCombPair]
  have hdist :
      dist ((StdSimplex.subBarycenter (K := ℝ) F hF).iConvexComb a)
        ((StdSimplex.subBarycenter (K := ℝ) (G \ F) hC).iConvexComb a) ≤ r := by
    apply dist_iConvexComb_le_of_pairwise
    intro i hi j hj
    rw [subBarycenter_support] at hi hj
    exact h i (hFG hi) j (Finset.mem_sdiff.mp hj).1
  have hrat : ((G \ F).card : ℝ) / G.card = 1 - (F.card : ℝ) / G.card := by
    have hGn : (G.card : ℝ) ≠ 0 := by exact_mod_cast (hF.mono hFG).card_pos.ne'
    have hc : (F.card : ℝ) + (G \ F).card = G.card := by
      exact_mod_cast (by simpa [add_comm] using Finset.card_sdiff_add_card_eq_card hFG : F.card + (G \ F).card = G.card)
    field_simp
    linarith
  rw [← hrat]
  exact mul_le_mul_of_nonneg_left hdist
    (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))

theorem barycenter_contraction_factor_le (F G : ℕ) (hF : 0 < F)
    (hG : 0 < G) (D : ℕ) (hGD : G ≤ D) (r : ℝ) (hr : 0 ≤ r) :
    (1 - (F : ℝ) / G) * r ≤ (1 - 1 / (D : ℝ)) * r := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast lt_of_lt_of_le hG hGD
  have hGr : (0 : ℝ) < G := by exact_mod_cast hG
  have hFr : (1 : ℝ) ≤ F := by exact_mod_cast hF
  have hGDr : (G : ℝ) ≤ D := by exact_mod_cast hGD
  have hfrac : 1 / (D : ℝ) ≤ (F : ℝ) / G := by
    apply (div_le_div_iff₀ hDr hGr).mpr
    nlinarith
  exact mul_le_mul_of_nonneg_right (sub_le_sub_left hfrac 1) hr

theorem subdivision_chain_pairwise_contraction {V : Type u}
    (K : AbstractSimplicialComplex V)
    {X : Type v} [ConvexSpace ℝ X] [MetricSpace X] [IsConvexDist X]
    (a : V → X) (D : ℕ) (hcard : ∀ s : K.Simplex, s.1.card ≤ D)
    (r : ℝ) (hr : 0 ≤ r)
    (hold : ∀ s : K.Simplex, ∀ i ∈ s.1, ∀ j ∈ s.1, dist (a i) (a j) ≤ r)
    (c : K.barycentricSubdivision.Simplex) :
    ∀ s ∈ c.1, ∀ t ∈ c.1,
      dist (((K.simplexBarycenter s).iConvexComb a))
        (((K.simplexBarycenter t).iConvexComb a)) ≤ (1 - 1 / (D : ℝ)) * r := by
  intro s hs t ht
  rcases c.2.2 s hs t ht with h | h
  · exact (nested_barycenter_dist_le s.1 t.1 (K.nonempty _ s.2) h a r hr (hold t)).trans
      (barycenter_contraction_factor_le s.1.card t.1.card
        (K.nonempty _ s.2).card_pos (K.nonempty _ t.2).card_pos D (hcard t) r hr)
  · rw [dist_comm]
    exact (nested_barycenter_dist_le t.1 s.1 (K.nonempty _ t.2) h a r hr (hold s)).trans
      (barycenter_contraction_factor_le t.1.card s.1.card
        (K.nonempty _ t.2).card_pos (K.nonempty _ s.2).card_pos D (hcard s) r hr)

/-- Iteration gives a uniform geometric estimate on the images of all vertices
of a simplex at every stage. -/
theorem subdivision_coordinate_vertex_dist_le {V : Type u}
    (K : AbstractSimplicialComplex V) [Fintype K.Vertex]
    (D : ℕ) (hD : 0 < D)
    (hcard : ∀ s : K.Simplex, s.1.card ≤ D) :
    ∀ n, ∀ s : (K.Subdivision n).Simplex, ∀ i ∈ s.1, ∀ j ∈ s.1,
      dist (coordinateVector K (subdivisionVertexImages K n i))
        (coordinateVector K (subdivisionVertexImages K n j)) ≤
          (1 - 1 / (D : ℝ)) ^ n := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hq : 0 ≤ 1 - 1 / (D : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hDr).mpr (by simpa using hD1)
  intro n
  induction n with
  | zero =>
    intro s i hi j hj
    simpa using coordinateVector_dist_le_one K
      (subdivisionVertexImages K 0 i) (subdivisionVertexImages K 0 j)
  | succ n ih =>
    intro c s hs t ht
    have hnonneg : 0 ≤ (1 - 1 / (D : ℝ)) ^ n := pow_nonneg hq n
    have hstep := subdivision_chain_pairwise_contraction (K.Subdivision n)
      (fun v => coordinateVector K (subdivisionVertexImages K n v)) D
      (iteratedSubdivision_simplex_card_bound K D hcard n)
      ((1 - 1 / (D : ℝ)) ^ n) hnonneg ih c s hs t ht
    simp only [subdivisionVertexImages, coordinateVector_iConvexComb]
    simpa [pow_succ, mul_comm] using hstep

/-- The geometric bound tends to zero, including the zero-ratio case D=1. -/
theorem subdivision_contraction_eventually_lt (D : ℕ) (hD : 0 < D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → (1 - 1 / (D : ℝ)) ^ n < ε := by
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD
  have hD1 : (1 : ℝ) ≤ D := by exact_mod_cast hD
  have hq : 0 ≤ 1 - 1 / (D : ℝ) := by
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hDr).mpr (by simpa using hD1)
  have hqlt : 1 - 1 / (D : ℝ) < 1 := sub_lt_self _ (div_pos zero_lt_one hDr)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp
    (tendsto_pow_atTop_nhds_zero_of_lt_one hq hqlt) ε hε
  refine ⟨N, fun n hn => ?_⟩
  have hx := hN n hn
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (pow_nonneg hq n)] at hx
  exact hx

theorem subdivision_simplex_coordinate_diameter_le {V : Type u}
    (K : AbstractSimplicialComplex V) [Fintype K.Vertex]
    (d : MetricSpace K.Realization)
    (hd : ∀ x y, D10Topology.Ch09.distance d.toPseudoMetricSpace x y =
      dist (coordinateVector K x.1) (coordinateVector K y.1))
    (n : ℕ) (s : (K.Subdivision n).Simplex) (r : ℝ)
    (hvertex : ∀ i ∈ s.1, ∀ j ∈ s.1,
      dist (coordinateVector K (subdivisionVertexImages K n i))
        (coordinateVector K (subdivisionVertexImages K n j)) ≤ r) :
    D10Topology.Ch09.diameter d.toPseudoMetricSpace
      (K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s)) ≤
      ENNReal.ofReal r := by
  apply (D10Topology.Ch09.diameter_le_iff _ _ _).mpr
  rintro _ ⟨_, ⟨p, rfl⟩, rfl⟩ _ ⟨_, ⟨q, rfl⟩, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  rw [hd, iteratedSubdivisionMap_coordinates, iteratedSubdivisionMap_coordinates,
    coordinateVector_iConvexComb, coordinateVector_iConvexComb]
  change dist ((p.map (Subtype.val : s.1 → (K.iteratedComplex n).1)).iConvexComb
      (fun i => coordinateVector K (subdivisionVertexImages K n i)))
    ((q.map (Subtype.val : s.1 → (K.iteratedComplex n).1)).iConvexComb
      (fun i => coordinateVector K (subdivisionVertexImages K n i))) ≤ r
  rw [iConvexComb_map, iConvexComb_map]
  apply dist_iConvexComb_le_of_pairwise
  intro i hi j hj
  exact hvertex i.1 i.2 j.1 j.2

theorem subdivision_simplex_coordinate_mesh_tends_zero {V : Type u}
    (K : AbstractSimplicialComplex V) [Fintype K.Vertex]
    (d : MetricSpace K.Realization)
    (hd : ∀ x y, D10Topology.Ch09.distance d.toPseudoMetricSpace x y =
      dist (coordinateVector K x.1) (coordinateVector K y.1))
    (D : ℕ) (hD : 0 < D) (hcard : ∀ s : K.Simplex, s.1.card ≤ D)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n, N ≤ n → ∀ s : (K.Subdivision n).Simplex,
      D10Topology.Ch09.diameter d.toPseudoMetricSpace
        (K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s)) <
        ENNReal.ofReal ε := by
  obtain ⟨N, hN⟩ := subdivision_contraction_eventually_lt D hD ε hε
  refine ⟨N, fun n hn s => ?_⟩
  exact (subdivision_simplex_coordinate_diameter_le K d hd n s
    ((1 - 1 / (D : ℝ)) ^ n)
    (subdivision_coordinate_vertex_dist_le K D hD hcard n s)).trans_lt
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (hN n hn))

theorem subdivision_simplex_mesh_tends_zero {V : Type u}
    (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (d : MetricSpace K.Realization)
    (hd : D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
      (inferInstance : TopologicalSpace K.Realization)) :
    ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n → ∀ s : (K.Subdivision n).Simplex,
      D10Topology.Ch09.diameter d.toPseudoMetricSpace
        (K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s)) <
        ENNReal.ofReal ε := by
  let : Finite K.Vertex := finite_vertex K hK
  let : Fintype K.Vertex := Fintype.ofFinite _
  obtain ⟨d₀, h₀, hc, hcoords⟩ := finite_realization_coordinate_metric K hK
  obtain ⟨B, hB⟩ := finite_complex_simplex_card_bound K hK
  have hcard : ∀ s : K.Simplex, s.1.card ≤ B + 1 := by
    intro s
    exact (hB 0 s).trans (Nat.le_succ B)
  exact compact_metric_shrinking_transfer d₀ d hc (h₀.trans hd.symm)
    (fun n (s : (K.Subdivision n).Simplex) =>
      K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s))
    (subdivision_simplex_coordinate_mesh_tends_zero K d₀ hcoords (B + 1)
      (Nat.succ_pos B) hcard)

/-- The Lebesgue number is for the chosen metric, whose topology is proved
equal to the weak topology; its diameter premise concerns nonempty subsets. -/
theorem pullback_stars_lebesgue (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (hK : K.IsFinite)
    (f : C(K.Realization, L.Realization)) :
    ∃ d : MetricSpace K.Realization,
      D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
        (inferInstance : TopologicalSpace K.Realization) ∧
      ∃ ε : ℝ, 0 < ε ∧ ∀ A : Set K.Realization, A.Nonempty →
        D10Topology.Ch09.diameter d.toPseudoMetricSpace A < ENNReal.ofReal ε →
        ∃ w : L.Vertex, MapsTo f A (L.openStar w) := by
  obtain ⟨d, hd, hc⟩ := finite_realization_metric K hK
  let U : Set (Set K.Realization) := range (fun w : L.Vertex => f ⁻¹' L.openStar w)
  have hU : ∀ A ∈ U, IsOpen[D10Topology.Ch09.metricTopology d.toPseudoMetricSpace] A := by
    rintro A ⟨w, rfl⟩
    rw [hd]
    exact (openStar_isOpen L w).preimage f.continuous
  have hcover : (univ : Set K.Realization) ⊆ ⋃₀ U := by
    intro x _
    have hx : f x ∈ ⋃ w : L.Vertex, L.openStar w := by rw [openStars_cover]; trivial
    obtain ⟨w, hw⟩ := mem_iUnion.mp hx
    exact mem_sUnion.mpr ⟨_, ⟨w, rfl⟩, hw⟩
  obtain ⟨ε, hε, hsmall⟩ := D10Topology.Ch09.lebesgue_number d hc U hU hcover
  refine ⟨d, hd, ε, hε, ?_⟩
  intro A hA hdiam
  obtain ⟨B, ⟨w, rfl⟩, hB⟩ := hsmall A hA hdiam
  exact ⟨w, hB⟩

theorem openStar_nonempty (K : AbstractSimplicialComplex V) (v : K.Vertex) :
    (K.openStar v).Nonempty := by
  refine ⟨⟨Convexity.StdSimplex.single v.1, ?_⟩, ?_⟩
  · simpa using v.2
  · change 0 < (Convexity.StdSimplex.single (R := ℝ) v.1).weights v.1
    simp

theorem mem_simplexChart_iff_support_subset (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (x : K.Realization) :
    x ∈ Set.range (K.simplexChart s) ↔ x.1.weights.support ⊆ s.1 := by
  constructor
  · rintro ⟨p, rfl⟩
    intro w hw
    have hw' := Finsupp.mapDomain_support hw
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw'
    exact z.2
  · intro hx
    refine ⟨simplexCoordinates x.1 s.1 hx, ?_⟩
    apply Subtype.ext
    exact simplexCoordinates_map_val _ _ _

def vertexPoint (K : AbstractSimplicialComplex V) (v : K.Vertex) : K.Realization :=
  ⟨Convexity.StdSimplex.single v.1, by simpa using v.2⟩

theorem vertexPoint_mem_simplexChart (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (v : K.Vertex) (hv : v.1 ∈ s.1) :
    vertexPoint K v ∈ Set.range (K.simplexChart s) := by
  rw [mem_simplexChart_iff_support_subset]
  simpa [vertexPoint] using Finset.singleton_subset_iff.mpr hv

theorem distance_le_diameter {X : Type*} (d : PseudoMetricSpace X)
    {A : Set X} {x y : X} (hx : x ∈ A) (hy : y ∈ A) :
    ENNReal.ofReal (D10Topology.Ch09.distance d x y) ≤ D10Topology.Ch09.diameter d A := by
  exact le_iSup_of_le x (le_iSup_of_le hx
    (le_iSup_of_le y (le_iSup_of_le hy le_rfl)))

theorem openStar_image_diameter_le_two_mul (K : AbstractSimplicialComplex V)
    {X : Type v} (d : PseudoMetricSpace X) (f : K.Realization → X)
    (r : ℝ) (hr : 0 ≤ r)
    (hmesh : ∀ s : K.Simplex,
      D10Topology.Ch09.diameter d (f '' Set.range (K.simplexChart s)) ≤ ENNReal.ofReal r)
    (v : K.Vertex) :
    D10Topology.Ch09.diameter d (f '' K.openStar v) ≤ ENNReal.ofReal (2 * r) := by
  have hdist (x : K.Realization) (hx : x ∈ K.openStar v) :
      D10Topology.Ch09.distance d (f x) (f (vertexPoint K v)) ≤ r := by
    let s : K.Simplex := ⟨x.1.weights.support, x.2⟩
    have hxs : x ∈ Set.range (K.simplexChart s) := by
      rw [mem_simplexChart_iff_support_subset]
    have hvs : vertexPoint K v ∈ Set.range (K.simplexChart s) :=
      vertexPoint_mem_simplexChart K s v (Finsupp.mem_support_iff.mpr (ne_of_gt hx))
    exact (ENNReal.ofReal_le_ofReal_iff hr).mp
      ((distance_le_diameter d (mem_image_of_mem f hxs) (mem_image_of_mem f hvs)).trans (hmesh s))
  apply (D10Topology.Ch09.diameter_le_iff d _ _).mpr
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  apply ENNReal.ofReal_le_ofReal
  calc
    D10Topology.Ch09.distance d (f x) (f y) ≤
        D10Topology.Ch09.distance d (f x) (f (vertexPoint K v)) +
          D10Topology.Ch09.distance d (f (vertexPoint K v)) (f y) :=
      @dist_triangle X d (f x) (f (vertexPoint K v)) (f y)
    _ = D10Topology.Ch09.distance d (f x) (f (vertexPoint K v)) +
          D10Topology.Ch09.distance d (f y) (f (vertexPoint K v)) := by
      rw [D10Topology.Ch09.distance, @dist_comm X d (f (vertexPoint K v)) (f y)]
    _ ≤ 2 * r := by linarith [hdist x hx, hdist y hy]
theorem shrinkingMeshAndStars_of_simplex_mesh
    (hmesh : ∀ {V : Type u} (K : AbstractSimplicialComplex V), K.IsFinite →
      ∀ (d : MetricSpace K.Realization),
        D10Topology.Ch09.metricTopology d.toPseudoMetricSpace =
          (inferInstance : TopologicalSpace K.Realization) →
        ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n, N ≤ n →
          ∀ s : (K.Subdivision n).Simplex,
            D10Topology.Ch09.diameter d.toPseudoMetricSpace
              (K.iteratedSubdivisionMap n '' Set.range ((K.Subdivision n).simplexChart s)) <
              ENNReal.ofReal ε) :
    P202Specs.Topology.SimplicialApproximation.shrinkingMeshAndStars.{u} := by
  intro V K hK d hd ε hε
  have heps : 0 < ε / 3 := by linarith
  obtain ⟨N, hN⟩ := hmesh K hK d hd (ε / 3) heps
  refine ⟨N, fun n hn => ⟨?_, ?_⟩⟩
  · intro s
    exact (hN n hn s).trans
      ((ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith))
  · intro v
    apply lt_of_le_of_lt
      (openStar_image_diameter_le_two_mul (K.Subdivision n) d.toPseudoMetricSpace
        (K.iteratedSubdivisionMap n) (ε / 3) heps.le
        (fun s => (hN n hn s).le) v)
    exact (ENNReal.ofReal_lt_ofReal_iff hε).mpr (by linarith)

/-- Star refinement follows from shrinking mesh and the chosen-metric
Lebesgue-number adapter. -/
theorem starRefinement_of_shrinking
    (hmesh : P202Specs.Topology.SimplicialApproximation.shrinkingMeshAndStars.{u}) :
    P202Specs.Topology.SimplicialApproximation.starRefinement.{u,v} := by
  intro V W K L hK f
  obtain ⟨d, hd, ε, hε, hsmall⟩ := pullback_stars_lebesgue K L hK f
  obtain ⟨N, hN⟩ := hmesh K hK d hd ε hε
  refine ⟨N, fun n hn v => ?_⟩
  obtain ⟨w, hw⟩ := hsmall
    (K.iteratedSubdivisionMap n '' (K.Subdivision n).openStar v)
    ((openStar_nonempty _ v).image _) ((hN n hn).2 v)
  exact ⟨w, fun x hx => hw (mem_image_of_mem _ hx)⟩

theorem simplexChart_injective (K : AbstractSimplicialComplex V) (s : K.Simplex) :
    Function.Injective (K.simplexChart s) := by
  intro p q h
  apply Convexity.StdSimplex.ext
  apply Finsupp.mapDomain_injective Subtype.val_injective
  exact congrArg (fun x : K.Realization => x.1.weights) h

theorem realization_isClosed_iff (K : AbstractSimplicialComplex V) (A : Set K.Realization) :
    IsClosed A ↔ ∀ s : K.Simplex, IsClosed (K.simplexChart s ⁻¹' A) := by
  change IsClosed[⨆ s : K.Simplex,
    TopologicalSpace.coinduced (K.simplexChart s) inferInstance] A ↔ _
  simp only [isClosed_iSup_iff, isClosed_coinduced]

/-- A direct weak-simplex version of the compact-support argument. It does
not assume a CW instance on the realization. -/
theorem compact_realization_finite_vertices (L : AbstractSimplicialComplex W)
    (C : Set L.Realization) (hC : IsCompact C) :
    ∃ F : Finset W, ∀ x ∈ C, x.1.weights.support ⊆ F := by
  let S : Set W := {w | ∃ x ∈ C, w ∈ x.1.weights.support}
  have hS : S.Finite := by
    by_contra hS
    let v : ℕ ↪ S := Set.Infinite.natEmbedding S hS
    choose p hp hv using (fun n : ℕ => (v n).2)
    have hv_inj : Function.Injective (fun n : ℕ => (v n).1) :=
      Subtype.val_injective.comp v.injective
    have hclosed : ∀ Q : Set L.Realization, Q ⊆ range p → IsClosed Q := by
      intro Q hQ
      rw [realization_isClosed_iff]
      intro s
      let N : Set ℕ := {n | (v n).1 ∈ s.1}
      have hN : N.Finite := Set.Finite.preimage hv_inj.injOn s.1.finite_toSet
      have him : (p '' N).Finite := hN.image p
      have hpre : (L.simplexChart s ⁻¹' Q).Finite := by
        apply (Set.Finite.preimage (simplexChart_injective L s).injOn him).subset
        intro x hx
        obtain ⟨n, hn⟩ := hQ hx
        refine ⟨n, ?_, hn⟩
        have hsupport : (L.simplexChart s x).1.weights.support ⊆ s.1 := by
          intro w hw
          have hw' := Finsupp.mapDomain_support hw
          obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hw'
          exact z.2
        apply hsupport
        rw [← hn]
        exact hv n
      let : T2Space (L.GeometricSimplex s) :=
        (Convexity.StdSimplex.isEmbedding_toFun_comp_weights ℝ s.1).t2Space
      exact hpre.isClosed
    have hdisc : IsDiscrete (range p) := by
      rw [isDiscrete_iff_forall_mem_exists_isOpen]
      intro x hx
      refine ⟨(range p \ {x})ᶜ, (hclosed _ sdiff_subset).isOpen_compl, ?_⟩
      ext y
      simp only [mem_inter_iff, mem_compl_iff, mem_sdiff, mem_singleton_iff]
      constructor
      · rintro ⟨h, hy⟩
        by_contra hne
        exact h ⟨hy, hne⟩
      · rintro rfl
        exact ⟨fun h => h.2 rfl, hx⟩
    have hpfin : (range p).Finite :=
      (hC.of_isClosed_subset (hclosed _ Subset.rfl) (range_subset_iff.mpr hp)).finite hdisc
    have hbig : (⋃ x ∈ range p, (x.1.weights.support : Set W)).Finite :=
      hpfin.biUnion (fun x _ => x.1.weights.support.finite_toSet)
    have hvrange : (range (fun n : ℕ => (v n).1)).Finite := by
      apply hbig.subset
      rintro w ⟨n, rfl⟩
      exact mem_iUnion.mpr ⟨p n, mem_iUnion.mpr ⟨mem_range_self n, hv n⟩⟩
    exact Set.infinite_range_of_injective hv_inj hvrange
  refine ⟨hS.toFinset, fun x hx w hw => ?_⟩
  exact hS.mem_toFinset.mpr ⟨x, hx, hw⟩

private def restrictVertices (L : AbstractSimplicialComplex W) (F : Finset W) :
    AbstractSimplicialComplex W where
  simplices := {s | s ∈ L.simplices ∧ s ⊆ F}
  nonempty _ hs := L.nonempty _ hs.1
  face hs hts ht := ⟨L.face hs.1 hts ht, hts.trans hs.2⟩

private theorem restrictVertices_finite (L : AbstractSimplicialComplex W) (F : Finset W) :
    (restrictVertices L F).IsFinite :=
  F.powerset.finite_toSet.subset (fun _ hs => Finset.mem_powerset.mpr hs.2)

theorem inclusionRealization_continuous {K L : AbstractSimplicialComplex V}
    (h : K.simplices ⊆ L.simplices) : Continuous (inclusionRealization h) := by
  rw [realization_continuous_iff]
  intro s
  exact continuous_simplexChart L ⟨s.1, h s.2⟩

theorem finiteRealization_coordinateEmbedding (K : AbstractSimplicialComplex V)
    (hK : K.IsFinite) :
    IsEmbedding (fun x : K.Realization => (fun v : V => x.1.weights v)) := by
  let : CompactSpace K.Realization := ⟨finiteRealization_compact K hK⟩
  apply IsClosedEmbedding.isEmbedding
  apply Continuous.isClosedEmbedding
  · exact continuous_pi (continuous_realization_weight K)
  · intro p q h
    apply Subtype.ext
    ext v
    exact congrFun h v

private def interpolate (p q : Convexity.StdSimplex ℝ W) (t : Interval) :
    Convexity.StdSimplex ℝ W :=
  Convexity.convexCombPair (1 - (t : ℝ)) (t : ℝ)
    (sub_nonneg.mpr t.2.2) t.2.1 (by ring) p q

private theorem interpolate_support (p q : Convexity.StdSimplex ℝ W) (t : Interval)
    (h : q.weights.support ⊆ p.weights.support) :
    (interpolate p q t).weights.support ⊆ p.weights.support := by
  rw [interpolate, Convexity.StdSimplex.weights_convexCombPair]
  exact Finsupp.support_add.trans (Finset.union_subset
    Finsupp.support_smul (Finsupp.support_smul.trans h))

theorem star_homotopy (K : AbstractSimplicialComplex V)
    (L : AbstractSimplicialComplex W) (hK : K.IsFinite)
    (f : C(K.Realization, L.Realization)) (g : SimplicialMap K L)
    (hstar : ∀ v x, x ∈ K.openStar v → 0 < (f x).1.weights (g.vertex v)) :
    ∃ H : C(K.Realization × Interval, L.Realization),
      (∀ x, H (x, 0) = f x) ∧ (∀ x, H (x, 1) = g.realization x) ∧
      ∀ x t w, (H (x, t)).1.weights w =
        (1 - (t : ℝ)) * (f x).1.weights w + (t : ℝ) * (g.realization x).1.weights w := by
  have hsupp (x : K.Realization) :
      (g.realization x).1.weights.support ⊆ (f x).1.weights.support := by
    intro w hw
    rw [SimplicialMap.realization, Convexity.StdSimplex.weights_map,
      Finsupp.support_mapDomain_of_nonneg (K.activeCoordinates x).nonneg] at hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    have hvne : x.1.weights v.1 ≠ 0 := by
      simpa only [activeCoordinates, Finsupp.subtypeDomain_apply] using
        (Finsupp.mem_support_iff.mp hv)
    exact Finsupp.mem_support_iff.mpr
      (hstar v x (lt_of_le_of_ne (x.1.weights_nonneg v.1) hvne.symm)).ne'
  let : CompactSpace K.Realization := ⟨finiteRealization_compact K hK⟩
  obtain ⟨F, hF⟩ := compact_realization_finite_vertices L (range f) (isCompact_range f.continuous)
  let J := restrictVertices L F
  let H₀ : K.Realization × Interval → J.Realization := fun z =>
    ⟨interpolate (f z.1).1 (g.realization z.1).1 z.2, by
      have hsub := interpolate_support (f z.1).1 (g.realization z.1).1 z.2 (hsupp z.1)
      exact ⟨L.face (f z.1).2 hsub (Convexity.StdSimplex.support_weights_nonempty _),
        hsub.trans (hF (f z.1) (mem_range_self z.1))⟩⟩
  have hH₀ : Continuous H₀ := by
    apply (finiteRealization_coordinateEmbedding J (restrictVertices_finite L F)).continuous_iff.mpr
    apply continuous_pi
    intro w
    change Continuous (fun z : K.Realization × Interval =>
      (interpolate (f z.1).1 (g.realization z.1).1 z.2).weights w)
    simp only [interpolate, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
    exact ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).mul
      ((continuous_realization_weight L w).comp (f.continuous.comp continuous_fst))).add
      ((continuous_subtype_val.comp continuous_snd).mul
        ((continuous_realization_weight L w).comp ((simplicialMap_continuous g).comp continuous_fst)))
  have hi : J.simplices ⊆ L.simplices := fun _ hs => hs.1
  let incl : J.Realization → L.Realization := inclusionRealization hi
  let H : C(K.Realization × Interval, L.Realization) :=
    ⟨incl ∘ H₀, (inclusionRealization_continuous hi).comp hH₀⟩
  refine ⟨H, ?_, ?_, ?_⟩
  · intro x
    apply Subtype.ext
    change interpolate (f x).1 (g.realization x).1 0 = (f x).1
    simp [interpolate]
  · intro x
    apply Subtype.ext
    change interpolate (f x).1 (g.realization x).1 1 = (g.realization x).1
    simp [interpolate]
  · intro x t w
    change (interpolate (f x).1 (g.realization x).1 t).weights w = _
    simp only [interpolate, Convexity.StdSimplex.weights_convexCombPair,
      Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]

/-- A continuous bijective barycentric map is the canonical homeomorphism. -/
theorem subdivision_homeomorphism_of_bijective {V : Type u}
    (K : AbstractSimplicialComplex V) (hK : K.IsFinite)
    (hbij : Function.Bijective K.subdivisionMap) :
    ∃ h : K.barycentricSubdivision.Realization ≃ₜ K.Realization,
      (h : K.barycentricSubdivision.Realization → K.Realization) = K.subdivisionMap := by
  let : CompactSpace K.barycentricSubdivision.Realization :=
    ⟨finiteRealization_compact _ (finite_subdivision K hK)⟩
  let : T2Space K.Realization := (finiteRealization_coordinateEmbedding K hK).t2Space
  let e : K.barycentricSubdivision.Realization ≃ K.Realization :=
    Equiv.ofBijective K.subdivisionMap hbij
  exact ⟨(show Continuous e from subdivisionMap_continuous K).homeoOfEquivCompactToT2, rfl⟩

theorem iterated_subdivision_homeomorphism_of_bijective
    (hb : ∀ {V : Type u} (K : AbstractSimplicialComplex V), K.IsFinite →
      Function.Bijective K.subdivisionMap) :
    P202Specs.Topology.SimplicialApproximation.subdivisionHomeomorphism.{u} := by
  intro V K hK n
  induction n with
  | zero => exact ⟨Homeomorph.refl _, rfl⟩
  | succ n ih =>
    obtain ⟨h, hh⟩ := ih
    obtain ⟨e, he⟩ := subdivision_homeomorphism_of_bijective
      (K.Subdivision n) (finite_iteratedSubdivision K hK n)
      (hb _ (finite_iteratedSubdivision K hK n))
    refine ⟨e.trans h, ?_⟩
    change (h : _ → _) ∘ (e : _ → _) = K.iteratedSubdivisionMap (n + 1)
    rw [hh, he]
    rfl

/-- The unnormalized linear evaluation underlying the canonical barycentric map. -/
def barycentricEvalWeights (K : AbstractSimplicialComplex V) (w : K.Simplex →₀ ℝ) : V →₀ ℝ :=
  w.sum (fun s r => r • (K.simplexBarycenter s).weights)

theorem simplexBarycenter_weight_of_mem (K : AbstractSimplicialComplex V)
    (s : K.Simplex) {v : V} (hv : v ∈ s.1) :
    (K.simplexBarycenter s).weights v = (s.1.card : ℝ)⁻¹ := by
  simp only [simplexBarycenter, Convexity.StdSimplex.weights_subBarycenter,
    Finsupp.coe_finsetSum, Finset.sum_apply]
  rw [Finset.sum_eq_single v]
  · simp
  · intro b hb hne
    exact Finsupp.single_eq_of_ne hne.symm
  · exact fun h => (h hv).elim

theorem barycentricEvalWeights_apply (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (v : V) :
    barycentricEvalWeights K w v =
      ∑ s ∈ w.support, w s * (K.simplexBarycenter s).weights v := by
  simp [barycentricEvalWeights, Finsupp.sum, Finsupp.coe_finsetSum, Finset.sum_apply]

theorem barycentricEvalWeights_nonneg (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (hw : ∀ s, 0 ≤ w s) (v : V) :
    0 ≤ barycentricEvalWeights K w v := by
  rw [barycentricEvalWeights_apply]
  exact Finset.sum_nonneg fun s hs => mul_nonneg (hw s) ((K.simplexBarycenter s).nonneg v)

theorem chain_has_top_only_vertex (K : AbstractSimplicialComplex V)
    {c : Finset K.Simplex} (hc : c ∈ K.barycentricSubdivision.simplices)
    {s : K.Simplex} (_hs : s ∈ c) (hmax : ∀ t ∈ c, t.1 ⊆ s.1) :
    ∃ v ∈ s.1, ∀ t ∈ c, t ≠ s → v ∉ t.1 := by
  by_cases he : (c.erase s).Nonempty
  · obtain ⟨t, ht, htop⟩ := chain_has_largest
      (K.barycentricSubdivision.face hc (Finset.erase_subset s c) he)
    have ht' : t ∈ c := (Finset.mem_erase.mp ht).2
    have hts : t.1 ≠ s.1 := fun h => (Finset.mem_erase.mp ht).1 (Subtype.ext h)
    obtain ⟨v, hvs, hvt⟩ := Finset.exists_of_ssubset
      (Finset.ssubset_iff_subset_ne.mpr ⟨hmax t ht', hts⟩)
    refine ⟨v, hvs, fun r hr hrs hvr => hvt ?_⟩
    exact htop r (Finset.mem_erase.mpr ⟨hrs, hr⟩) hvr
  · obtain ⟨v, hv⟩ := K.nonempty _ s.2
    refine ⟨v, hv, fun t ht hts => ?_⟩
    exact (he ⟨t, Finset.mem_erase.mpr ⟨hts, ht⟩⟩).elim

theorem barycentricEvalWeights_support (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (hw : ∀ s, 0 ≤ w s)
    (_hc : w.support ∈ K.barycentricSubdivision.simplices)
    {s : K.Simplex} (hs : s ∈ w.support)
    (hmax : ∀ t ∈ w.support, t.1 ⊆ s.1) :
    (barycentricEvalWeights K w).support = s.1 := by
  ext v
  constructor
  · intro hv
    by_contra hvs
    apply Finsupp.mem_support_iff.mp hv
    rw [barycentricEvalWeights_apply]
    apply Finset.sum_eq_zero
    intro t ht
    dsimp only [simplexBarycenter]
    rw [Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero t.1
      (K.nonempty _ t.2) v (fun h => hvs (hmax t ht h)), mul_zero]
  · intro hvs
    apply Finsupp.mem_support_iff.mpr
    have hwpos : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm (Finsupp.mem_support_iff.mp hs))
    have hbpos : 0 < (K.simplexBarycenter s).weights v := by
      rw [simplexBarycenter_weight_of_mem K s hvs]
      exact inv_pos.mpr (by exact_mod_cast (K.nonempty _ s.2).card_pos)
    have hle : w s * (K.simplexBarycenter s).weights v ≤ barycentricEvalWeights K w v := by
      rw [barycentricEvalWeights_apply]
      exact Finset.single_le_sum
        (fun t ht => mul_nonneg (hw t) ((K.simplexBarycenter t).nonneg v)) hs
    exact ne_of_gt (lt_of_lt_of_le (mul_pos hwpos hbpos) hle)

theorem barycentricEvalWeights_top_minimum (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (hw : ∀ s, 0 ≤ w s)
    (hc : w.support ∈ K.barycentricSubdivision.simplices)
    {s : K.Simplex} (hs : s ∈ w.support)
    (hmax : ∀ t ∈ w.support, t.1 ⊆ s.1) :
    (∀ v ∈ s.1, w s / s.1.card ≤ barycentricEvalWeights K w v) ∧
      ∃ v ∈ s.1, barycentricEvalWeights K w v = w s / s.1.card := by
  constructor
  · intro v hv
    rw [div_eq_mul_inv, ← simplexBarycenter_weight_of_mem K s hv,
      barycentricEvalWeights_apply]
    exact Finset.single_le_sum
      (fun t ht => mul_nonneg (hw t) ((K.simplexBarycenter t).nonneg v)) hs
  · obtain ⟨v, hv, hvo⟩ := chain_has_top_only_vertex K hc hs hmax
    refine ⟨v, hv, ?_⟩
    rw [barycentricEvalWeights_apply, Finset.sum_eq_single s]
    · rw [simplexBarycenter_weight_of_mem K s hv, div_eq_mul_inv]
    · intro t ht hts
      dsimp only [simplexBarycenter]
      rw [Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero t.1
        (K.nonempty _ t.2) v (hvo t ht hts), mul_zero]
    · exact fun h => (h hs).elim

@[simp] theorem barycentricEvalWeights_zero (K : AbstractSimplicialComplex V) :
    barycentricEvalWeights K 0 = 0 := by simp [barycentricEvalWeights]

theorem barycentricEvalWeights_add (K : AbstractSimplicialComplex V)
    (w z : K.Simplex →₀ ℝ) :
    barycentricEvalWeights K (w + z) =
      barycentricEvalWeights K w + barycentricEvalWeights K z := by
  exact Finsupp.sum_add_index (fun s hs => zero_smul _ _)
    (fun s hs a b => add_smul a b _)

@[simp] theorem barycentricEvalWeights_single (K : AbstractSimplicialComplex V)
    (s : K.Simplex) (r : ℝ) :
    barycentricEvalWeights K (Finsupp.single s r) = r • (K.simplexBarycenter s).weights := by
  exact Finsupp.sum_single_index (zero_smul _ _)

theorem barycentricEvalWeights_erase (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (s : K.Simplex) :
    barycentricEvalWeights K (w.erase s) =
      barycentricEvalWeights K w - w s • (K.simplexBarycenter s).weights := by
  apply eq_sub_iff_add_eq.mpr
  rw [← barycentricEvalWeights_single, ← barycentricEvalWeights_add,
    Finsupp.erase_add_single]

theorem barycentricEvalWeights_eq_zero (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) (hw : ∀ s, 0 ≤ w s)
    (he : barycentricEvalWeights K w = 0) : w = 0 := by
  ext s
  by_contra hn
  have hs : s ∈ w.support := Finsupp.mem_support_iff.mpr hn
  have hwpos : 0 < w s := lt_of_le_of_ne (hw s) (Ne.symm hn)
  obtain ⟨v, hv⟩ := K.nonempty _ s.2
  have hbpos : 0 < (K.simplexBarycenter s).weights v := by
    rw [simplexBarycenter_weight_of_mem K s hv]
    exact inv_pos.mpr (by exact_mod_cast (K.nonempty _ s.2).card_pos)
  have hle : w s * (K.simplexBarycenter s).weights v ≤ barycentricEvalWeights K w v := by
    rw [barycentricEvalWeights_apply]
    exact Finset.single_le_sum
      (fun t ht => mul_nonneg (hw t) ((K.simplexBarycenter t).nonneg v)) hs
  have : 0 < barycentricEvalWeights K w v := lt_of_lt_of_le (mul_pos hwpos hbpos) hle
  simp [he] at this

theorem barycentricEvalWeights_injective_chains (K : AbstractSimplicialComplex V)
    (w z : K.Simplex →₀ ℝ) (hw : ∀ s, 0 ≤ w s) (hz : ∀ s, 0 ≤ z s)
    (hcw : ∀ s ∈ w.support, ∀ t ∈ w.support, s.1 ⊆ t.1 ∨ t.1 ⊆ s.1)
    (hcz : ∀ s ∈ z.support, ∀ t ∈ z.support, s.1 ⊆ t.1 ∨ t.1 ⊆ s.1)
    (he : barycentricEvalWeights K w = barycentricEvalWeights K z) : w = z := by
  generalize hn : w.support.card = n
  induction n using Nat.strong_induction_on generalizing w z with
  | h n ih =>
    by_cases hw0 : w = 0
    · subst w
      exact (barycentricEvalWeights_eq_zero K z hz (by simpa using he.symm)).symm
    have hwne : w.support.Nonempty := Finsupp.support_nonempty_iff.mpr hw0
    have hz0 : z ≠ 0 := by
      intro hz0
      exact hw0 (barycentricEvalWeights_eq_zero K w hw (by simpa [hz0] using he))
    have hzne : z.support.Nonempty := Finsupp.support_nonempty_iff.mpr hz0
    obtain ⟨s, hs, htop⟩ := chain_has_largest (K := K) ⟨hwne, hcw⟩
    obtain ⟨t, ht, htop'⟩ := chain_has_largest (K := K) ⟨hzne, hcz⟩
    have hst : s = t := by
      apply Subtype.ext
      rw [← barycentricEvalWeights_support K w hw ⟨hwne, hcw⟩ hs htop,
        ← barycentricEvalWeights_support K z hz ⟨hzne, hcz⟩ ht htop', he]
    subst t
    have hwmin := barycentricEvalWeights_top_minimum K w hw ⟨hwne, hcw⟩ hs htop
    have hzmin := barycentricEvalWeights_top_minimum K z hz ⟨hzne, hcz⟩ ht htop'
    have hws : w s = z s := by
      apply (div_left_inj' (by exact_mod_cast (K.nonempty _ s.2).card_pos.ne') :
        w s / (s.1.card : ℝ) = z s / s.1.card ↔ w s = z s).mp
      apply le_antisymm
      · obtain ⟨v, hv, heq⟩ := hzmin.2
        rw [← heq, ← he]
        exact hwmin.1 v hv
      · obtain ⟨v, hv, heq⟩ := hwmin.2
        rw [← heq, he]
        exact hzmin.1 v hv
    have herase : w.erase s = z.erase s := by
      have hlt : (w.erase s).support.card < n := by
        simpa [Finsupp.support_erase, ← hn] using Finset.card_erase_lt_of_mem hs
      apply ih (w.erase s).support.card hlt (w.erase s) (z.erase s)
      · intro t; simp only [Finsupp.erase_apply]; split_ifs; exact le_rfl; exact hw t
      · intro t; simp only [Finsupp.erase_apply]; split_ifs; exact le_rfl; exact hz t
      · intro a ha b hb
        exact hcw a (Finset.mem_of_mem_erase (by simpa using ha)) b
          (Finset.mem_of_mem_erase (by simpa using hb))
      · intro a ha b hb
        exact hcz a (Finset.mem_of_mem_erase (by simpa using ha)) b
          (Finset.mem_of_mem_erase (by simpa using hb))
      · rw [barycentricEvalWeights_erase, barycentricEvalWeights_erase, he, hws]
      · rfl
    calc
      w = Finsupp.single s (w s) + w.erase s := (Finsupp.single_add_erase s w).symm
      _ = Finsupp.single s (z s) + z.erase s := by rw [hws, herase]
      _ = z := Finsupp.single_add_erase s z

theorem subdivisionMap_weights_linear (K : AbstractSimplicialComplex V)
    (p : K.barycentricSubdivision.Realization) :
    (K.subdivisionMap p).1.weights = barycentricEvalWeights K p.1.weights := by
  change ((p.1.map K.simplexBarycenter).weights.sum
    (fun d r => r • d.weights)) = _
  rw [Convexity.StdSimplex.weights_map,
    Finsupp.sum_mapDomain_index
      (h := fun (d : Convexity.StdSimplex ℝ V) (r : ℝ) => r • d.weights)
      (fun d => zero_smul ℝ d.weights) (fun d r s => add_smul r s d.weights)]
  rfl

theorem subdivisionMap_injective (K : AbstractSimplicialComplex V) :
    Function.Injective K.subdivisionMap := by
  intro p q he
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  apply barycentricEvalWeights_injective_chains K p.1.weights q.1.weights
    p.1.nonneg q.1.nonneg p.2.2 q.2.2
  rw [← subdivisionMap_weights_linear, ← subdivisionMap_weights_linear, he]

theorem barycentricEvalWeights_surjective (K : AbstractSimplicialComplex V)
    (f : V →₀ ℝ) (hf : ∀ v, 0 ≤ f v) (T : K.Simplex)
    (hT : f.support ⊆ T.1) :
    ∃ w : K.Simplex →₀ ℝ,
      (∀ s, 0 ≤ w s) ∧
      (∀ s ∈ w.support, ∀ t ∈ w.support, s.1 ⊆ t.1 ∨ t.1 ⊆ s.1) ∧
      barycentricEvalWeights K w = f ∧
      (∀ s ∈ w.support, s.1 ⊆ f.support) := by
  generalize hn : f.support.card = n
  induction n using Nat.strong_induction_on generalizing f with
  | h n ih =>
    by_cases hf0 : f = 0
    · subst f
      exact ⟨0, by simp, by simp, by simp, by simp⟩
    have hfn : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hf0
    let s : K.Simplex := ⟨f.support, K.face T.2 hT hfn⟩
    obtain ⟨v₀, hv₀, hmin⟩ := f.support.exists_min_image (fun v => f v) hfn
    let m : ℝ := f v₀
    have hm : 0 < m := lt_of_le_of_ne (hf v₀) (Ne.symm (Finsupp.mem_support_iff.mp hv₀))
    have hcard : (s.1.card : ℝ) ≠ 0 := by exact_mod_cast hfn.card_pos.ne'
    let a : ℝ := m * s.1.card
    have ha : 0 ≤ a := mul_nonneg hm.le (Nat.cast_nonneg _)
    have hscale : a * (s.1.card : ℝ)⁻¹ = m := by
      dsimp only [a]
      rw [mul_assoc, mul_inv_cancel₀ hcard, mul_one]
    let r : V →₀ ℝ := f - a • (K.simplexBarycenter s).weights
    have hr_apply (v : V) : r v = if v ∈ f.support then f v - m else 0 := by
      dsimp only [r]
      simp only [Finsupp.sub_apply, Finsupp.smul_apply, smul_eq_mul]
      by_cases hv : v ∈ f.support
      · rw [simplexBarycenter_weight_of_mem K s hv, hscale, if_pos hv]
      · rw [show (K.simplexBarycenter s).weights v = 0 from
          Convexity.StdSimplex.subBarycenter_weights_apply_eq_zero s.1
            (K.nonempty _ s.2) v hv, Finsupp.notMem_support_iff.mp hv]
        simp [hv]
    have hr : ∀ v, 0 ≤ r v := by
      intro v
      rw [hr_apply]
      split_ifs with hv
      · exact sub_nonneg.mpr (hmin v hv)
      · exact le_rfl
    have hrs : r.support ⊆ f.support := by
      intro v hv
      by_contra hv'
      exact Finsupp.mem_support_iff.mp hv (by simp [hr_apply, hv'])
    have hrv : v₀ ∉ r.support := by simp [Finsupp.mem_support_iff, hr_apply, hv₀, m]
    have hrlt : r.support.card < n := by
      rw [← hn]
      apply Finset.card_lt_card
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hrs, fun heq => hrv (heq.symm ▸ hv₀)⟩
    obtain ⟨w, hw, hcw, hew, hws⟩ := ih r.support.card hrlt r hr (hrs.trans hT) rfl
    refine ⟨w + Finsupp.single s a, ?_, ?_, ?_, ?_⟩
    · intro t
      exact add_nonneg (hw t) (by by_cases ht : t = s <;> simp [ht, ha])
    · intro t ht u hu
      have ht' := Finsupp.support_add ht
      have hu' := Finsupp.support_add hu
      rcases Finset.mem_union.mp ht' with ht | ht
      · rcases Finset.mem_union.mp hu' with hu | hu
        · exact hcw t ht u hu
        · have hu : u = s := Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
          subst u
          exact Or.inl ((hws t ht).trans hrs)
      · have ht : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
        subst t
        rcases Finset.mem_union.mp hu' with hu | hu
        · exact Or.inr ((hws u hu).trans hrs)
        · have hu : u = s := Finset.mem_singleton.mp (Finsupp.support_single_subset hu)
          subst u
          exact Or.inl Finset.Subset.rfl
    · rw [barycentricEvalWeights_add, barycentricEvalWeights_single, hew]
      exact sub_add_cancel _ _
    · intro t ht
      rcases Finset.mem_union.mp (Finsupp.support_add ht) with ht | ht
      · exact (hws t ht).trans hrs
      · have ht : t = s := Finset.mem_singleton.mp (Finsupp.support_single_subset ht)
        subst t
        exact Finset.Subset.rfl

theorem barycentricEvalWeights_total (K : AbstractSimplicialComplex V)
    (w : K.Simplex →₀ ℝ) :
    (barycentricEvalWeights K w).sum (fun _ r => r) = w.sum (fun _ r => r) := by
  unfold barycentricEvalWeights
  rw [Finsupp.sum_sum_index (by simp) (by simp)]
  apply Finsupp.sum_congr
  intro s hs
  rw [Finsupp.sum_smul_index (by simp), ← Finsupp.mul_sum,
    (K.simplexBarycenter s).total, mul_one]

theorem subdivisionMap_surjective (K : AbstractSimplicialComplex V) :
    Function.Surjective K.subdivisionMap := by
  intro p
  obtain ⟨w, hw, hcw, he, hws⟩ := barycentricEvalWeights_surjective K p.1.weights p.1.nonneg
    ⟨p.1.weights.support, p.2⟩ Finset.Subset.rfl
  have htotal : w.sum (fun _ r => r) = 1 := by
    rw [← barycentricEvalWeights_total K w, he]
    exact p.1.total
  let q : Convexity.StdSimplex ℝ K.Simplex := ⟨w, hw, htotal⟩
  have hqn : q.weights.support.Nonempty := q.support_weights_nonempty
  refine ⟨⟨q, hqn, hcw⟩, ?_⟩
  apply Subtype.ext
  apply Convexity.StdSimplex.ext
  exact (subdivisionMap_weights_linear K _).trans he

theorem subdivisionHomeomorphism_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.subdivisionHomeomorphism.{u} := by
  apply iterated_subdivision_homeomorphism_of_bijective
  intro V K _hK
  exact ⟨subdivisionMap_injective K, subdivisionMap_surjective K⟩

/-- Assemble finite-source approximation from canonical subdivision
homeomorphisms and the shrinking-mesh interface. -/
theorem approximation_of_subdivision_and_shrinking
    (hhome : P202Specs.Topology.SimplicialApproximation.subdivisionHomeomorphism.{u})
    (hmesh : P202Specs.Topology.SimplicialApproximation.shrinkingMeshAndStars.{u}) :
    P202Specs.Topology.SimplicialApproximation.finiteSourceSimplicialApproximation.{u,v} := by
  intro V W K L hK f
  obtain ⟨N, hN⟩ := starRefinement_of_shrinking hmesh K L hK f
  refine ⟨N, fun n hn => ?_⟩
  obtain ⟨h, hh⟩ := hhome K hK n
  choose w hw using hN n hn
  let a : (K.Subdivision n).Vertex → W := fun v => (w v).1
  let f' : C((K.Subdivision n).Realization, L.Realization) :=
    f.comp ⟨h, h.continuous_toFun⟩
  have ha : ∀ v x, x ∈ (K.Subdivision n).openStar v → 0 < (f' x).1.weights (a v) := by
    intro v x hx
    change 0 < (f (h x)).1.weights (w v).1
    rw [hh]
    exact hw v hx
  obtain ⟨g, hg, _⟩ := starCriterion_map (K.Subdivision n) L f' a ha
  have hgstar : ∀ v x, x ∈ (K.Subdivision n).openStar v →
      0 < (f' x).1.weights (g.vertex v) := by
    rw [hg]
    exact ha
  obtain ⟨H, h0, h1, _⟩ := star_homotopy (K.Subdivision n) L
    (finite_iteratedSubdivision K hK n) f' g hgstar
  exact ⟨g, h, H, hh, h0, h1⟩

end P202.Topology

namespace P202.Topology
open P202.Cellular P202.Cellular.AbstractSimplicialComplex

theorem simplicialMapContinuous_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.simplicialMapContinuous.{u,v} := by
  intro V W K L g
  exact simplicialMap_continuous g

theorem openStars_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.openStars.{u} := by
  intro V K
  exact ⟨openStar_isOpen K, openStars_cover K⟩

theorem starCriterion_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.starCriterion.{u,v} := by
  intro V W K L f a ha
  exact starCriterion_map K L f a ha

theorem subdivisionFaceCompatibility_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.subdivisionFaceCompatibility.{u} := by
  intro V K L h x
  exact subdivision_face_compatibility h x

theorem finiteMetricRealization_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.finiteMetricRealization.{u} := by
  intro V K hK
  exact finite_realization_metric K hK

theorem starHomotopy_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.starHomotopy.{u,v} := by
  intro V W K L hK f g hstar
  exact star_homotopy K L hK f g hstar

theorem shrinkingMeshAndStars_conditional
    (_premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (_premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (_premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (_premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (_premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (_premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (_premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (_premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.shrinkingMeshAndStars.{u} := by
  apply shrinkingMeshAndStars_of_simplex_mesh
  intro V K hK d hd
  exact subdivision_simplex_mesh_tends_zero K hK d hd

theorem starRefinement_conditional
    (premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.starRefinement.{u,v} := by
  exact starRefinement_of_shrinking (shrinkingMeshAndStars_conditional premise1 premise2 premise3 premise4 premise5 premise6 premise7 premise8)

theorem finiteSourceSimplicialApproximation_conditional
    (premise1 : P202Specs.Topology.CellTopology.compactContainedInFiniteSubcomplex.{u})
    (premise2 : P202Specs.Topology.CellTopology.compactImageFiniteSupport.{u,v})
    (premise3 : P202Specs.Topology.CellTopology.finiteCompactImagesFiniteSupport.{u,v})
    (premise4 : P202Specs.Topology.CellTopology.finiteSingularSimplexSupport.{u})
    (premise5 : P202Specs.Topology.CellTopology.intervalHomotopyFiniteSupport.{u})
    (premise6 : P202Specs.Topology.CellTopology.intervalMapFiniteSupport.{u})
    (premise7 : P202Specs.Topology.CellTopology.subcomplexClosed.{u})
    (premise8 : P202Specs.Topology.CellTopology.subcomplexWeakTopology.{u})
    : P202Specs.Topology.SimplicialApproximation.finiteSourceSimplicialApproximation.{u,v} := by
  exact approximation_of_subdivision_and_shrinking
    (subdivisionHomeomorphism_conditional premise1 premise2 premise3 premise4 premise5 premise6 premise7 premise8)
    (shrinkingMeshAndStars_conditional premise1 premise2 premise3 premise4 premise5 premise6 premise7 premise8)

end P202.Topology

universe v8_closure_d825aa67da8f841a_u0 v8_closure_d825aa67da8f841a_u1
theorem _root_.«P202».«Topology».«finiteMetricRealization» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«finiteMetricRealization».{v8_closure_d825aa67da8f841a_u0} :=
  @_root_.«P202».«Topology».«finiteMetricRealization_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«finiteSourceSimplicialApproximation» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«finiteSourceSimplicialApproximation».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} :=
  @_root_.«P202».«Topology».«finiteSourceSimplicialApproximation_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«openStars» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«openStars».{v8_closure_d825aa67da8f841a_u0} :=
  @_root_.«P202».«Topology».«openStars_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«shrinkingMeshAndStars» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«shrinkingMeshAndStars».{v8_closure_d825aa67da8f841a_u0} :=
  @_root_.«P202».«Topology».«shrinkingMeshAndStars_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«simplicialMapContinuous» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«simplicialMapContinuous».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} :=
  @_root_.«P202».«Topology».«simplicialMapContinuous_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«starCriterion» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«starCriterion».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} :=
  @_root_.«P202».«Topology».«starCriterion_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«starHomotopy» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«starHomotopy».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} :=
  @_root_.«P202».«Topology».«starHomotopy_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«starRefinement» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«starRefinement».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} :=
  @_root_.«P202».«Topology».«starRefinement_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u1}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«subdivisionFaceCompatibility» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«subdivisionFaceCompatibility».{v8_closure_d825aa67da8f841a_u0} :=
  @_root_.«P202».«Topology».«subdivisionFaceCompatibility_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
theorem _root_.«P202».«Topology».«subdivisionHomeomorphism» : _root_.«P202Specs».«Topology».«SimplicialApproximation».«subdivisionHomeomorphism».{v8_closure_d825aa67da8f841a_u0} :=
  @_root_.«P202».«Topology».«subdivisionHomeomorphism_conditional».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0} (@_root_.«P202».«Topology».«compactContainedInFiniteSubcomplex».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«compactImageFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteCompactImagesFiniteSupport».{v8_closure_d825aa67da8f841a_u0, v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«finiteSingularSimplexSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalHomotopyFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«intervalMapFiniteSupport».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexClosed».{v8_closure_d825aa67da8f841a_u0}) (@_root_.«P202».«Topology».«subcomplexWeakTopology».{v8_closure_d825aa67da8f841a_u0})
