import MathGenome.Internal.FunctionalAnalysis.Specs.ExpandedFA.Supplements.NetTests

open Set Filter Topology

universe u v w

namespace ExpandedFA.NetTests

/-- A filter represented by a directed net: a set in the filter, together
with a point of that set, ordered by reverse inclusion of the sets. -/
def FilterIndex {X : Type u} (F : Filter X) :=
  {p : Set X × X // p.1 ∈ F ∧ p.2 ∈ p.1}

instance {X : Type u} (F : Filter X) : Preorder (FilterIndex F) where
  le p q := q.val.1 ⊆ p.val.1
  le_refl _ := Subset.rfl
  le_trans _ _ _ hpq hqr := hqr.trans hpq

instance {X : Type u} (F : Filter X) [NeBot F] : Nonempty (FilterIndex F) := by
  obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (univ_mem : (univ : Set X) ∈ F)
  exact ⟨⟨(univ, x), univ_mem, hx⟩⟩

instance {X : Type u} (F : Filter X) [NeBot F] : IsDirectedOrder (FilterIndex F) where
  directed p q := by
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem (inter_mem p.property.1 q.property.1)
    exact ⟨⟨(p.val.1 ∩ q.val.1, x), inter_mem p.property.1 q.property.1, hx⟩,
      inter_subset_left, inter_subset_right⟩

/-- The point net has precisely the original filter as its image filter. -/
theorem map_filterIndex {X : Type u} (F : Filter X) [NeBot F] :
    map (fun p : FilterIndex F => p.val.2) atTop = F := by
  apply le_antisymm
  · intro s hs
    obtain ⟨x, hx⟩ := Filter.nonempty_of_mem hs
    exact eventually_atTop.2 ⟨⟨(s, x), hs, hx⟩, fun p hp => hp p.property.2⟩
  · intro s hs
    obtain ⟨p, hp⟩ := eventually_atTop.1 hs
    apply mem_of_superset p.property.1
    intro x hx
    exact hp ⟨(p.val.1, x), p.property.1, hx⟩ Subset.rfl

/-- Closed sets contain limits of nets, for arbitrary index universes. -/
theorem closed_net_limit {X : Type u} [TopologicalSpace X] {s : Set X}
    (hs : IsClosed s) {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {a : ι → X} {x : X} (ha : ∀ i, a i ∈ s) (hx : Tendsto a atTop (𝓝 x)) : x ∈ s :=
  hs.mem_of_tendsto hx (Eventually.of_forall ha)

theorem closedCriterion : Specs.ExpandedFA.NetTests.closedCriterion.{u} := by
  intro X _ s
  constructor
  · intro hs ι _ _ _ a x ha hx
    exact closed_net_limit hs ha hx
  · intro h
    apply isClosed_iff_clusterPt.2
    intro x hx
    let F := comap ((↑) : s → X) (𝓝 x)
    have : NeBot F := mem_closure_iff_comap_neBot.1 hx.mem_closure
    have ha : Tendsto (fun p : FilterIndex F => (p.val.2 : X)) atTop (𝓝 x) := by
      change map (((↑) : s → X) ∘ (fun p : FilterIndex F => p.val.2)) atTop ≤ _
      rw [← map_map, map_filterIndex]
      exact map_comap_le
    exact h (FilterIndex F) (fun p => (p.val.2 : X)) x
      (fun p => p.val.2.property) ha

theorem continuousCriterion : Specs.ExpandedFA.NetTests.continuousCriterion.{u,v} := by
  intro X Y _ _ f
  constructor
  · intro hf ι _ _ _ a x hx
    exact (hf.tendsto x).comp hx
  · intro h
    apply continuous_iff_continuousAt.2
    intro x
    have hx : Tendsto (fun p : FilterIndex (𝓝 x) => p.val.2) atTop (𝓝 x) := by
      change map _ _ ≤ _
      rw [map_filterIndex]
    have hf := h (FilterIndex (𝓝 x)) (fun p => p.val.2) x hx
    change map _ _ ≤ _ at hf ⊢
    rw [← map_map, map_filterIndex] at hf
    exact hf

/-- Indices selecting a term in a neighborhood of a cluster point. Both the
original index and reverse neighborhood inclusion occur in the order. -/
def SubnetIndex {X : Type u} [TopologicalSpace X] {ι : Type v}
    (a : ι → X) (x : X) :=
  {p : ι × Set X // p.2 ∈ 𝓝 x ∧ a p.1 ∈ p.2}

instance {X : Type u} [TopologicalSpace X] {ι : Type v} [Preorder ι]
    (a : ι → X) (x : X) : Preorder (SubnetIndex a x) where
  le p q := p.val.1 ≤ q.val.1 ∧ q.val.2 ⊆ p.val.2
  le_refl _ := ⟨le_rfl, Subset.rfl⟩
  le_trans _ _ _ hpq hqr := ⟨hpq.1.trans hqr.1, hqr.2.trans hpq.2⟩

instance {X : Type u} [TopologicalSpace X] {ι : Type v} [Nonempty ι]
    (a : ι → X) (x : X) : Nonempty (SubnetIndex a x) := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  exact ⟨⟨(i, univ), univ_mem, mem_univ _⟩⟩

theorem subnetIndex_directed {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {a : ι → X} {x : X} (hx : MapClusterPt x atTop a) :
    IsDirectedOrder (SubnetIndex a x) where
  directed p q := by
    obtain ⟨i, hpi, hqi⟩ := exists_ge_ge p.val.1 q.val.1
    have hf := mapClusterPt_iff_frequently.1 hx _ (inter_mem p.property.1 q.property.1)
    obtain ⟨j, hij, hj⟩ := frequently_atTop.1 hf i
    exact ⟨⟨(j, p.val.2 ∩ q.val.2), inter_mem p.property.1 q.property.1, hj⟩,
      ⟨hpi.trans hij, inter_subset_left⟩, ⟨hqi.trans hij, inter_subset_right⟩⟩

/-- Extract a monotone cofinal subnet from an arbitrary cluster point. -/
theorem subnet_of_clusterPt {X : Type u} [TopologicalSpace X]
    {ι : Type v} [Preorder ι] [Nonempty ι] [IsDirectedOrder ι]
    {a : ι → X} {x : X} (hx : MapClusterPt x atTop a) :
    ∃ (κ : Type (max u v)) (_ : Preorder κ) (_ : Nonempty κ) (_ : IsDirectedOrder κ)
      (φ : κ → ι), IsSubnetMap φ ∧ Tendsto (a ∘ φ) atTop (𝓝 x) := by
  let _ := subnetIndex_directed hx
  refine ⟨SubnetIndex a x, inferInstance, inferInstance, inferInstance,
    (fun p => p.val.1), ⟨?_, ?_⟩, ?_⟩
  · intro p q hpq
    exact hpq.1
  · intro i
    exact ⟨⟨(i, univ), univ_mem, mem_univ _⟩, le_rfl⟩
  · apply tendsto_atTop'.2
    intro U hU
    obtain ⟨p⟩ := (inferInstance : Nonempty (SubnetIndex a x))
    obtain ⟨i, _, hi⟩ := frequently_atTop.1 (mapClusterPt_iff_frequently.1 hx U hU) p.val.1
    exact ⟨⟨(i, U), hU, hi⟩, fun q hpq => hpq.2 q.property.2⟩

theorem compactSubnet : Specs.ExpandedFA.NetTests.compactSubnet.{u,v} := by
  intro X _ _ ι _ _ _ a
  obtain ⟨x, hx⟩ := exists_clusterPt_of_compactSpace (map a atTop)
  obtain ⟨κ, hκ, hnκ, hdκ, φ, hφ, hconv⟩ := subnet_of_clusterPt hx
  exact ⟨κ, hκ, hnκ, hdκ, φ, x, hφ, hconv⟩

theorem compactCriterion : Specs.ExpandedFA.NetTests.compactCriterion.{u} := by
  intro X _
  constructor
  · intro hX
    let _ := hX
    exact compactSubnet X
  · intro h
    refine ⟨?_⟩
    intro F _ _
    obtain ⟨κ, hκ, hnκ, hdκ, φ, x, hφ, hconv⟩ :=
      h (FilterIndex F) (fun p => p.val.2)
    letI := hκ
    let _ := hnκ
    let _ := hdκ
    refine ⟨x, mem_univ _, ?_⟩
    have ht : Tendsto φ atTop atTop := hφ.1.tendsto_atTop_atTop hφ.2
    have hc := hconv.mapClusterPt.of_comp ht
    change ClusterPt x (map (fun p : FilterIndex F => p.val.2) atTop) at hc
    rwa [map_filterIndex] at hc

/-- Terms with second coordinate at least two vanish, while the first row
contains arbitrarily large positive integers. -/
theorem unboundedNetExample : Specs.ExpandedFA.NetTests.unboundedNetExample := by
  have hev : ∀ᶠ i in atTop, spikeNet i = 0 := by
    apply eventually_atTop.2
    refine ⟨(1, 2), ?_⟩
    intro i hi
    have hi2 : i.2 ≠ 1 := by
      intro heq
      have : (2 : ℕ+) ≤ 1 := heq ▸ hi.2
      norm_num at this
    simp [spikeNet, hi2]
  have hunb : ∀ R : ℝ, ∃ i, R < spikeNet i := by
    intro R
    obtain ⟨n, hn⟩ := exists_nat_gt R
    refine ⟨(⟨n + 1, Nat.zero_lt_succ n⟩, 1), ?_⟩
    simp only [spikeNet, ↓reduceIte]
    exact hn.trans (by exact_mod_cast Nat.lt_succ_self n)
  refine ⟨hev, ?_, hunb, ?_⟩
  · have heq : spikeNet =ᶠ[atTop] (fun _ => (0 : ℝ)) := hev
    exact tendsto_const_nhds.congr' heq.symm
  · intro hbound
    obtain ⟨R, hR⟩ := (NormedSpace.isVonNBounded_iff' ℝ).1 hbound
    obtain ⟨i, hi⟩ := hunb R
    have hle := hR (spikeNet i) (mem_range_self i)
    exact (not_lt_of_ge (le_trans (le_abs_self _) hle)) hi

end ExpandedFA.NetTests
