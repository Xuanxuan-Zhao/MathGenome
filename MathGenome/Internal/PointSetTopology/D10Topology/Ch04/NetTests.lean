import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch04.NetTests
import MathGenome.Internal.PointSetTopology.D10Topology.Ch04.NetsAndSubnets
import MathGenome.Internal.PointSetTopology.D10Topology.Ch02.ContinuityTests

/-!
Closure and continuity by nets, paper.tex d10:04:closure-net and
 d10:04:continuity-net. The witness is the paper's net of pairs (U,a),
ordered by reverse inclusion of U. ULift allows the same construction in
any larger index universe. No selection of a point for each neighborhood
is needed, and antisymmetry is not required.
-/

open Set
universe u v w
namespace D10Topology.Ch04

variable {X : Type u} [t : TopologicalSpace X]

theorem mem_closure_of_net {D : Type v}
    [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (A : Set X) (a : Net D X) (x : X)
    (ha : ∀ d, a d ∈ A) (hx : Converges t a x) : x ∈ closure A := by
  apply (Ch01.closure_neighborhood_test A x).mpr
  intro N hN
  obtain ⟨d₀, hd₀⟩ := hx N hN
  exact ⟨a d₀, hd₀ d₀ le_rfl, ha d₀⟩

private def ClosureIndex (A : Set X) (x : X) :=
  {q : ULift.{v} (Set X × X) //
    IsOpen q.down.1 ∧ x ∈ q.down.1 ∧ q.down.2 ∈ q.down.1 ∩ A}

private instance closureIndexPreorder (A : Set X) (x : X) :
    Preorder (ClosureIndex.{u, v} A x) where
  le q r := r.val.down.1 ⊆ q.val.down.1
  le_refl _ := Subset.rfl
  le_trans _ _ _ hqr hrs := hrs.trans hqr

private theorem closureIndex_nonempty (A : Set X) (x : X) (hx : x ∈ closure A) :
    Nonempty (ClosureIndex.{u, v} A x) := by
  obtain ⟨a, haU, haA⟩ :=
    (Ch01.closure_neighborhood_test A x).mp hx univ (Ch01.neighborhood_univ t x)
  exact ⟨⟨⟨(univ, a)⟩, isOpen_univ, mem_univ x, haU, haA⟩⟩

private theorem closureIndex_directed (A : Set X) (x : X) (hx : x ∈ closure A) :
    IsDirectedOrder (ClosureIndex.{u, v} A x) := by
  constructor
  intro q r
  have hU : Ch01.Neighborhood t x (q.val.down.1 ∩ r.val.down.1) :=
    ⟨_, q.property.1.inter r.property.1,
      ⟨q.property.2.1, r.property.2.1⟩, Subset.rfl⟩
  obtain ⟨a, haU, haA⟩ := (Ch01.closure_neighborhood_test A x).mp hx _ hU
  exact ⟨⟨⟨(q.val.down.1 ∩ r.val.down.1, a)⟩,
    q.property.1.inter r.property.1, ⟨q.property.2.1, r.property.2.1⟩, haU, haA⟩,
    inter_subset_left, inter_subset_right⟩

private theorem closureIndex_converges (A : Set X) (x : X) (hx : x ∈ closure A) :
    Converges t (fun q : ClosureIndex.{u, v} A x => q.val.down.2) x := by
  intro N hN
  obtain ⟨U, hU, hxU, hUN⟩ := hN
  obtain ⟨a, haU, haA⟩ := (Ch01.closure_neighborhood_test A x).mp hx U
    ⟨U, hU, hxU, Subset.rfl⟩
  refine ⟨⟨⟨(U, a)⟩, hU, hxU, haU, haA⟩, ?_⟩
  intro q hq
  exact hUN (hq q.property.2.2.1)

theorem closure_iff_exists_net (A : Set X) (x : X) :
    x ∈ closure A ↔
      ∃ (D : Type (max u v)) (p : Preorder D),
        Nonempty D ∧ @IsDirectedOrder D p.toLE ∧
        ∃ a : Net D X, (∀ d, a d ∈ A) ∧ @Converges D X p t a x := by
  constructor
  · intro hx
    exact ⟨ClosureIndex.{u, v} A x, closureIndexPreorder A x,
      closureIndex_nonempty A x hx, closureIndex_directed A x hx,
      (fun q => q.val.down.2), (fun q => q.property.2.2.2),
      closureIndex_converges A x hx⟩
  · rintro ⟨D, p, hn, hd, a, ha, hx⟩
    let := p
    let := hn
    let := hd
    exact mem_closure_of_net A a x ha hx

theorem closed_iff_net_limits (A : Set X) :
    IsClosed A ↔
      ∀ {D : Type (max u v)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X) (x : X), (∀ d, a d ∈ A) → Converges t a x → x ∈ A := by
  constructor
  · intro hA D _ _ _ a x ha hx
    exact hA.closure_subset (mem_closure_of_net A a x ha hx)
  · intro h
    apply isClosed_of_closure_subset
    intro x hx
    obtain ⟨D, p, hn, hd, a, ha, hx⟩ := (closure_iff_exists_net.{u, v} A x).mp hx
    let := p
    let := hn
    let := hd
    exact h a x ha hx

variable {Y : Type v} [tY : TopologicalSpace Y]

theorem continuousAt_preserves_net_limits (f : X → Y) (x : X) (hf : ContinuousAt f x)
    {D : Type w} [Preorder D] [Nonempty D] [IsDirectedOrder D]
    (a : Net D X) (ha : Converges t a x) : Converges tY (f ∘ a) (f x) := by
  intro N hN
  exact ha (f ⁻¹' N) ((Ch02.continuousAt_iff_neighborhood_preimages f x).mp hf N hN)

theorem continuousAt_iff_net_limits (f : X → Y) (x : X) :
    ContinuousAt f x ↔
      ∀ {D : Type (max u w)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X), Converges t a x → Converges tY (f ∘ a) (f x) := by
  constructor
  · intro hf D _ _ _ a ha
    exact continuousAt_preserves_net_limits f x hf a ha
  · intro h
    apply (Ch02.continuousAt_iff_neighborhood_preimages f x).mpr
    intro N hN
    by_contra hpre
    have hx : x ∈ closure (f ⁻¹' N)ᶜ := by
      apply (Ch01.closure_neighborhood_test _ x).mpr
      intro U hU
      by_contra hdisj
      have hsub : U ⊆ f ⁻¹' N := by
        intro a ha
        by_contra hfa
        exact hdisj ⟨a, ha, hfa⟩
      exact hpre (Ch01.neighborhood_mono t x U (f ⁻¹' N) hU hsub)
    obtain ⟨D, p, hn, hd, a, ha, hx⟩ :=
      (closure_iff_exists_net.{u, w} (f ⁻¹' N)ᶜ x).mp hx
    let := p
    let := hn
    let := hd
    obtain ⟨d₀, hd₀⟩ := h a hx N hN
    exact ha d₀ (hd₀ d₀ le_rfl)

theorem continuous_iff_net_limits (f : X → Y) :
    Continuous f ↔
      ∀ {D : Type (max u w)} [Preorder D] [Nonempty D] [IsDirectedOrder D]
        (a : Net D X) (x : X), Converges t a x → Converges tY (f ∘ a) (f x) := by
  rw [Ch02.continuous_iff_pointwise]
  constructor
  · intro h D _ _ _ a x ha
    exact continuousAt_preserves_net_limits f x (h x) a ha
  · intro h x
    apply (continuousAt_iff_net_limits.{u, v, w} f x).mpr
    intro D _ _ _ a ha
    exact h a x ha

end D10Topology.Ch04
