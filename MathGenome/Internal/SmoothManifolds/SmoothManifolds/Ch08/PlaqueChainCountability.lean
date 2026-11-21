import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch08.PlaqueChainCountability

set_option autoImplicit false
namespace SmoothManifolds.PlaqueChains
open Set
universe u v w

/-- A relation with countable sets of successors has countable forward components. -/
theorem countable_reachable {A : Type*} (r : A → A → Prop)
    (hr : ∀ a, {b | r a b}.Countable) (a : A) :
    {b | Relation.ReflTransGen r a b}.Countable := by
  let levels : ℕ → Set A :=
    Nat.rec {a} (fun _ s => ⋃ b ∈ s, {c | r b c})
  have hc : ∀ n, (levels n).Countable := by
    intro n
    induction n with
    | zero => exact countable_singleton a
    | succ n ih => exact ih.biUnion (fun b _ => hr b)
  apply (countable_iUnion hc).mono
  intro b hb
  have : ∃ n, b ∈ levels n := by
    induction hb with
    | refl => exact ⟨0, mem_singleton a⟩
    | @tail b c hab hbc ih =>
      obtain ⟨n, hn⟩ := ih
      exact ⟨n + 1, mem_iUnion.2 ⟨b, mem_iUnion.2 ⟨hn, hbc⟩⟩⟩
  exact mem_iUnion.2 this

/-- Nonempty disjoint open intersections in a plaque form a countable family. -/
theorem neighbors_countable {X : Type u} [TopologicalSpace X]
    {I : Type v} [Countable I] {Z : Type w} (P : I × Z → Set X)
    (hsecond : ∀ a, SecondCountableTopology (P a))
    (hdisjoint : ∀ i, Pairwise (fun z z' => Disjoint (P (i, z)) (P (i, z'))))
    (hopen : ∀ a b, IsOpen (Subtype.val ⁻¹' P b : Set (P a))) (a : I × Z) :
    {b | (P a ∩ P b).Nonempty}.Countable := by
  let := hsecond a
  have hf (i : I) : {z | (P a ∩ P (i, z)).Nonempty}.Countable := by
    apply Set.PairwiseDisjoint.countable_of_isOpen
      (s := fun z => (Subtype.val ⁻¹' P (i, z) : Set (P a)))
    · intro z hz z' hz' hne
      exact (hdisjoint i hne).preimage Subtype.val
    · intro z hz
      exact hopen a (i, z)
    · intro z hz
      obtain ⟨x, hxa, hxz⟩ := hz
      exact ⟨⟨x, hxa⟩, hxz⟩
  apply (countable_iUnion (fun i => (hf i).image (fun z => (i, z)))).mono
  rintro ⟨i, z⟩ hb
  exact mem_iUnion.2 ⟨i, mem_image_of_mem _ hb⟩

theorem reachable_countable :
    Specs.SmoothManifolds.Ch08.PlaqueChainCountability.reachable_countableType := by
  intro X _ I _ Z P hsecond hdisjoint hopen a
  exact countable_reachable _ (neighbors_countable P hsecond hdisjoint hopen) a

/-- Reverse an intersecting plaque chain, without requiring any plaque nonempty
unless it is used by an edge. -/
theorem reverse_chain {X : Type*} {A : Type*} (P : A → Set X) {a b : A}
    (h : Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) a b) :
    Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) b a := by
  induction h with
  | refl => exact .refl
  | tail hab hbc ih =>
    exact ih.head (by obtain ⟨x, hxb, hxc⟩ := hbc; exact ⟨x, hxc, hxb⟩)

/-- The point-generated equivalence relation gives chains between any plaques
containing its endpoints. Covering is used only at an intermediate point. -/
theorem chain_of_point_relation {X : Type*} {A : Type*} (P : A → Set X)
    (hcover : ∀ x, ∃ a, x ∈ P a) {x y : X}
    (h : Relation.EqvGen (fun x y => ∃ a, x ∈ P a ∧ y ∈ P a) x y) :
    ∀ a b, x ∈ P a → y ∈ P b →
      Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) a b := by
  induction h with
  | rel x y h =>
    obtain ⟨c, hxc, hyc⟩ := h
    intro a b hxa hyb
    exact (Relation.ReflTransGen.single ⟨x, hxa, hxc⟩).trans
      (.single ⟨y, hyc, hyb⟩)
  | refl x =>
    intro a b hxa hxb
    exact .single ⟨x, hxa, hxb⟩
  | symm x y h ih =>
    intro a b hya hxb
    exact reverse_chain P (ih b a hxb hya)
  | trans x y z hxy hyz ihxy ihyz =>
    obtain ⟨c, hyc⟩ := hcover y
    intro a b hxa hzb
    exact (ihxy a c hxa hyc).trans (ihyz c b hyc hzb)

/-- Every point of a reachable plaque belongs to the initial point's class. -/
theorem point_relation_of_chain {X : Type*} {A : Type*} (P : A → Set X)
    {a b : A} {p : X} (hp : p ∈ P a)
    (h : Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) a b) :
    ∀ q ∈ P b, Relation.EqvGen (fun x y => ∃ c, x ∈ P c ∧ y ∈ P c) p q := by
  induction h with
  | refl =>
    intro q hq
    exact .rel _ _ ⟨a, hp, hq⟩
  | @tail b c hab hbc ih =>
    obtain ⟨x, hxb, hxc⟩ := hbc
    intro q hq
    exact .trans _ _ _ (ih x hxb) (.rel _ _ ⟨c, hxc, hq⟩)

theorem point_class_cover :
    Specs.SmoothManifolds.Ch08.PlaqueChainCountability.point_class_coverType := by
  intro X _ I _ Z P hsecond hdisjoint hopen hcover p
  obtain ⟨a, hpa⟩ := hcover p
  let S := {b | Relation.ReflTransGen (fun c d => (P c ∩ P d).Nonempty) a b}
  refine ⟨S, reachable_countable P hsecond hdisjoint hopen a, ?_, ?_⟩
  · intro b hb q hq
    exact point_relation_of_chain P hpa hb q hq
  · ext q
    constructor
    · intro hq
      obtain ⟨b, hqb⟩ := hcover q
      exact mem_iUnion.2 ⟨b, mem_iUnion.2
        ⟨chain_of_point_relation P hcover hq a b hpa hqb, hqb⟩⟩
    · intro hq
      obtain ⟨b, hqb⟩ := mem_iUnion.1 hq
      obtain ⟨hb, hqb⟩ := mem_iUnion.1 hqb
      exact point_relation_of_chain P hpa hb q hqb

end SmoothManifolds.PlaqueChains
