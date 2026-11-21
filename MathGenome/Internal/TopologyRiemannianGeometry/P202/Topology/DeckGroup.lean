import MathGenome.Internal.TopologyRiemannianGeometry.P202Specs.Topology.DeckGroup
import MathGenome.Internal.TopologyRiemannianGeometry.P202.Topology.CoveringClassification

namespace P202.Topology.DeckGroup
open P202Specs.Topology
open P202.Topology.CoveringClassification
open scoped unitInterval
universe u v
noncomputable section
variable {E : Type u} {B : Type v} [TopologicalSpace E] [TopologicalSpace B]

omit [TopologicalSpace B] in
@[simp] theorem deckFiber_one (p : E → B) (b : B) (e : Fiber p b) :
    deckFiber p b 1 e = e := Subtype.ext rfl

omit [TopologicalSpace B] in
@[simp] theorem deckFiber_mul (p : E → B) (b : B) (F K : DeckGroup p) (e : Fiber p b) :
    deckFiber p b (F * K) e = deckFiber p b F (deckFiber p b K e) := Subtype.ext rfl

theorem determined : DeckExpected.determined.{u,v} := by
  intro E B _ _ _ p hp e F K heq
  have hmaps : (⟨F.val, F.val.continuous⟩ : C(E, E)) = ⟨K.val, K.val.continuous⟩ := by
    apply coveringLiftUnique E B E (F.val e) (p e) e
      ⟨p, congrFun F.property e⟩ hp ⟨p, rfl⟩
    · exact ⟨fun x => congrFun F.property x, rfl⟩
    · exact ⟨fun x => congrFun K.property x, heq.symm⟩
  apply Subtype.ext
  apply Homeomorph.ext
  exact fun x => DFunLike.congr_fun hmaps x

theorem free : DeckExpected.free.{u,v} := by
  intro E B _ _ _ p hp b e F hF
  apply determined E B p hp e.val
  exact congrArg Subtype.val hF

theorem commutes : DeckExpected.commutes.{u,v} := by
  intro E B _ _ p hp b F e g
  obtain ⟨a, rfl⟩ := loopClass_surjective g
  obtain ⟨L, hL, _⟩ := pathLifting E B p hp a.toContinuousMap e.val
    (e.property.trans a.source.symm)
  have hL' : ∀ t, p (L t) = a t := hL.1
  have hend := monodromyEndpointFormula E B p hp b e a L hL' hL.2
  let FL : C(unitInterval, E) := ⟨fun t => F.val (L t), F.val.continuous.comp L.continuous⟩
  have hFL : ∀ t, p (FL t) = a t := fun t => (congrFun F.property (L t)).trans (hL.1 t)
  have h0 : FL 0 = (deckFiber p b F e).val := congrArg F.val hL.2
  apply Subtype.ext
  change F.val (fiberAction p b e (loopClass a)).val = _
  rw [hend, monodromyEndpointFormula E B p hp b (deckFiber p b F e) a FL hFL h0]
  rfl

/-- Equality with the conjugate subgroup is exactly normalization. -/
theorem normalizes_iff {G : Type*} [Group G] (H : Subgroup G) (g : G) :
    g ∈ Subgroup.normalizer H ↔ H = conjugateSubgroup H g := by
  rw [Subgroup.mem_normalizer_iff]
  constructor
  · intro h
    ext a
    exact h a
  · intro h a
    exact SetLike.ext_iff.mp h a

/-- Homeomorphisms over the base preserve the monodromy stabilizer. -/
theorem subgroup_deck (p : C(E, B)) (b : B) (e : Fiber p b) (F : DeckGroup p) :
    fiberSubgroup p b e = fiberSubgroup p b (deckFiber p b F e) := by
  exact image_eq_of_pointedIsomorphism
    (⟨p, e.property⟩ : PointedMap E B e.val b)
    (⟨p, (deckFiber p b F e).property⟩ : PointedMap E B (deckFiber p b F e).val b)
    ⟨F.val, rfl, fun x => congrFun F.property x⟩

/-- The possible values at the distinguished point correspond precisely to
normalizer elements. This uses actual pointed homeomorphisms from the lifting
criterion, not assumed automorphisms of the fiber. -/
theorem exists_deck_iff [ConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : C(E, B)) (hp : Covering p) (b : B) (e : Fiber p b) (g : Pi1 B b) :
    (∃ F : DeckGroup p, deckFiber p b F e = fiberAction p b e g) ↔
      g ∈ Subgroup.normalizer (fiberSubgroup p b e : Set (Pi1 B b)) := by
  rw [normalizes_iff]
  have hc := pointChangeConjugacy E B p hp b e g
  constructor
  · rintro ⟨F, hF⟩
    rw [← hc, ← hF]
    exact subgroup_deck p b e F
  · intro hn
    let f := fiberAction p b e g
    let p₀ : PointedMap E B e.val b := ⟨p, e.property⟩
    let p₁ : PointedMap E B f.val b := ⟨p, f.property⟩
    have hs : p₀.induced.range = p₁.induced.range := hn.trans hc.symm
    obtain ⟨F, hF, hover⟩ :=
      (pointedIsomorphismCriterion E E B e.val f.val b p₀ p₁ hp hp).mp hs
    exact ⟨⟨F, funext hover⟩, Subtype.ext hF⟩

/-- The deck transformation specified by a normalizer loop. -/
def normalizerDeck [ConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : C(E, B)) (hp : Covering p) (b : B) (e : Fiber p b)
    (n : Subgroup.normalizer (fiberSubgroup p b e : Set (Pi1 B b))) : DeckGroup p :=
  ((exists_deck_iff p hp b e n.val).mpr n.property).choose

theorem normalizerDeck_point [ConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : C(E, B)) (hp : Covering p) (b : B) (e : Fiber p b)
    (n : Subgroup.normalizer (fiberSubgroup p b e : Set (Pi1 B b))) :
    deckFiber p b (normalizerDeck p hp b e n) e = fiberAction p b e n.val :=
  ((exists_deck_iff p hp b e n.val).mpr n.property).choose_spec

/-- First-path-first concatenation makes this a homomorphism with ordinary
composition on deck transformations, rather than the reversed multiplication. -/
def normalizerHom [ConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : C(E, B)) (hp : Covering p) (b : B) (e : Fiber p b) :
    Subgroup.normalizer (fiberSubgroup p b e : Set (Pi1 B b)) →* DeckGroup p where
  toFun := normalizerDeck p hp b e
  map_one' := by
    apply determined E B p hp e.val
    have h := normalizerDeck_point p hp b e 1
    change deckFiber p b (normalizerDeck p hp b e 1) e = fiberAction p b e 1 at h
    rw [(monodromyActionLaws E B p hp b).1] at h
    exact congrArg Subtype.val h
  map_mul' n m := by
    apply determined E B p hp e.val
    have heq : deckFiber p b (normalizerDeck p hp b e (n * m)) e =
        deckFiber p b (normalizerDeck p hp b e n * normalizerDeck p hp b e m) e := by
      rw [deckFiber_mul, normalizerDeck_point p hp b e m, commutes E B p hp,
        normalizerDeck_point, normalizerDeck_point,
        ← (monodromyActionLaws E B p hp b).2]
      rfl
    exact congrArg Subtype.val heq


/-- Its value at a point detects the identity element. -/
theorem eq_one_iff [ConnectedSpace E] (p : C(E, B)) (hp : Covering p)
    (b : B) (e : Fiber p b) (F : DeckGroup p) :
    F = 1 ↔ deckFiber p b F e = e := by
  constructor
  · rintro rfl
    exact deckFiber_one p b e
  · exact free E B p hp b e F

theorem normalizerHom_surjective [ConnectedSpace E] [PathConnectedSpace B]
    [LocallyPathConnectedSpace B] (p : C(E, B)) (hp : Covering p)
    (b : B) (e : Fiber p b) : Function.Surjective (normalizerHom p hp b e) := by
  have := connectedCoverPathConnected E B p hp
  intro F
  obtain ⟨g, hg⟩ := monodromyTransitive E B p hp b e (deckFiber p b F e)
  have hn := (exists_deck_iff p hp b e g).mp ⟨F, hg.symm⟩
  refine ⟨⟨g, hn⟩, determined E B p hp e.val ?_⟩
  exact congrArg Subtype.val ((normalizerDeck_point p hp b e ⟨g, hn⟩).trans hg)

theorem normalizerHom_kernel [ConnectedSpace E] [LocallyPathConnectedSpace B]
    (p : C(E, B)) (hp : Covering p) (b : B) (e : Fiber p b) :
    (fiberSubgroup p b e).subgroupOf (Subgroup.normalizer (fiberSubgroup p b e)) =
      (normalizerHom p hp b e).ker := by
  ext n
  change n.val ∈ fiberSubgroup p b e ↔ normalizerHom p hp b e n = 1
  rw [eq_one_iff p hp b e]
  change n.val ∈ fiberSubgroup p b e ↔ deckFiber p b (normalizerDeck p hp b e n) e = e
  rw [normalizerDeck_point]
  exact (monodromyStabilizer E B p hp b e n.val).symm

theorem deckGroup : DeckExpected.deckGroup.{u,v} := by
  intro E B _ _ _ _ _ _ p hp b e
  let H := (fiberSubgroup p b e).subgroupOf (Subgroup.normalizer (fiberSubgroup p b e))
  refine ⟨QuotientGroup.liftEquiv H (normalizerHom_surjective p hp b e)
    (normalizerHom_kernel p hp b e), ?_⟩
  intro n
  rw [QuotientGroup.liftEquiv_coe]
  exact normalizerDeck_point p hp b e n

theorem regularity : DeckExpected.regularity.{u,v} := by
  intro E B _ _ _ _ _ _ p hp b e
  have := connectedCoverPathConnected E B p hp
  rw [← Subgroup.normalizer_eq_top_iff]
  constructor
  · intro ht
    apply top_unique
    intro g _
    obtain ⟨F, hF⟩ := ht e (fiberAction p b e g)
    exact (exists_deck_iff p hp b e g).mp ⟨F, hF⟩
  · intro hnormal
    have heval : ∀ y : Fiber p b, ∃ F : DeckGroup p, deckFiber p b F e = y := by
      intro y
      obtain ⟨g, hg⟩ := monodromyTransitive E B p hp b e y
      have hn : g ∈ Subgroup.normalizer (fiberSubgroup p b e) := by
        rw [hnormal]
        trivial
      obtain ⟨F, hF⟩ := (exists_deck_iff p hp b e g).mpr hn
      exact ⟨F, hF.trans hg⟩
    intro x y
    obtain ⟨F, hF⟩ := heval x
    obtain ⟨K, hK⟩ := heval y
    refine ⟨K * F⁻¹, ?_⟩
    have hi : deckFiber p b F⁻¹ (deckFiber p b F e) = e := by
      rw [← deckFiber_mul, inv_mul_cancel, deckFiber_one]
    rw [deckFiber_mul, ← hF, hi, hK]

end
end P202.Topology.DeckGroup
