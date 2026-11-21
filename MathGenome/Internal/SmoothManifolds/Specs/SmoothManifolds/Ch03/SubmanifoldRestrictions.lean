import MathGenome.Internal.SmoothManifolds.Specs.SmoothManifolds.Ch03.MapClasses

/-! Restriction statements retain the chosen topology and smooth structure on
an immersed subset. They quantify over every such structure, rather than
choosing a topology from the existential submanifold predicate. -/
namespace Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions
open _root_.SmoothManifolds _root_.SmoothManifolds.ModelData
  _root_.SmoothManifolds.AtlasData _root_.SmoothManifolds.MapData
  _root_.SmoothManifolds.MapClassData
universe u v w

/-- Smoothness can be detected after a smooth immersion, provided the lift
is continuous in the domain topology of that immersion. -/
def lift_through_immersionType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v} {P : Type w}
    [TopologicalSpace M] [TopologicalSpace N] [TopologicalSpace P]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N)
    (R : SmoothManifold k c P) (i : P → N) (f : M → P),
    IsSmoothMap R T i → IsImmersion R T i → Continuous f →
    IsSmoothMap S T (i ∘ f) → IsSmoothMap S R f

/-- Restrict the source to any immersed submanifold, with its own topology. -/
def restrict_sourceType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (s : Set M)
    (t : TopologicalSpace s) (R : @SmoothManifold k c s t) (f : M → N),
    @IsSmoothMap k m c a s M t _ R S Subtype.val →
    @IsImmersion k m c a s M t _ R S Subtype.val →
    IsSmoothMap S T f →
    @IsSmoothMap k n c b s N t _ R T (fun x => f x.val)

/-- The range condition defines the induced map; continuity refers to t,
which need not be the ambient subspace topology. -/
def restrict_targetType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (s : Set N)
    (t : TopologicalSpace s) (R : @SmoothManifold k c s t) (f : M → N)
    (himage : ∀ x, f x ∈ s),
    @IsSmoothMap k n c b s N t _ R T Subtype.val →
    @IsImmersion k n c b s N t _ R T Subtype.val →
    IsSmoothMap S T f →
    @Continuous M s _ t (fun x => ⟨f x, himage x⟩) →
    @IsSmoothMap m k a c M s _ t S R (fun x => ⟨f x, himage x⟩)

/-- An embedded inclusion supplies continuity of the induced map. -/
def restrict_embedded_targetType : Prop :=
  ∀ {m n k : ℕ} {a b c : ModelKind} {M : Type u} {N : Type v}
    [TopologicalSpace M] [TopologicalSpace N]
    (S : SmoothManifold m a M) (T : SmoothManifold n b N) (s : Set N)
    (t : TopologicalSpace s) (R : @SmoothManifold k c s t) (f : M → N)
    (himage : ∀ x, f x ∈ s),
    @IsSmoothEmbedding k n c b s N t _ R T Subtype.val →
    IsSmoothMap S T f →
    @IsSmoothMap m k a c M s _ t S R (fun x => ⟨f x, himage x⟩)

end Specs.SmoothManifolds.Ch03.SubmanifoldRestrictions
