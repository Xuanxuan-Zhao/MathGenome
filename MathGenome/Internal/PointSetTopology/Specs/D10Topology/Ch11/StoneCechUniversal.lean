import MathGenome.Internal.PointSetTopology.Specs.D10Topology.Ch11.StoneCechConstruction

/-!
Independent statements for the extension and uniqueness assertions of
paper.tex, d10:11:stone-cech. `Beta` is the actual evaluation-closure
construction from the upstream Spec. Targets may lie in a different
universe and need not be inhabited. Equality after composition with
`betaUnit` means equality on the actual dense image of X.
-/

open Set Topology
universe u v

namespace Specs.D10Topology.Ch11.StoneCechUniversal

def stoneCech_extension_unique : Prop :=
  ∀ {X : Type u} {H : Type v} [TopologicalSpace X] [TopologicalSpace H] [T2Space H]
    (g h : StoneCechConstruction.Beta X → H), Continuous g → Continuous h →
    g ∘ StoneCechConstruction.betaUnit = h ∘ StoneCechConstruction.betaUnit → g = h

def stoneCech_universal : Prop :=
  ∀ {X : Type u} {H : Type v} [TopologicalSpace X] [TopologicalSpace H]
    [CompactSpace H] [T2Space H], Ch07.SeparationConventions.tychonoffValue X →
    ∀ (f : X → H), Continuous f →
      ∃! g : StoneCechConstruction.Beta X → H,
        Continuous g ∧ g ∘ StoneCechConstruction.betaUnit = f

def stoneCech_empty_target : Prop :=
  ∀ {X : Type u} {H : Type v} [TopologicalSpace X] [IsEmpty H] (f : X → H),
    IsEmpty X ∧ IsEmpty (StoneCechConstruction.Beta X)

/-- The comparison compactification has the same extension property.
It suffices to test its property on targets in the universe of X, since
this includes Beta X. No restriction is imposed on the universe of K. -/
def stoneCech_characterization : Prop :=
  ∀ {X : Type u} {K : Type v} [TopologicalSpace X] [TopologicalSpace K],
    Ch07.SeparationConventions.tychonoffValue X → ∀ (i : X → K),
    LocalCompactConventions.HausdorffCompactification i →
    (∀ (H : Type u) [TopologicalSpace H] [CompactSpace H] [T2Space H]
      (f : X → H), Continuous f →
      ∃! g : K → H, Continuous g ∧ g ∘ i = f) →
    ∃! e : StoneCechConstruction.Beta X ≃ₜ K,
      ∀ x, e (StoneCechConstruction.betaUnit x) = i x

end Specs.D10Topology.Ch11.StoneCechUniversal
