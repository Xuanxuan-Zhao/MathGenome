import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.CanonicalQuotient

/-! GC-13 (paper.tex:4823–4850). These statements concern canonical
modules when they exist; they assert no existence over an arbitrary base. -/

universe u
namespace AdvCommAlg.Gorenstein.CanonicalUniquenessSpec

def uniquenessType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W V : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W]
    [AddCommGroup V] [Module R V] [Module.Finite R V],
    Specs.IsCanonicalModuleValue R W → Specs.IsCanonicalModuleValue R V →
    Nonempty (W ≃ₗ[R] V)

def gorensteinTestType : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsNoetherianRing R] [IsLocalRing R]
    (W : Type u) [AddCommGroup W] [Module R W] [Module.Finite R W],
    Specs.IsCanonicalModuleValue R W →
    (Specs.LocalGorensteinValue R ↔ Nonempty (W ≃ₗ[R] R))

/-- Both modules are the actual Ext modules, with the target action from
GC-10, for arbitrary surjective Gorenstein local presentations. -/
def presentationIndependenceType : Prop :=
  ∀ (S T R : Type u) [CommRing S] [CommRing T] [CommRing R]
    [IsNoetherianRing S] [IsNoetherianRing T] [IsNoetherianRing R]
    [IsLocalRing S] [IsLocalRing T] [IsLocalRing R]
    [Algebra S R] [Algebra T R],
    Function.Surjective (algebraMap S R) → Function.Surjective (algebraMap T R) →
    Specs.LocalGorensteinValue S → Specs.LocalGorensteinValue T →
    CohenMacaulay.Specs.LocalCohenMacaulayValue R R →
    ∀ s t d : ℕ, ringKrullDim S = (s : WithBot ℕ∞) →
      ringKrullDim T = (t : WithBot ℕ∞) → ringKrullDim R = (d : WithBot ℕ∞) →
      Nonempty (CanonicalQuotient.omega S R s d ≃ₗ[R] CanonicalQuotient.omega T R t d)

end AdvCommAlg.Gorenstein.CanonicalUniquenessSpec
