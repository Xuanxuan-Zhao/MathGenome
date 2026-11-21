import Mathlib.Algebra.Module.Injective
import Mathlib.RingTheory.Artinian.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Basic

/-! The single injective-envelope interface used throughout the Gorenstein chapter. -/
namespace AdvCommAlg.Gorenstein
universe u

/-- Essentiality means that every nonzero submodule meets the displayed image. -/
def IsEssential {R M E : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup E] [Module R E] (ι : M →ₗ[R] E) : Prop :=
  ∀ N : Submodule R E, N ≠ ⊥ → N ⊓ LinearMap.range ι ≠ ⊥

/-- An injective envelope includes its displayed inclusion, not just its isomorphism type. -/
structure IsInjectiveEnvelope {R M E : Type u} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup E] [Module R E] (ι : M →ₗ[R] E) : Prop where
  injective : Function.Injective ι
  injectiveModule : Module.Injective R E
  essential : IsEssential ι

/-- Data of an injective envelope, in the same universe as the original module. -/
structure InjectiveEnvelope (R M : Type u) [Ring R] [AddCommGroup M] [Module R M] where
  carrier : Type u
  [addCommGroup : AddCommGroup carrier]
  [module : Module R carrier]
  inclusion : M →ₗ[R] carrier
  isEnvelope : IsInjectiveEnvelope inclusion

attribute [instance] InjectiveEnvelope.addCommGroup InjectiveEnvelope.module

namespace InjectiveEnvelopeSpec

def existence : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsLocalRing R] [IsArtinianRing R],
    Nonempty (InjectiveEnvelope R (IsLocalRing.ResidueField R))

def uniqueness : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsLocalRing R] [IsArtinianRing R]
    (E F : Type u) [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E) (κ : IsLocalRing.ResidueField R →ₗ[R] F),
    IsInjectiveEnvelope ι → IsInjectiveEnvelope κ →
      ∃ e : E ≃ₗ[R] F, e.toLinearMap.comp ι = κ

end InjectiveEnvelopeSpec
end AdvCommAlg.Gorenstein
