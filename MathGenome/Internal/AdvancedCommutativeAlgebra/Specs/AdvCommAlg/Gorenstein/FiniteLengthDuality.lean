import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.FiniteLengthDual

/-! GC-04: the actual evaluation map and the exact contravariant duality.
All modules, including the zero module, are allowed. The envelope is not
assumed finite. Exactness and length preservation use the upstream interface. -/
noncomputable section
universe u
namespace AdvCommAlg.Gorenstein

/-- Evaluation into the double Hom dual with values in E. -/
def envelopeEvaluation (R E M : Type u) [CommRing R]
    [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M] :
    M →ₗ[R] ((M →ₗ[R] E) →ₗ[R] E) :=
  LinearMap.flip (LinearMap.id : (M →ₗ[R] E) →ₗ[R] (M →ₗ[R] E))

namespace FiniteLengthDualitySpec

def biduality : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      ∃ e : M ≃ₗ[R] ((M →ₗ[R] E) →ₗ[R] E),
        e.toLinearMap = envelopeEvaluation R E M

/-- Naturality with respect to every R-linear map, using precomposition on duals. -/
def naturality : Prop :=
  ∀ (R : Type u) [CommRing R] (E M N : Type u)
    [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] (f : M →ₗ[R] N),
    (LinearMap.lcomp R E (LinearMap.lcomp R E f)).comp (envelopeEvaluation R E M) =
      (envelopeEvaluation R E N).comp f

/-- The dual gives a bijection of Hom sets with the direction reversed. -/
def fullyFaithful : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∀ (M N : Type u) [AddCommGroup M] [Module R M]
      [AddCommGroup N] [Module R N] [Module.Finite R M] [Module.Finite R N],
      Function.Bijective (fun f : M →ₗ[R] N => LinearMap.lcomp R E f)

/-- Coherence of the two evaluation isomorphisms of the self-inverse duality. -/
def triangle : Prop :=
  ∀ (R : Type u) [CommRing R] (E M : Type u)
    [AddCommGroup E] [Module R E] [AddCommGroup M] [Module R M],
    (LinearMap.lcomp R E (envelopeEvaluation R E M)).comp
      (envelopeEvaluation R E (M →ₗ[R] E)) = LinearMap.id

/-- Algebraic presentation of an exact contravariant duality: closure in finite
modules, exactness, length preservation, a natural evaluation isomorphism,
full faithfulness, and the self-inverse coherence identity. Biduality also gives
essential surjectivity, with the dual of N as a preimage of every finite N. -/
def exactDuality : Prop :=
  FiniteLengthDualSpec.finiteDual.{u} ∧ FiniteLengthDualSpec.exactness.{u} ∧
  FiniteLengthDualSpec.lengthDual.{u} ∧ biduality.{u} ∧ naturality.{u} ∧
  fullyFaithful.{u} ∧ triangle.{u}

end FiniteLengthDualitySpec
end AdvCommAlg.Gorenstein
