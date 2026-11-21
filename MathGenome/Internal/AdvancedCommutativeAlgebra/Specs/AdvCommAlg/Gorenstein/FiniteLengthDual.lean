import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Gorenstein.InjectiveEnvelope
import MathGenome.Internal.AdvancedCommutativeAlgebra.Specs.AdvCommAlg.Depth.Type
import Mathlib.RingTheory.Length
import Mathlib.LinearAlgebra.LeftExact

/-! GC-04, paper.tex:4494–4517: the exactness and length part.
The double-dual evaluation assertion is allocated to `gc_04`.
No finiteness assumption is imposed on the displayed injective envelope. -/
noncomputable section
universe u
namespace AdvCommAlg.Gorenstein.FiniteLengthDualSpec

/-- Identification of the residue-field dual, with its canonical descended k-action.
The displayed equality fixes the identification by the given inclusion into E. -/
def residueDual : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∃ e : Depth.ResidueHom R E ≃ₗ[IsLocalRing.ResidueField R] IsLocalRing.ResidueField R,
      ∀ f, ι (e f) = f 1

/-- Exactness reverses the arrows of each short exact sequence. -/
def exactness : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∀ (A B C : Type u) [AddCommGroup A] [Module R A]
      [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C]
      [Module.Finite R A] [Module.Finite R B] [Module.Finite R C]
      (f : A →ₗ[R] B) (g : B →ₗ[R] C),
      Function.Injective f → Function.Surjective g → Function.Exact f g →
      Function.Injective (LinearMap.lcomp R E g) ∧
      Function.Surjective (LinearMap.lcomp R E f) ∧
      Function.Exact (LinearMap.lcomp R E g) (LinearMap.lcomp R E f)

def finiteDual : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.Finite R (M →ₗ[R] E)

def lengthDual : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    ∀ (M : Type u) [AddCommGroup M] [Module R M] [Module.Finite R M],
      Module.length R (M →ₗ[R] E) = Module.length R M

/-- Finiteness of E is a conclusion, obtained by taking M = R. -/
def envelopeLength : Prop :=
  ∀ (R : Type u) [CommRing R] [Nontrivial R] [IsArtinianRing R] [IsLocalRing R]
    (E : Type u) [AddCommGroup E] [Module R E]
    (ι : IsLocalRing.ResidueField R →ₗ[R] E), IsInjectiveEnvelope ι →
    Module.Finite R E ∧ Module.length R E = Module.length R R

end AdvCommAlg.Gorenstein.FiniteLengthDualSpec
