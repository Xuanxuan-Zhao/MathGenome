import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic

/-!
The cyclic degree-characteristic converse of K07.20.artin_schreier,
paper.tex:6026–6042. The automorphism generator is supplied explicitly,
as in the upstream additive Hilbert 90 interface. `FiniteDimensional`
means finite extension degree, not a finite underlying field. No
perfection or invertibility-of-degree assumption is imposed.

The parameter condition says exactly that a is outside the image of
u ↦ u^p-u on K. The equality of intermediate fields states L=K(theta)
for the specified embedding K → L.
-/

universe u v
namespace Specs.D07.Ch20.ArtinSchreierCyclicDegreePConverse

/-- For every specified cyclic generator, an Artin–Schreier generator
with translation by one and nontrivial base-field parameter exists. -/
def CyclicDegreePConverse : Prop :=
  ∀ (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
    (p : ℕ) [Fact p.Prime] [CharP K p]
    [FiniteDimensional K L] [IsGalois K L],
    Module.finrank K L = p →
    ∀ (σ : L ≃ₐ[K] L),
      (∀ τ : L ≃ₐ[K] L, τ ∈ Subgroup.zpowers σ) →
      ∃ (θ : L) (a : K),
        σ θ = θ + 1 ∧
        θ ^ p - θ = algebraMap K L a ∧
        (¬ ∃ c : K, a = c ^ p - c) ∧
        IntermediateField.adjoin K ({θ} : Set L) = ⊤

end Specs.D07.Ch20.ArtinSchreierCyclicDegreePConverse
