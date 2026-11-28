import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.HomogeneousGenerators
import Mathlib.RingTheory.FiniteType

open LinearAlgebraicGroups

universe u v w

namespace RepTheorySurvey.Invariants.Specs

/-- Hilbert finite generation for an action by algebra automorphisms. -/
def GroupHilbertFiniteGeneration : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w}
    [Field k] [Group G] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : GroupAlgebraAction k G A)
    (R : A →ₗ[k] groupFixedSubalgebra ρ),
    𝒜 0 = (⊥ : Subalgebra k A).toSubmodule →
    (∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n) →
    groupIsReynolds ρ R →
    (∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) →
    ∃ (m : ℕ) (f : Fin m → groupFixedSubalgebra ρ) (d : Fin m → ℕ),
      (∀ i, 0 < d i) ∧ (∀ i, (f i : A) ∈ 𝒜 (d i)) ∧
        Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = groupFixedSubalgebra ρ

/-- Hilbert finite generation for a rational algebra action in the right coaction model. -/
def RationalHilbertFiniteGeneration : Prop :=
  ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
    {H : HopfAlgebraCategory k}
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] rationalFixedSubalgebra ρ),
    𝒜 0 = (⊥ : Subalgebra k A).toSubmodule →
    (∀ n, (rationalToRightComodule ρ).IsSubcomodule (𝒜 n)) →
    rationalIsReynolds ρ R →
    (∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) →
    ∃ (m : ℕ) (f : Fin m → rationalFixedSubalgebra ρ) (d : Fin m → ℕ),
      (∀ i, 0 < d i) ∧ (∀ i, (f i : A) ∈ 𝒜 (d i)) ∧
        Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = rationalFixedSubalgebra ρ

end RepTheorySurvey.Invariants.Specs
