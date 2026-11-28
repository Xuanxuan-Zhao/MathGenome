import MathGenome.Internal.RepresentationTheoryDeepening.Specs.RepTheorySurvey.Invariants.Actions
import Mathlib.RingTheory.Adjoin.Basic
import Mathlib.RingTheory.GradedAlgebra.Basic
import Mathlib.RingTheory.Ideal.Span

open LinearAlgebraicGroups

universe u v w t

namespace RepTheorySurvey.Invariants.Specs

variable {k : Type u} {A : Type w} [Field k] [CommRing A] [Algebra k A]

/-- The elements of a subalgebra that are homogeneous of some positive degree. -/
def positiveHomogeneousInvariants (𝒜 : ℕ → Submodule k A) (B : Subalgebra k A) : Set A :=
  {x | x ∈ B ∧ ∃ n > 0, x ∈ 𝒜 n}

set_option linter.checkUnivs false in
def PositiveHomogeneousInvariantsType :=
  ∀ {k : Type u} {A : Type w} [Field k] [CommRing A] [Algebra k A],
    (ℕ → Submodule k A) → Subalgebra k A → Set A

def GroupFixedSubalgebraIsInternal : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : GroupAlgebraAction k G A),
    (∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n) →
    DirectSum.IsInternal (fun n ↦ (𝒜 n).comap (groupFixedSubalgebra ρ).val.toLinearMap)

def RationalFixedSubalgebraIsInternal : Prop :=
  ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A] {H : HopfAlgebraCategory k}
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : RationalAlgebraAction H A),
    (∀ n, (rationalToRightComodule ρ).IsSubcomodule (𝒜 n)) →
    DirectSum.IsInternal (fun n ↦ (𝒜 n).comap (rationalFixedSubalgebra ρ).val.toLinearMap)

def GroupAdjoinHomogeneousEqFixedSubalgebra : Prop :=
  ∀ {k : Type u} {G : Type v} {A : Type w} [Field k] [Group G] [CommRing A] [Algebra k A]
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : GroupAlgebraAction k G A)
    (R : A →ₗ[k] groupFixedSubalgebra ρ) {ι : Type t} [Finite ι]
    (f : ι → groupFixedSubalgebra ρ) (d : ι → ℕ),
    𝒜 0 = (⊥ : Subalgebra k A).toSubmodule →
    (∀ (g : G) (n : ℕ) (x : A), x ∈ 𝒜 n → ρ g x ∈ 𝒜 n) →
    groupIsReynolds ρ R →
    (∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) →
    (∀ i, 0 < d i) →
    (∀ i, (f i : A) ∈ 𝒜 (d i)) →
    Ideal.span (Set.range fun i ↦ (f i : A)) =
      Ideal.span (positiveHomogeneousInvariants 𝒜 (groupFixedSubalgebra ρ)) →
    Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = groupFixedSubalgebra ρ

def RationalAdjoinHomogeneousEqFixedSubalgebra : Prop :=
  ∀ {k A : Type u} [Field k] [CommRing A] [Algebra k A] {H : HopfAlgebraCategory k}
    (𝒜 : ℕ → Submodule k A) [GradedAlgebra 𝒜] (ρ : RationalAlgebraAction H A)
    (R : A →ₗ[k] rationalFixedSubalgebra ρ) {ι : Type t} [Finite ι]
    (f : ι → rationalFixedSubalgebra ρ) (d : ι → ℕ),
    𝒜 0 = (⊥ : Subalgebra k A).toSubmodule →
    (∀ n, (rationalToRightComodule ρ).IsSubcomodule (𝒜 n)) →
    rationalIsReynolds ρ R →
    (∀ (n : ℕ) (x : A), x ∈ 𝒜 n → (R x : A) ∈ 𝒜 n) →
    (∀ i, 0 < d i) →
    (∀ i, (f i : A) ∈ 𝒜 (d i)) →
    Ideal.span (Set.range fun i ↦ (f i : A)) =
      Ideal.span (positiveHomogeneousInvariants 𝒜 (rationalFixedSubalgebra ρ)) →
    Algebra.adjoin k (Set.range fun i ↦ (f i : A)) = rationalFixedSubalgebra ρ

end RepTheorySurvey.Invariants.Specs
