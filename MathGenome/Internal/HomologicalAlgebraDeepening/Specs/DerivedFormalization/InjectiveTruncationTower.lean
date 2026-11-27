import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Cochains
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.CategoryTheory.Functor.OfSequence

namespace Specs.DerivedFormalization.InjectiveTruncationTower

open CategoryTheory CategoryTheory.Limits
open Specs.DerivedFormalization.Cochains (compValue)

universe u v

variable {R : Type u} [CommRing R]

/-- The good lower truncations, using the opcycles (the cokernel of the
incoming differential) in the cutoff degree. -/
noncomputable abbrev stage (X : compValue.{v} R) (n : ℕ) :=
  CochainComplex.truncGE X (-(n : ℤ))

/-- The canonical quotient projections to the good truncations. -/
noncomputable abbrev projection (X : compValue.{v} R) (n : ℕ) :
    X ⟶ stage X n :=
  CochainComplex.πTruncGE X (-(n : ℤ))

/-- The good truncations form a degreewise surjective tower with limit the
original complex, via the canonical quotient projections. -/
def truncationTowerExistsType : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{v} R),
    ∃ t : ∀ n : ℕ, stage X (n + 1) ⟶ stage X n,
      (∀ n, projection X (n + 1) ≫ t n = projection X n) ∧
      (∀ (n : ℕ) (j : ℤ), Function.Surjective ((t n).f j)) ∧
      ∃ π : (Functor.const ℕᵒᵖ).obj X ⟶ Functor.ofOpSequence t,
        (∀ n : ℕ, π.app ⟨n⟩ = projection X n) ∧
        Nonempty (IsLimit (Cone.mk X π))

/-- A strict map of towers from the good truncations to bounded-below
complexes of injectives, with termwise monic quasi-isomorphisms at the stages
and module-linear sections of the injective tower transitions in each degree.
The module universe contains the ring universe. -/
def injectiveTruncationTowerExistsType : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{max u v} R)
    (t : ∀ n : ℕ, stage X (n + 1) ⟶ stage X n),
    (∀ n, projection X (n + 1) ≫ t n = projection X n) →
    ∃ (I : ℕᵒᵖ ⥤ compValue.{max u v} R) (ι : Functor.ofOpSequence t ⟶ I),
      (∀ n : ℕ, (I.obj ⟨n⟩).IsStrictlyGE (-(n : ℤ)) ∧
        (∀ j : ℤ, Injective ((I.obj ⟨n⟩).X j)) ∧
        (∀ j : ℤ, Mono ((ι.app ⟨n⟩).f j)) ∧ QuasiIso (ι.app ⟨n⟩)) ∧
      ∀ (n : ℕ) (j : ℤ), ∃ s : (I.obj ⟨n⟩).X j ⟶ (I.obj ⟨n + 1⟩).X j,
        s ≫ (I.map (homOfLE (Nat.le_add_right n 1)).op).f j = 𝟙 _

end Specs.DerivedFormalization.InjectiveTruncationTower
