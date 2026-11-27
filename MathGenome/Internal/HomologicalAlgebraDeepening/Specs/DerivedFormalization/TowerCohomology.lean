import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerExactSequence

namespace Specs.DerivedFormalization.TowerCohomology

open CategoryTheory CategoryTheory.Limits Opposite
open Specs.DerivedFormalization.Cochains (compValue)
open Specs.DerivedFormalization.TowerExactSequence (transition)

universe u v

/-- The ordinary inverse limit of a degreewise-surjective tower of acyclic complexes
is acyclic. -/
def limitAcyclicType : Prop :=
  ∀ (R : Type u) [Ring R] (A : ℕᵒᵖ ⥤ compValue.{v} R),
    (∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i)) →
    (∀ n : ℕ, (A.obj (op n)).Acyclic) →
    (limit A).Acyclic

/-- A stagewise quasi-isomorphism between degreewise-surjective towers induces
a quasi-isomorphism on their ordinary inverse limits. -/
def limitMapQuasiIsoType : Prop :=
  ∀ (R : Type u) [Ring R] (A B : ℕᵒᵖ ⥤ compValue.{v} R) (f : A ⟶ B),
    (∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition A n).f i)) →
    (∀ (n : ℕ) (i : ℤ), Function.Surjective ((transition B n).f i)) →
    (∀ n : ℕ, QuasiIso (f.app (op n))) →
    QuasiIso (limMap f)

end Specs.DerivedFormalization.TowerCohomology
