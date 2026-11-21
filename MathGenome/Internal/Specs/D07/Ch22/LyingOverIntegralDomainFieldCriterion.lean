import Mathlib.Algebra.Field.IsField
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Ideal.Maximal
import Mathlib.RingTheory.IntegralClosure.IsIntegral.Defs

/-!
Independent specifications for the field criterion and maximal-ideal
contraction in the first paragraph of K07.22.lying_over
(paper.tex:7293–7310).

An inclusion is represented by an injective unital ring homomorphism.
`f.IsIntegral` says that every element of the target satisfies a monic
polynomial over the source, evaluated using exactly this map. `IsField`
uses the given ring operations and includes nontriviality. The second
statement allows arbitrary commutative rings, including zero rings;
maximal ideals are proper by definition. No localization is involved.
-/

universe u v

namespace Specs.D07.Ch22.LyingOverIntegralDomainFieldCriterion

/-- An integral inclusion of domains preserves and reflects being a field. -/
def IntegralDomainFieldCriterion : Prop :=
  ∀ (A : Type u) (D : Type v) [CommRing A] [CommRing D]
    [IsDomain A] [IsDomain D] (f : A →+* D),
    Function.Injective f → f.IsIntegral → (IsField A ↔ IsField D)

/-- Maximal ideals contract to maximal ideals under integral inclusions,
without domain assumptions on the ambient rings. -/
def MaximalContraction : Prop :=
  ∀ (R : Type u) (B : Type v) [CommRing R] [CommRing B]
    (f : R →+* B), Function.Injective f → f.IsIntegral →
    ∀ M : Ideal B, M.IsMaximal → (M.comap f).IsMaximal

end Specs.D07.Ch22.LyingOverIntegralDomainFieldCriterion
