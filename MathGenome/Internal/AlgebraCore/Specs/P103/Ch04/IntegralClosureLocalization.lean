import Mathlib.RingTheory.Localization.Algebra
import Mathlib.RingTheory.IntegralClosure.Algebra.Basic

/-!
The last assertion of Theorem 4.5, `paper.tex` 895–901.
All rings are commutative and unital. `Algebra R A` represents an arbitrary
unital ring map, with no injectivity or nontriviality assumption.
The denominators in A and in its integral closure are the images of S.
In particular S may contain zero.
-/
namespace P103.Ch04.IntegralClosureLocalization.Specs

universe u v

variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
  (S : Submonoid R)

/-- A denominator in S, viewed in the image submonoid in A. -/
def denominator (s : S) : Algebra.algebraMapSubmonoid A S :=
  ⟨algebraMap R A s, Algebra.mem_algebraMapSubmonoid_of_mem s⟩

/-- The fraction a/s in the localization of A at the image of S. -/
noncomputable def fraction (a : A) (s : S) :
    Localization (Algebra.algebraMapSubmonoid A S) :=
  IsLocalization.mk' _ a (denominator R A S s)

/-- The map induced by the actual inclusion of the integral closure into A.
Its coefficient ring is S⁻¹R, with the canonical localized algebra structures. -/
noncomputable def localizedInclusion :
    Localization (Algebra.algebraMapSubmonoid (integralClosure R A) S) →ₐ[Localization S]
      Localization (Algebra.algebraMapSubmonoid A S) :=
  IsLocalization.mapₐ S (Localization S) _ _ (integralClosure R A).val

/-- Localization preserves this inclusion, even if S contains zero. -/
def InjectiveType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R), Function.Injective (localizedInclusion R A S)

/-- Equality as subalgebras of the same ambient localization. -/
def ImageType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R),
    (localizedInclusion R A S).range =
      integralClosure (Localization S) (Localization (Algebra.algebraMapSubmonoid A S))

/-- An integral localized fraction has an integral numerator after multiplying
by two denominators. This formulation makes no cancellation assumption. -/
def ClearingType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (a : A) (s : S),
    IsIntegral (Localization S) (fraction R A S a s) →
      ∃ u t : S, IsIntegral R (((u * t : S) : R) • a) ∧
        fraction R A S a s = fraction R A S (((u * t : S) : R) • a) (u * t * s)

/-- The equivalent representative criterion, in both directions. -/
def RepresentationType : Prop :=
  ∀ (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Algebra R A]
    (S : Submonoid R) (a : A) (s : S),
    IsIntegral (Localization S) (fraction R A S a s) ↔
      ∃ (c : integralClosure R A) (t : S),
        fraction R A S a s = fraction R A S (c : A) t

end P103.Ch04.IntegralClosureLocalization.Specs
