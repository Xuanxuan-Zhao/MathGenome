import Mathlib.LinearAlgebra.Basis.Defs
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.TensorProduct.Basic

open Module
open scoped TensorProduct

namespace LinearAlgebraicGroups.Specs

universe u v

/-- A principal localization at a nonzero base element has a nonempty basis
over the localized base, with the scalar action induced by localization. -/
def hasFreeLocalization (A : Type u) (B : Type v) [CommRing A] [CommRing B]
    [Algebra A B] : Prop :=
  ∃ s : A, s ≠ 0 ∧
    letI : Algebra (Localization.Away s) (Localization.Away (algebraMap A B s)) :=
      localizationAlgebra (Submonoid.powers s) B
    ∃ ι : Type, Nonempty ι ∧
      Nonempty (Basis ι (Localization.Away s) (Localization.Away (algebraMap A B s)))

/-- Generic freeness for a finite-type algebra with nonzero generic fiber. -/
def genericFreeness : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B],
    Nontrivial (FractionRing A ⊗[A] B) → hasFreeLocalization A B

/-- Generic freeness for an inclusion, as used on the affine charts in the source. -/
def genericFreeness_of_injective : Prop :=
  ∀ {A : Type u} {B : Type v} [CommRing A] [IsDomain A] [CommRing B] [Algebra A B]
    [Algebra.FiniteType A B],
    Function.Injective (algebraMap A B) → hasFreeLocalization A B

end LinearAlgebraicGroups.Specs
