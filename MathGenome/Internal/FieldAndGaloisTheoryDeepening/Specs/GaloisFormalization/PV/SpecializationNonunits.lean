import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.RingTheory.FiniteType

namespace Specs.GaloisFormalization.PV

universe u v

/-- Only finitely many base-field translates of a transcendental element are units. -/
def finite_unit_specializations : Prop :=
  ∀ {F : Type u} {B : Type v} [Field F] [Infinite F] [CommRing B] [IsDomain B]
    [Algebra F B] [Algebra.FiniteType F B] (t : B),
    Transcendental F t → Set.Finite {a : F | IsUnit (t - algebraMap F B a)}

end Specs.GaloisFormalization.PV
