import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.RingTheory.RingHom.FaithfullyFlat

universe u v

namespace DerivedFormalization.Specs.Descent

/-- A finite family generating the unit ideal gives a faithfully flat map to the product
of the localizations at its elements. -/
def localizationCoverFaithfullyFlat : Prop :=
  ∀ (A : Type u) [CommRing A] (ι : Type v) [Finite ι] (f : ι → A),
    Ideal.span (Set.range f) = ⊤ →
      (algebraMap A (∀ i : ι, Localization.Away (f i))).FaithfullyFlat

end DerivedFormalization.Specs.Descent
