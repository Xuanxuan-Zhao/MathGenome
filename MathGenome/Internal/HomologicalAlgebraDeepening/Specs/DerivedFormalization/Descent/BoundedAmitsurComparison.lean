import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurTotalComplex
import Mathlib.Algebra.Homology.Embedding.CochainComplex
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Bounded-below comparison for the Amitsur product totalization. -/

namespace BoundedAmitsurComparisonSpec

open AmitsurTotalComplexSpec.Independent

universe u v w

/-- The Amitsur augmentation for the original coefficient complex is a
quasi-isomorphism when its terms vanish below an integer bound. -/
def AugmentationQuasiIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (X : Input.{u, w} A)
    (lower : ℤ), X.IsStrictlyGE lower → QuasiIso (augmentation.{u, v, w} A B X)

end BoundedAmitsurComparisonSpec
