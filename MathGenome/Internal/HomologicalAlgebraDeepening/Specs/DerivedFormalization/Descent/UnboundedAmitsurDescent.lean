import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic

/-! Unbounded Amitsur descent for cochain complexes of modules. -/

namespace Specs.DerivedFormalization.Descent.UnboundedAmitsurDescent

open CategoryTheory
open AmitsurTotalComplexSpec.Independent (Input augmentation functor)
open Specs.DerivedFormalization.Cochains (qValue)
open Specs.DerivedFormalization.Descent.AmitsurHorizontalLimit (towerFunctor toHolim)
open Specs.DerivedFormalization.SequentialHomotopyLimits (holimValue)

universe u v w

/-- The natural augmentation is a quasi-isomorphism for every coefficient
complex over a faithfully flat base change. -/
def AugmentationQuasiIso : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B]
    [Module.FaithfullyFlat A B] (X : Input.{u, w} A),
    QuasiIso (augmentation.{u, v, w} A B X)

/-- In the derived category the canonical comparison identifies the product
totalization with the shifted-cone homotopy limit of the finite-column quotients. -/
def DerivedHolimComparison : Prop :=
  ∀ (A : Type u) (B : Type v) [CommRing A] [CommRing B] [Algebra A B],
    ∃ e : functor.{u, v, w} A B ⋙ qValue A ≅ (towerFunctor A B ⋙ holimValue) ⋙ qValue A,
      ∀ X, e.hom.app X = (qValue A).map (toHolim A B X)

end Specs.DerivedFormalization.Descent.UnboundedAmitsurDescent
