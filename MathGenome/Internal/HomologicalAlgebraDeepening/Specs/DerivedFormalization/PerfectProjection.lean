import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.DerivedHomComparisonMaps
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectComplex

/-! Projection through a perfect factor (U11). -/

namespace Specs.DerivedFormalization.PerfectProjection

open CategoryTheory
open Cochains (derivedValue)
open CochainTensorTransport (AdequateModel)
open DerivedHomAdjunction (Closed)
open DerivedHomModels (Models)
open PerfectComplex (isPerfectValue)
open DerivedHomComparisonMaps (projectionComparisonValue ProjectionNaturality)

universe u a

attribute [local instance] HasDerivedCategory.standard

/-- The natural tensor-evaluation comparison is invertible when the tensor
factor has a bounded finite projective representative. -/
def ProjectionIsomorphism : Prop :=
  ProjectionNaturality.{u,a} ∧
    ∀ {R : Type u} [CommRing R] {A : Type a} [CommRing A] {e : R ≃+* A}
      {M : AdequateModel e} {T : DerivedTensor.Model M} {H : Models.{u,a} R}
      (c : Closed T H) (P X Y : derivedValue.{a} R),
      isPerfectValue P → IsIso (projectionComparisonValue c P X Y)

end Specs.DerivedFormalization.PerfectProjection
