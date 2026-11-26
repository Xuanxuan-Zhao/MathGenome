import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Arithmetic.SplitAlbertLocalForms
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

open CategoryTheory
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Arithmetic.F4LiftedChevalleySpecification

open LinearAlgebraicGroups.Specs
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification)
open IntegralCentralQuotient (HopfSpectrum)
open IntegralSemisimpleModel (Integers fibre)
open Pinning (SplitBorelPair AttachedDatum)
open SplitAlbertLocalFormsSpecification (HasF4Cartan)

/-- The scalar map between the two copies of the integers. -/
abbrev integerLift : Algebra Integers.{0} Integers.{u} :=
  ((ULift.ringEquiv : Integers.{u} ≃+* ℤ).symm.toRingHom.comp
    (ULift.ringEquiv : Integers.{0} ≃+* ℤ).toRingHom).toAlgebra

attribute [local instance] integerLift

private noncomputable abbrev hopfBaseExtension
    (R₀ : Type) [CommRing R₀] (R : Type u) [CommRing R] [Algebra R₀ R]
    (A : Type) [CommRing A] [HopfAlgebra R₀ A] :
    Grp (IntegralCentralQuotient.OverBase R) :=
  HopfSpectrum R (R ⊗[R₀] A)

/-- The scalar extension of the supplied coordinate Hopf algebra to the raised universe. -/
noncomputable abbrev liftedGroup (A : Type) [CommRing A] [HopfAlgebra Integers.{0} A] :=
  hopfBaseExtension Integers.{0} Integers.{u} A

/-- Each field fibre of the given lifted Chevalley model has a split Borel pair
with its full attached based root system of type F₄. -/
def Statement : Prop :=
  ∀ (S : IntegralSplitIdentification) (A : Type) [CommRing A] [HopfAlgebra Integers.{0} A],
    (HopfSpectrum Integers.{0} A ≅ S.chevalley.group) →
    ∀ (k : Type u) [Field k],
      ∃ (P : SplitBorelPair k) (D : AttachedDatum P),
        HasF4Cartan D.toBased ∧ D.toBased.datum.IsRootSystem ∧
          Nonempty (P.G.val ≅ (fibre k).obj (liftedGroup.{u} A))

end LinearAlgebraicGroups.Arithmetic.F4LiftedChevalleySpecification
