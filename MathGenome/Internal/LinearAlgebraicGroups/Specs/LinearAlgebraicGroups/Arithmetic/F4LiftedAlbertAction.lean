import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Albert.AutomorphismType
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.RelativeFormComparison
import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Descent.SemilinearVectorSpaces
import Mathlib.RingTheory.HopfAlgebra.TensorProduct

namespace LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertActionSpecification

open CategoryTheory
open LinearAlgebraicGroups.Specs
open IntegralSemisimpleModel (Integers fibre)
open IntegralCentralQuotient (HopfSpectrum)
open RelativeFormComparison (fieldTest fieldMap)
open Albert.AutomorphismTypeSpecification (IntegralSplitIdentification)
open Albert.SplitSpecification (ParaQuadratic SplitRank IsSplitModel)
open Albert.IntrinsicCubicSpecification (SplitChart)
open Descent (SemilinearAction)
open scoped TensorProduct CategoryTheory.MonObj

universe u

/-- The inclusion of the small copy of the integers into the lifted copy. -/
abbrev integerLift : Algebra Integers.{0} Integers.{u} :=
  (ULift.ringEquiv.symm.toRingHom.comp ULift.ringEquiv.toRingHom).toAlgebra

attribute [local instance] integerLift

/-- The coordinate ring after extension to the lifted integers. The explicit
instance declarations fix the two universe levels of the tensor factors. -/
abbrev LiftedCoordinates (A : Type) [CommRing A] [Algebra Integers.{0} A] :=
  @TensorProduct Integers.{0} _ Integers.{u} A _ _
    (@Algebra.toModule _ _ _ _ integerLift) (@Algebra.toModule _ _ _ _ ‹Algebra Integers.{0} A›)

abbrev liftedCommRing (A : Type) [CommRing A] [Algebra Integers.{0} A] :
    CommRing (LiftedCoordinates.{u} A) :=
  Algebra.TensorProduct.instCommRing (R := Integers.{0}) (A := Integers.{u}) (B := A)

attribute [local instance] liftedCommRing

noncomputable abbrev liftedHopf (A : Type) [CommRing A] [HopfAlgebra Integers.{0} A] :
    HopfAlgebra Integers.{u} (LiftedCoordinates.{u} A) :=
  TensorProduct.instHopfAlgebra (R := Integers.{0}) (S := Integers.{u}) (A := A) (B := Integers.{u})

attribute [local instance] liftedHopf

/-- The actual field fibre of the lifted integral Hopf spectrum acts on the
split quadratic Albert law, compatibly with scalar Galois automorphisms. -/
def Statement : Prop :=
  ∀ (S : IntegralSplitIdentification) (A : Type) [CommRing A] [HopfAlgebra Integers.{0} A],
    (HopfSpectrum Integers.{0} A ≅ S.chevalley.group) →
    ∀ (k K : Type u) [Field k] [Field K] [Algebra k K],
      let H := (fibre k).obj (HopfSpectrum Integers.{u} (LiftedCoordinates.{u} A))
      let M := SplitRank.octonion.Model k
      ∃ (J : ParaQuadratic k M) (_ : SplitChart J K),
        IsSplitModel J .octonion ∧
        ∃ a : (fieldTest k K ⟶ H.X) →* (K ⊗[k] M ≃ₗ[K] K ⊗[k] M),
          Function.Injective a ∧
          Set.range a = {g | g (1 ⊗ₜ[k] J.unit) = 1 ⊗ₜ[k] J.unit ∧
            ∀ x y, g (J.op K x y) = J.op K (g x) (g y)} ∧
          ∀ σ p x, (SemilinearAction.scalarExtension M).act σ (a p x) =
            a (fieldMap k K σ ≫ p) ((SemilinearAction.scalarExtension M).act σ x)

end LinearAlgebraicGroups.Arithmetic.F4LiftedAlbertActionSpecification
