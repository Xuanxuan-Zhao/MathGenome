import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralCentralQuotient
import Mathlib.RingTheory.DedekindDomain.Instances
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Localization.BaseChange

open scoped TensorProduct
open Algebra.TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.CentralCoverSpreading

noncomputable section

abbrev TorusCoordinates (R : Type u) [CommRing R] (I : Type) :=
  MonoidAlgebra R (ULift.{u} (Multiplicative (I → ℤ)))

abbrev KernelCoordinates (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :=
  MonoidAlgebra R (ULift.{u} (∀ i, Multiplicative (ZMod (n i))))

/-- Pullback on the character lattice of the marked power homomorphism. -/
def powerCharacters {I : Type} (n : I → ℕ) :
    ULift.{u} (Multiplicative (I → ℤ)) →* ULift.{u} (Multiplicative (I → ℤ)) :=
  MulEquiv.ulift.symm.toMonoidHom.comp
    ((show Multiplicative (I → ℤ) →* Multiplicative (I → ℤ) from
      { toFun := fun c => Multiplicative.ofAdd fun i => (n i : ℤ) * c.toAdd i
        map_one' := congrArg Multiplicative.ofAdd (funext fun i => mul_zero (n i : ℤ))
        map_mul' := fun c d => congrArg Multiplicative.ofAdd
          (funext fun i => mul_add (n i : ℤ) (c.toAdd i) (d.toAdd i)) }).comp
      MulEquiv.ulift.toMonoidHom)

abbrev powerPullback (R : Type u) [CommRing R] {I : Type} (n : I → ℕ) :
    TorusCoordinates R I →ₐc[R] TorusCoordinates R I :=
  MonoidAlgebra.mapDomainBialgHom R (powerCharacters n)

/-- The full kernel is the fibre over the counit, expressed by its ideal in
the source coordinate algebra. -/
def IsFullKernel {R B C N : Type u} [CommRing R] [CommRing B] [CommRing C] [CommRing N]
    [HopfAlgebra R B] [HopfAlgebra R C] [HopfAlgebra R N]
    (q : B →ₐc[R] C) (j : C →ₐc[R] N) : Prop :=
  Function.Surjective j ∧
    RingHom.ker j.toAlgHom.toRingHom =
      (RingHom.ker (Bialgebra.counitAlgHom R B).toRingHom).map q.toAlgHom.toRingHom

/-- Coordinate maps of the marked diagram. The generic isomorphisms of the
two tori and of the kernel are used as coordinates, so all three of those
objects have their specified group algebras as coordinate rings. -/
structure Diagram (R B C : Type u) [CommRing R] [CommRing B] [CommRing C]
    [HopfAlgebra R B] [HopfAlgebra R C] {I : Type} (n : I → ℕ) where
  cover : B →ₐc[R] C
  sourceTorus : C →ₐc[R] TorusCoordinates R I
  targetTorus : B →ₐc[R] TorusCoordinates R I
  kernel : C →ₐc[R] KernelCoordinates R n
  sourceTorusClosed : Function.Surjective sourceTorus
  targetTorusClosed : Function.Surjective targetTorus
  torusSquare : sourceTorus.comp cover = (powerPullback R n).comp targetTorus
  kernelFull : IsFullKernel cover kernel
  kernelCentral : IntegralCentralQuotient.IsCentral kernel

section BaseChange

variable (R E : Type u) [CommRing R] [CommRing E] [Algebra R E]

/-- Comparison on the tensor square of coordinate algebras when extending the
coefficient ring. -/
def tensorComparison {B B' C C' : Type u} [CommRing B] [CommRing B'] [CommRing C]
    [CommRing C'] [Algebra R B] [Algebra R C] [Algebra R B'] [Algebra R C']
    [Algebra E B'] [Algebra E C'] [IsScalarTower R E B'] [IsScalarTower R E C']
    (b : B →ₐ[R] B') (c : C →ₐ[R] C') :
    B ⊗[R] C →ₐ[R] B' ⊗[E] C' :=
  lift (((includeLeft : B' →ₐ[E] B' ⊗[E] C').restrictScalars R).comp b)
    (((includeRight : C' →ₐ[E] B' ⊗[E] C').restrictScalars R).comp c)
    (fun _ _ => Commute.all _ _)

/-- A generic fibre identification in coordinates. The base-change field
asserts the actual tensor-product isomorphism, and the other fields identify
the group operations under it. -/
structure GenericFibre (B B' : Type u) [CommRing B] [CommRing B'] [HopfAlgebra R B]
    [HopfAlgebra E B'] [Algebra R B'] [IsScalarTower R E B'] where
  inclusion : B →ₐ[R] B'
  baseChange : IsBaseChange E inclusion.toLinearMap
  comul : ∀ b : B,
    tensorComparison R E inclusion inclusion (Bialgebra.comulAlgHom R B b) =
      Bialgebra.comulAlgHom E B' (inclusion b)
  counit : ∀ b : B,
    algebraMap R E (Bialgebra.counitAlgHom R B b) = Bialgebra.counitAlgHom E B' (inclusion b)
  antipode : ∀ b : B,
    inclusion (HopfAlgebra.antipodeAlgHom R B b) = HopfAlgebra.antipodeAlgHom E B' (inclusion b)

end BaseChange

/-- The two marked group algebras extend coefficients by the scalar map. -/
def groupAlgebraInclusion (R E M : Type u) [CommRing R] [CommRing E] [Algebra R E]
    [CommGroup M] : MonoidAlgebra R M →ₐ[R] MonoidAlgebra E M :=
  MonoidAlgebra.lift R (MonoidAlgebra E M) M (MonoidAlgebra.of E M)

section Spreading

variable {A E B C D : Type u} [CommRing A] [Field E] [Algebra A E]
  [CommRing B] [CommRing C] [HopfAlgebra E B] [HopfAlgebra E C] [CommRing D] [Algebra A D]
  {I : Type} {n : I → ℕ}

set_option linter.unusedVariables false in
/-- Models over one principal localization, with generic fibre identifications
compatible with every map in the diagram and with the ambient immersion. -/
structure IntegralDiagram (generic : Diagram E B C n)
    (ambient : E ⊗[A] D →ₐ[E] B) (R : Type u) [CommRing R] [Algebra A R] [Algebra R E]
    [IsScalarTower A R E] [Algebra R B] [Algebra R C] [IsScalarTower R E B]
    [IsScalarTower R E C] where
  target : Type u
  source : Type u
  [targetRing : CommRing target]
  [sourceRing : CommRing source]
  [targetHopf : HopfAlgebra R target]
  [sourceHopf : HopfAlgebra R source]
  diagram : Diagram R target source n
  targetPresentation : Algebra.FinitePresentation R target
  sourcePresentation : Algebra.FinitePresentation R source
  torusPresentation : Algebra.FinitePresentation R (TorusCoordinates R I)
  kernelPresentation : Algebra.FinitePresentation R (KernelCoordinates R n)
  targetFlat : Module.Flat R target
  coverFinite : letI := diagram.cover.toAlgHom.toAlgebra; Module.Finite target source
  coverFaithfullyFlat : letI := diagram.cover.toAlgHom.toAlgebra; Module.FaithfullyFlat target source
  coverPresentation : letI := diagram.cover.toAlgHom.toAlgebra; Algebra.FinitePresentation target source
  coverTorsor : IntegralCentralQuotient.IsRightTorsor diagram.cover diagram.kernel
  ambientMap : R ⊗[A] D →ₐ[R] target
  ambientClosed : Function.Surjective ambientMap
  genericTarget : GenericFibre R E target B
  genericSource : GenericFibre R E source C
  coverAgrees : ∀ x : target,
    genericSource.inclusion (diagram.cover x) = generic.cover (genericTarget.inclusion x)
  sourceTorusAgrees : ∀ x : source,
    groupAlgebraInclusion R E _ (diagram.sourceTorus x) =
      generic.sourceTorus (genericSource.inclusion x)
  targetTorusAgrees : ∀ x : target,
    groupAlgebraInclusion R E _ (diagram.targetTorus x) =
      generic.targetTorus (genericTarget.inclusion x)
  kernelAgrees : ∀ x : source,
    groupAlgebraInclusion R E _ (diagram.kernel x) = generic.kernel (genericSource.inclusion x)
  ambientAgrees : ∀ x : D,
    genericTarget.inclusion (ambientMap (1 ⊗ₜ[A] x)) = ambient (1 ⊗ₜ[A] x)

/-- Spread the centrally covered affine group, its marked split tori and full
kernel, and the prescribed closed immersion into the fixed affine ambient scheme. -/
def Statement : Prop :=
  ∀ (A E : Type u) [CommRing A] [IsDedekindDomain A] [Field E] [Algebra A E]
    [IsFractionRing A E] (B C D : Type u) [CommRing B] [CommRing C]
    [HopfAlgebra E B] [HopfAlgebra E C] [Algebra.FiniteType E B] [Algebra.FiniteType E C]
    [CommRing D] [Algebra A D] [Algebra.FinitePresentation A D]
    (I : Type) [Fintype I] (n : I → ℕ), (∀ i, 0 < n i) →
    ∀ (generic : Diagram E B C n) (ambient : E ⊗[A] D →ₐ[E] B),
    Function.Surjective ambient →
    (letI := generic.cover.toAlgHom.toAlgebra; Module.Finite B C) →
    (letI := generic.cover.toAlgHom.toAlgebra; Module.FaithfullyFlat B C) →
    ∃ d : A, d ≠ 0 ∧
    ∃ rE : Algebra (Localization.Away d) E,
      letI := rE
      ∃ h : IsScalarTower A (Localization.Away d) E,
      letI := h
      letI : Algebra (Localization.Away d) B := ((algebraMap E B).comp (algebraMap _ E)).toAlgebra
      letI : Algebra (Localization.Away d) C := ((algebraMap E C).comp (algebraMap _ E)).toAlgebra
      letI : IsScalarTower (Localization.Away d) E B := IsScalarTower.of_algebraMap_eq' rfl
      letI : IsScalarTower (Localization.Away d) E C := IsScalarTower.of_algebraMap_eq' rfl
      Nonempty (IntegralDiagram generic ambient (Localization.Away d))

end Spreading

end

end LinearAlgebraicGroups.Specs.CentralCoverSpreading
