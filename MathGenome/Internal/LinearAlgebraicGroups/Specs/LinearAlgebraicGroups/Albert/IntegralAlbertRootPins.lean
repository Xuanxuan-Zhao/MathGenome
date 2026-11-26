import MathGenome.Internal.LinearAlgebraicGroups.Specs.LinearAlgebraicGroups.Classification.IntegralRecognition

open AlgebraicGeometry WithConv
open scoped TensorProduct

universe u

namespace LinearAlgebraicGroups.Specs.IntegralAlbertRootPins

open IntegralCentralQuotient (IntegralRing HopfSpectrum)
open IntegralRecognition (Tangent dualCoefficients HasWeight IsWeightBasis)
open Pinning (BasedRootDatum)

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {R A X : Type u} [CommRing R] [CommRing A] [HopfAlgebra R A] [CommGroup X]

local notation "ε" => Bialgebra.counitAlgHom R A
local notation "H" => MonoidAlgebra R X

/-- The cotangent module at the identity. -/
abbrev IdentityCotangent (R A : Type u) [CommRing R] [CommRing A] [HopfAlgebra R A] :=
  (RingHom.ker (Bialgebra.counitAlgHom R A).toRingHom).Cotangent

/-- Project functions onto the augmentation ideal along the constants. -/
def augmentationPart : A →ₗ[R] RingHom.ker (ε).toRingHom :=
  LinearMap.codRestrict ((RingHom.ker (ε).toRingHom).restrictScalars R)
    ((LinearMap.id : A →ₗ[R] A) - (Algebra.linearMap R A).comp (ε).toLinearMap) fun a => by
    change ε (a - algebraMap R A (ε a)) = 0
    rw [map_sub, AlgHom.commutes]
    exact sub_self _

/-- The universal differential of a function at the identity. -/
def identityDifferential : A →ₗ[R] IdentityCotangent R A :=
  ((RingHom.ker (ε).toRingHom).toCotangent.restrictScalars R).comp augmentationPart

/-- Pullback along conjugation by the universal torus element. -/
def conjugationPullback (t : A →ₐc[R] H) : A →ₐ[R] A ⊗[R] H :=
  let g : A →ₐ[R] A ⊗[R] H := Algebra.TensorProduct.includeRight.comp t.toAlgHom
  (toConv g * toConv (Algebra.TensorProduct.includeLeft : A →ₐ[R] _) *
    toConv (g.comp (HopfAlgebra.antipodeAlgHom R A))).ofConv

/-- The coefficient of the indicated character in the universal conjugation pullback. -/
def characterProjection (t : A →ₐc[R] H) (χ : X) : A →ₗ[R] A :=
  (TensorProduct.rid R A).toLinearMap ∘ₗ
    TensorProduct.map LinearMap.id ((Finsupp.lapply χ).comp
      (MonoidAlgebra.coeffLinearEquiv R).toLinearMap) ∘ₗ
    (conjugationPullback t).toLinearMap

/-- Functionals whose differential sees only the indicated character component. -/
def WeightSpace (t : A →ₐc[R] H) (χ : X) (S : Type u) [CommRing S] [Algebra R S] :
    Submodule S (IdentityCotangent R A →ₗ[R] S) where
  carrier := {f | ∀ a, f (identityDifferential (characterProjection t χ a)) =
    f (identityDifferential a)}
  zero_mem' := fun _ => rfl
  add_mem' hf hg a := congrArg₂ (· + ·) (hf a) (hg a)
  smul_mem' c _ hf a := congrArg (c • ·) (hf a)

/-- The recognition weight equation on the base-changed group and torus, using the
base-changed monomial to evaluate the character. -/
def HasExtendedWeight (t : A →ₐc[R] H) (χ : X) (S : Type u) [CommRing S] [Algebra R S]
    (v : Tangent S (S ⊗[R] A)) : Prop :=
  ∀ (B : CommAlgCat.{u} S) (s : S ⊗[R] H →ₐ[S] B),
    let tS := Bialgebra.TensorProduct.map (BialgHom.id S S) t
    let g := toConv ((TrivSqZeroExt.inlAlgHom S B B).comp (s.comp tS.toAlgHom))
    let p := (dualCoefficients B).comp v.val
    let c := s ((1 : S) ⊗ₜ[R] MonoidAlgebra.of R X χ)
    let scale := (TrivSqZeroExt.map (c • (LinearMap.id : B →ₗ[B] B))).restrictScalars S
    g * toConv p * toConv (g.ofConv.comp (HopfAlgebra.antipodeAlgHom S (S ⊗[R] A))) =
      toConv (scale.comp p)

/-- The weight module is a direct summand and has canonical scalar extension,
with both integral and extended weights identified by their dual-number slopes. -/
def WeightBaseChange : Prop :=
  ∀ {R A X : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    [CommRing A] [HopfAlgebra R A] [CommGroup X]
    (t : A →ₐc[R] MonoidAlgebra R X) (χ : X),
    Algebra.FinitePresentation R A →
    Smooth (HopfSpectrum R A).X.hom →
    Function.Surjective t →
    (∃ P : Submodule R (IdentityCotangent R A →ₗ[R] R),
      IsCompl (WeightSpace t χ R) P) ∧
    (∀ v : Tangent R A, HasWeight t χ v ↔
      ∃! f : WeightSpace t χ R, ∀ a, (v.val a).snd = f.val (identityDifferential a)) ∧
    (∀ f : WeightSpace t χ R,
      ∃! v : Tangent R A, HasWeight t χ v ∧
        ∀ a, (v.val a).snd = f.val (identityDifferential a)) ∧
    ∀ (S : Type u) [CommRing S] [Algebra R S],
      (∃ e : (S ⊗[R] WeightSpace t χ R) ≃ₗ[S] WeightSpace t χ S,
        ∀ s f z, (e (s ⊗ₜ[R] f)).val z = s * algebraMap R S (f.val z)) ∧
      (∀ v : Tangent S (S ⊗[R] A), HasExtendedWeight t χ S v ↔
        ∃! f : WeightSpace t χ S, ∀ a,
          (v.val ((1 : S) ⊗ₜ[R] a)).snd = f.val (identityDifferential a)) ∧
      (∀ f : WeightSpace t χ S,
        ∃! v : Tangent S (S ⊗[R] A), HasExtendedWeight t χ S v ∧
          ∀ a, (v.val ((1 : S) ⊗ₜ[R] a)).snd = f.val (identityDifferential a))

/-- One-dimensional geometric generic weights admit simultaneous choices of integral
pins for a finite family of characters. -/
def PinChoices : Prop :=
  ∀ {A X J : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A] [CommGroup X] [Finite J]
    (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} X) (χ : J → X),
    Algebra.FinitePresentation IntegralRing.{u} A →
    Smooth (HopfSpectrum IntegralRing.{u} A).X.hom →
    Function.Surjective t →
    ∀ (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra IntegralRing.{u} K],
      (∀ j, Module.finrank K (WeightSpace t (χ j) K) = 1) →
      ∃ pin : J → Tangent IntegralRing.{u} A, ∀ j, IsWeightBasis t (χ j) (pin j)

/-- Simple-root pins with the indices and characters used by integral recognition. -/
def SimpleRootPins : Prop :=
  ∀ {D : BasedRootDatum.{u}} {A : Type u} [CommRing A] [HopfAlgebra IntegralRing.{u} A]
    (t : A →ₐc[IntegralRing.{u}] MonoidAlgebra IntegralRing.{u} (Multiplicative D.X)),
    Algebra.FinitePresentation IntegralRing.{u} A →
    Smooth (HopfSpectrum IntegralRing.{u} A).X.hom →
    Function.Surjective t →
    ∀ (K : Type u) [Field K] [CharZero K] [IsAlgClosed K] [Algebra IntegralRing.{u} K],
      (∀ i : ↥D.base.support,
        Module.finrank K (WeightSpace t (Multiplicative.ofAdd (D.datum.root i.val)) K) = 1) →
      ∃ pin : ↥D.base.support → Tangent IntegralRing.{u} A,
        ∀ i : ↥D.base.support, IsWeightBasis t (Multiplicative.ofAdd (D.datum.root i.val)) (pin i)

end

end LinearAlgebraicGroups.Specs.IntegralAlbertRootPins
