import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.CochainCoefficientLift
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.InjectiveTruncationTower
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KInjectiveReplacement
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.TowerExactSequence

namespace Specs.DerivedFormalization.KInjectiveReplacementTransport

open CategoryTheory CategoryTheory.Limits Opposite
open Cochains (compValue qValue)
open CochainModels (isKInjectiveValue)
open InjectiveTruncationTower (stage projection)
open CochainCoefficientLift (lift liftD fromOriginal fromOriginalCohomology)
open TowerExactSequence (transition)

noncomputable section

/-- The canonical cutoff quotient comparison for the exact coefficient lift. -/
abbrev cutoffIso.{v, u, t} {R : Type u} [CommRing R] (X : compValue.{v} R) (i : ℤ) :
    (ModuleCat.uliftFunctor.{max u t, v} R).obj ((X.truncGE i).X i) ≅
      (((lift.{max u t, v} R).obj X).truncGE i).X i :=
  (ModuleCat.uliftFunctor.{max u t, v} R).mapIso (X.truncGEXIsoOpcycles i) ≪≫
    ((X.sc i).mapOpcyclesIso (ModuleCat.uliftFunctor.{max u t, v} R)).symm ≪≫
    (((lift.{max u t, v} R).obj X).truncGEXIsoOpcycles i).symm

/-- The exact lift identifies the cutoff quotient, the original terms above it,
and the zero terms below it. -/
def TruncationComponents.{v, u, t} {R : Type u} [CommRing R]
    (X : compValue.{v} R) (n : ℕ)
    (e : (lift.{max u t, v} R).obj (stage X n) ≅ stage ((lift.{max u t, v} R).obj X) n) :
    Prop :=
  let a := -(n : ℤ)
  let L := lift.{max u t, v} R
  e.hom.f a = (cutoffIso.{v, u, t} X a).hom ∧
    (∀ i (hi : a < i), e.hom.f i =
      ((ModuleCat.uliftFunctor.{max u t, v} R).mapIso (X.truncGEXIso a i hi) ≪≫
        ((L.obj X).truncGEXIso a i hi).symm).hom) ∧
    ∀ i, i < a → e.hom.f i = 0

/-- The strict injective tower and its limit over the same ring, starting with
the actual original good truncation tower. -/
def liftedReplacementType.{v, u, t} : Prop :=
  ∀ {R : Type u} [CommRing R] (X : compValue.{v} R),
    let L := lift.{max u t, v} R
    let Y := L.obj X
    ∃ (s : ∀ n : ℕ, stage X (n + 1) ⟶ stage X n)
      (s' : ∀ n : ℕ, stage Y (n + 1) ⟶ stage Y n)
      (π : (Functor.const ℕᵒᵖ).obj X ⟶ Functor.ofOpSequence s)
      (π' : (Functor.const ℕᵒᵖ).obj Y ⟶ Functor.ofOpSequence s')
      (e : Functor.ofOpSequence s ⋙ L ≅ Functor.ofOpSequence s'),
      (∀ n : ℕ, π.app (op n) = projection X n ∧ π'.app (op n) = projection Y n ∧
        L.map (π.app (op n)) ≫ e.hom.app (op n) = π'.app (op n) ∧
        TruncationComponents.{v, u, t} X n (e.app (op n))) ∧
      (∀ n : ℕ, ∀ i : ℤ, Function.Surjective ((s n).f i) ∧
        Function.Surjective ((s' n).f i)) ∧
      Nonempty (IsLimit (Cone.mk X π)) ∧
      Nonempty (IsLimit ((Cone.postcompose e.hom).obj (L.mapCone (Cone.mk X π)))) ∧
      Nonempty (IsLimit (Cone.mk Y π')) ∧
      ∃ (J : ℕᵒᵖ ⥤ compValue.{max u v t} R) (ι : Functor.ofOpSequence s' ⟶ J),
        (∀ n : ℕ, (J.obj (op n)).IsStrictlyGE (-(n : ℤ)) ∧
          (∀ i : ℤ, Injective ((J.obj (op n)).X i)) ∧
          (∀ i : ℤ, Mono ((ι.app (op n)).f i)) ∧ QuasiIso (ι.app (op n))) ∧
        (∀ (n : ℕ) (i : ℤ), ∃ σ : (J.obj (op n)).X i ⟶ (J.obj (op (n + 1))).X i,
          σ ≫ (transition J n).f i = 𝟙 _) ∧
        ∃ f : Y ⟶ limit J,
          (∀ n : ℕ, f ≫ limit.π J (op n) = π'.app (op n) ≫ ι.app (op n)) ∧
          (∀ i : ℤ, Mono (f.f i)) ∧ QuasiIso f ∧ isKInjectiveValue (limit J) ∧
          (∀ i : ℤ, Injective ((limit J).X i)) ∧
          (∀ i : ℤ, Function.Injective ((fromOriginal.{max u t} f).f i)) ∧
          (∀ i : ℤ, Function.Bijective (fromOriginalCohomology.{max u t} f i)) ∧
          Nonempty ((liftD.{max u t, v} R).obj ((qValue.{v} R).obj X) ≅
            (qValue.{max u v t} R).obj (limit J))

/-- When the ring is small in the original module universe, the native result
holds in that universe via its small representative. -/
def smallReplacementType.{v, u} : Prop :=
  ∀ {R : Type u} [CommRing R] [Small.{v} R] (X : compValue.{v} R),
    ∃ (I : compValue.{v} R) (f : X ⟶ I),
      (∀ i : ℤ, Mono (f.f i)) ∧ QuasiIso f ∧ isKInjectiveValue I ∧
        ∀ i : ℤ, Injective (I.X i)

/-- Unbounded injective replacement with an independently sized original input,
together with the native adequate and small-ring cases. -/
def replacementTransportType.{v, u, t} : Prop :=
  liftedReplacementType.{v, u, t} ∧
    KInjectiveReplacement.replacementType.{u, v} ∧ smallReplacementType.{v, u}

end

end Specs.DerivedFormalization.KInjectiveReplacementTransport
