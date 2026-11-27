import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.KoszulRelativeDual
import MathGenome.Internal.HomologicalAlgebraDeepening.Specs.DerivedFormalization.PerfectRelativeDual

/-! Duality for a quotient by a finite regular sequence. -/

noncomputable section

namespace Specs.DerivedFormalization.RegularQuotientDuality

open CategoryTheory
open Cochains (compValue derivedValue qValue stalkValue derivedStalkValue
  derivedCohomologyValue cohomologyFactorsValue)
open CochainModels (isKInjectiveValue)
open CochainCoefficientLift (lift liftD liftDFactors)
open CochainRingTransport (uliftRingEquivValue)
open CochainTensor (tensor isKFlat)
open CochainTensorTransport (AdequateModel representedUnit)
open DerivedCoinduction (Coinduction comparison)
open DerivedScalarExtension (Extension)
open KoszulRelativeDual (determinantDual determinantModule scalarStalk coinduced
  ModelComparison TopIdentification singleShift)
open PerfectRelativeDual (source sourceModel targetAugmentation chainComparison)
open ScalarExtensionTransport (ModelStability)
open _root_.AdvCommAlg.Koszul (listIdeal)

universe u v

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A]
variable (J : Ideal A)
variable {A' B' : Type (max u v)} [CommRing A'] [CommRing B']
variable (e : A ≃+* A') {d : (A ⧸ J) ≃+* B'}

/-- The two presentations of A[0] agree by the inverse of the representative ring equivalence. -/
def unitPresentation : representedUnit e ≅ scalarStalk.{u,v} (A := A) :=
  let l : CochainRingTransport.rankOneValue e ≃ₗ[A] ModuleCat.of A (ULift.{v} A) :=
    { toFun := fun x => ULift.up (e.symm (show A' from x))
      invFun := fun x => e x.down
      left_inv := fun x => e.apply_symm_apply x
      right_inv := fun x => by
        cases x
        simp
      map_add' := fun x y => congrArg ULift.up (e.symm.map_add x y)
      map_smul' := fun r x => by
        change ULift.up (e.symm (e r * (show A' from x))) = ULift.up (r * e.symm x)
        rw [map_mul, e.symm_apply_apply] }
  (stalkValue A).mapIso l.toModuleIso

/-- The dual of the conormal determinant in cochain degree c. -/
abbrev determinantObject (c : ℕ) : derivedValue.{max u v} (A ⧸ J) :=
  ((derivedStalkValue.{max u v} (A ⧸ J)).obj
    (determinantModule.{u,v} J c))⟦-(c : ℤ)⟧

/-- The determinant identification is normalized by reduction of the top Koszul pairing
in every regular presentation of the ideal. -/
def IdentifiesDeterminant (G : Coinduction.{max u v} (Ideal.Quotient.mk J)) (c : ℕ)
    (δ : KoszulRelativeDual.relativeDual J G ≅ determinantObject.{u,v} J c) : Prop :=
  ∀ (b : List A) (hb : listIdeal b = J) (hlen : b.length = c),
    RingTheory.Sequence.IsRegular A b →
  ∀ (I : compValue.{max u v} A) (i : scalarStalk.{u,v} (A := A) ⟶ I)
    (hi : QuasiIso i) (hI : isKInjectiveValue I) (C : ModelComparison J b hb i),
    let M := determinantModule.{u,v} J c
    let H := derivedCohomologyValue (A ⧸ J) (c : ℤ)
    let ei := @asIso _ _ _ _ ((qValue A).map i)
      ((DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) i).2 hi)
    let eI := G.modelIso (Ideal.Quotient.mk J) I ei hI
    let eTop := ((cohomologyFactorsValue (A ⧸ J) (c : ℤ)).app (coinduced J I)).symm ≪≫
      (H.mapIso eI).symm ≪≫ H.mapIso (δ ≪≫ ((singleShift J c).app M).symm) ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} (A ⧸ J)) (c : ℤ)).app M
    TopIdentification J C (hlen ▸ eTop)

/-- The functor Y ↦ det(J/J²)ᵛ[-c] ⊗ᴸ_B L_f(Y). -/
abbrev determinantTensor {MB : AdequateModel d} (T : DerivedTensor.Model MB)
    (L : Extension d (Ideal.Quotient.mk J)) (c : ℕ) :
    derivedValue.{max u v} A ⥤ derivedValue.{max u v} (A ⧸ J) :=
  ((Functor.const (derivedValue.{max u v} A)).obj (determinantObject.{u,v} J c)).prod'
    L.derived ⋙ T.toDescent.tensorFunctor

/-- Change the first tensor factor along the normalized identification of `f^! A` with the
shifted determinant dual. -/
def determinantTensorComparison {MB : AdequateModel d} (T : DerivedTensor.Model MB)
    (L : Extension d (Ideal.Quotient.mk J))
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J)) {c : ℕ}
    (δ : KoszulRelativeDual.relativeDual J G ≅ determinantObject.{u,v} J c) :
    source.{u,u,v} (Ideal.Quotient.mk J) e d T L G ≅ determinantTensor J T L c :=
  let s := G.functor.mapIso ((qValue A).mapIso (unitPresentation.{u,v} e)) ≪≫ δ
  Functor.isoWhiskerRight
    (NatIso.ofComponents (fun Y => s.prod (Iso.refl (L.derived.obj Y)))
      (fun _ => by
        apply CategoryTheory.Prod.hom_ext
        · exact (Category.id_comp s.hom).trans (Category.comp_id s.hom).symm
        · exact (Category.comp_id _).trans (Category.id_comp _).symm))
    T.toDescent.tensorFunctor

/-- The tensor-evaluation comparison on the coefficient lift of an original complex. -/
def OnOriginal (MA : AdequateModel e) {MB : AdequateModel d}
    (T : DerivedTensor.Model MB) (L : Extension d (Ideal.Quotient.mk J))
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    (S : ModelStability d (Ideal.Quotient.mk J))
    (η : source.{u,u,v} (Ideal.Quotient.mk J) e d T L G ⟶ G.functor) : Prop :=
  let f := Ideal.Quotient.mk J
  let qA := qValue.{max u v} A
  let qB := qValue.{max u v} (A ⧸ J)
  let F := source.{u,u,v} f e d T L G
  ∀ (X : compValue.{v} A) (I : compValue.{max u v} A)
    (a : representedUnit e ⟶ I) [QuasiIso a] (hI : isKInjectiveValue I),
    let X' := (lift.{u,v} A).obj X
    let Y := (liftD.{u,v} A).obj ((qValue A).obj X)
    ∃ (P K : compValue.{max u v} A) (p : P ⟶ X') (i : X' ⟶ K)
      (j : tensor I P ⟶ K) (_ : QuasiIso p) (_ : QuasiIso i)
      (hP : isKFlat P) (hK : isKInjectiveValue K),
      QuasiIso j ∧
      qA.map (targetAugmentation.{u,u,v} e MA a j) = qA.map (p ≫ i) ∧
      letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) p).2
        (inferInstance : QuasiIso p)
      letI := (DerivedCategory.isIso_Q_map_iff_quasiIso (ModuleCat.{max u v} A) i).2
        (inferInstance : QuasiIso i)
      let α := (liftDFactors.{u,v} A).app X ≪≫ (asIso (qA.map p)).symm
      let β := (liftDFactors.{u,v} A).app X ≪≫ asIso (qA.map i)
      η.app Y ≫ (G.modelIso f K β hK).hom =
        F.map α.hom ≫ (sourceModel f e d T L G a hI P hP).hom ≫
          qB.map (chainComparison.{u,u,v} f d S I P K j)

/-- The natural isomorphism on all of D(A), with the intrinsic determinant identification
and the localized tensor-evaluation description of its inverse. -/
def QuotientFormula (a : List A) (MA : AdequateModel e) {MB : AdequateModel d}
    (T : DerivedTensor.Model MB) (L : Extension d (Ideal.Quotient.mk J))
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    (S : ModelStability d (Ideal.Quotient.mk J)) : Prop :=
    let f := Ideal.Quotient.mk J
    (a = [] → Nonempty (determinantDual J a.length ≃ₗ[A ⧸ J] (A ⧸ J))) ∧
    ∃ δ : KoszulRelativeDual.relativeDual J G ≅ determinantObject.{u,v} J a.length,
      IdentifiesDeterminant J G a.length δ ∧
    ∃ θ : G.functor ≅ determinantTensor J T L a.length,
      OnOriginal J e MA T L G S ((determinantTensorComparison J e T L G δ).hom ≫ θ.inv) ∧
      ∀ (I P K : compValue.{max u v} A) (i : representedUnit e ⟶ I) [QuasiIso i]
        (hI : isKInjectiveValue I) (hP : isKFlat P) (j : tensor I P ⟶ K) [QuasiIso j]
        (_ : isKInjectiveValue K),
        QuasiIso (targetAugmentation.{u,u,v} e MA i j) ∧
        ((determinantTensorComparison J e T L G δ).hom ≫ θ.inv).app ((qValue A).obj P) ≫
            G.functor.map ((qValue A).map (targetAugmentation.{u,u,v} e MA i j)) =
          (sourceModel.{u,u,v} f e d T L G i hI P hP).hom ≫
            (qValue (A ⧸ J)).map (chainComparison.{u,u,v} f d S I P K j) ≫
            comparison.{max u v} f G.adjunction K

/-- The formula holds for all choices of the derived functor models. -/
def Duality : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a : List A), listIdeal a = J → RingTheory.Sequence.IsRegular A a →
  ∀ {A' B' : Type (max u v)} [CommRing A'] [CommRing B']
    {e : A ≃+* A'} {d : (A ⧸ J) ≃+* B'} (MA : AdequateModel e) {MB : AdequateModel d}
    (T : DerivedTensor.Model MB) (L : Extension d (Ideal.Quotient.mk J))
    (G : Coinduction.{max u v} (Ideal.Quotient.mk J))
    (S : ModelStability d (Ideal.Quotient.mk J)),
    QuotientFormula J e a MA T L G S

/-- The formula is realized at the common adequate level using the two lifted rings. -/
def Realization : Prop :=
  ∀ {A : Type u} [CommRing A] [IsNoetherianRing A] (J : Ideal A)
    (a : List A), listIdeal a = J → RingTheory.Sequence.IsRegular A a →
    let f := Ideal.Quotient.mk J
    let e := uliftRingEquivValue.{v,u} A
    let d := uliftRingEquivValue.{v,u} (A ⧸ J)
    ∃ (MA : AdequateModel e) (MB : AdequateModel d) (T : DerivedTensor.Model MB)
      (L : Extension d f) (G : Coinduction.{max u v} f) (S : ModelStability d f),
      QuotientFormula.{u,v} J e a MA T L G S

end Specs.DerivedFormalization.RegularQuotientDuality
