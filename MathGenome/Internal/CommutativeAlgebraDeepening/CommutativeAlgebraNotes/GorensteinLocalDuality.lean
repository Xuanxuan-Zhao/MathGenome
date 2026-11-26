import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GorensteinLocalDuality
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteFreeDualityModel
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.ExactDualCochainCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfFiniteExt
import Batteries.Tactic.OpenPrivate
import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import Mathlib.Algebra.Homology.DerivedCategory.KInjective
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive Opposite HomologicalComplex IsLocalRing
open Specs.CommutativeAlgebraNotes.GorensteinLocalDuality
open CommutativeAlgebraNotes.CompletionOfFiniteExt
open CommutativeAlgebraNotes.MatlisDualFunctorSpecs
open CommutativeAlgebraNotes.ExactDualCochainCohomologySpecs
open CommutativeAlgebraNotes.CochainTensorHom (Complex homMap tensorHomIso tensorHomIso_natural)
open CochainComplex (linearHomComplex)
open CochainComplex.HomComplex
open scoped TensorProduct

noncomputable section

namespace CommutativeAlgebraNotes.GorensteinLocalDuality

universe u

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private abbrev A := completionRing R
private abbrev M := ModuleCat.{u} R

open private tensorCompletionIso_inv_natural extPull_push from
  MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CompletionOfFiniteExt
open private cech_represents_shifted_hull tensorSwap tensorSwap_natural_left
  stalkEndIso stalkEndIso_apply from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.FiniteFreeDualityModel

/-- Extension of the free module of rank one is the completed ring. -/
private def extendRingIso :
    (extend R (A (R := R))).obj (ringModule R) ≅ completedRingModule R :=
  (TensorProduct.AlgebraTensorModule.rid R (A (R := R)) (A (R := R))).toModuleIso

private def coefficientTransport (X : ModuleCat.{u} R) (j : ℤ) :
    signedRestrictedExt R X ((extend R (A (R := R))).obj (ringModule R)) j ≅
      signedRestrictedExt R X (completedRingModule R) j :=
  (signedAdjunction R X _ j).symm.toModuleIso ≪≫
    ((signedExt (A (R := R)) j).obj (op ((extend R (A (R := R))).obj X))).mapIso
      (extendRingIso (R := R)) ≪≫ (signedAdjunction R X _ j).toModuleIso

private lemma coefficientTransport_natural {X X' : ModuleCat.{u} R} (f : X' ⟶ X) (j : ℤ) :
    restrictedPull R X X' f _ j ≫ (coefficientTransport X' j).hom =
      (coefficientTransport X j).hom ≫ restrictedPull R X X' f _ j := by
  let F := extend R (completionRing R)
  let Z := F.obj (ringModule R)
  let Z' := completedRingModule R
  let a (Y : ModuleCat.{u} R) (B : ModuleCat.{u} (completionRing R)) :=
    (signedAdjunction R Y B j).toModuleIso
  let e := extendRingIso (R := R)
  change ((a X Z).inv ≫ extPull (F.map f) Z j ≫ (a X' Z).hom) ≫
      ((a X' Z).inv ≫ extPush (F.obj X') e.hom j ≫ (a X' Z').hom) =
    ((a X Z).inv ≫ extPush (F.obj X) e.hom j ≫ (a X Z').hom) ≫
      ((a X Z').inv ≫ extPull (F.map f) Z' j ≫ (a X' Z').hom)
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% extPull_push (F.map f) e.hom j]

/-- The completed Ext comparison with the coefficient module in its ring model. -/
def completionToCoefficient (X : ModuleCat.{u} R) [Module.Finite R X] (j : ℤ) :
    (complete R).obj (extModule R j X (ringModule R)) ≅
      signedRestrictedExt R X (completedRingModule R) j :=
  (tensorCompletionIso R (extModule R j X (ringModule R))).symm ≪≫
    (coefficientEquiv R X (ringModule R) j).toModuleIso ≪≫ coefficientTransport X j

private lemma completionToCoefficient_natural {X X' : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R X'] (f : X' ⟶ X) (j : ℤ) :
    (complete R).map (extPull f (ringModule R) j) ≫ (completionToCoefficient X' j).hom =
      (completionToCoefficient X j).hom ≫ restrictedPull R X X' f (completedRingModule R) j := by
  have h := (coefficientNaturality R X X' (ringModule R) (ringModule R) f (𝟙 _) j).1
  change _ ≫ _ ≫ _ = _ ≫ _
  simp only [completionToCoefficient, Iso.trans_hom, Iso.symm_hom, Category.assoc]
  change (complete R).map (extPull f (ringModule R) j) ≫ _ = _
  rw [← reassoc_of% tensorCompletionIso_inv_natural R (extPull f (ringModule R) j)]
  change _ ≫ (extend R (completionRing R)).map (extPull f (ringModule R) j) ≫
    ModuleCat.ofHom (signedCoefficientMap R X' (ringModule R) j) ≫ _ =
      _ ≫ ModuleCat.ofHom (signedCoefficientMap R X (ringModule R) j) ≫ _ ≫ _
  rw [← reassoc_of% h, coefficientTransport_natural]

omit [IsLocalRing R] [IsNoetherianRing R] in
private lemma hom_from_flat_injective (B J : M (R := R)) [Module.Flat R B] [Injective J] :
    Injective (ModuleCat.of R (B ⟶ J)) := by
  let F := MonoidalCategory.tensorLeft B
  let adj := ihom.adjunction B
  change Injective ((ihom B).obj J)
  constructor
  intro X Y f g hg
  have : Mono (F.map g) := by
    rw [ModuleCat.mono_iff_injective]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ ((ModuleCat.mono_iff_injective g).mp hg)
  refine ⟨adj.homEquiv Y J (Injective.factorThru (adj.homEquiv X J |>.symm f) (F.map g)), ?_⟩
  rw [← adj.homEquiv_naturality_left, Injective.comp_factorThru, Equiv.apply_symm_apply]

omit [IsNoetherianRing R] in
/-- The bounded flat Čech complex dualizes into a bounded-below complex of injectives. -/
private lemma dualCech_isKInjective (E : residueFieldEnvelopeValue R) (rs : List R) :
    ((dualComplexValue E).obj (op (CechComplex rs))).IsKInjective := by
  let C := CechComplex rs
  let D := (dualComplexValue E).obj (op C)
  have e (n : ℤ) : D.X n ≅ ModuleCat.of R (C.X (-n) ⟶ hull E) :=
    (Cochain.toSingleLinearEquiv (R := R) (K := C) (X := hull E)
      (neg_add_cancel n)).toModuleIso
  have : D.IsStrictlyGE (-(rs.length : ℤ)) :=
    (CochainComplex.isStrictlyGE_iff _ _).mpr (fun n hn => by
      have h := Cech.isZero_X rs (-n) (Or.inr (by omega))
      let : Subsingleton (C.X (-n) ⟶ hull E) := ⟨h.eq_of_src⟩
      exact (ModuleCat.isZero_of_subsingleton _).of_iso (e n))
  have : ∀ n : ℤ, Injective (D.X n) := fun n => by
    have : Injective (hull E) := (Module.injective_iff_injective_object R E.carrier).mp E.isEnvelope.injectiveModule
    have := Cech.flat rs (-n)
    exact Injective.of_iso (e n).symm (hom_from_flat_injective _ _)
  exact CochainComplex.isKInjective_of_injective D (-(rs.length : ℤ))

private abbrev S₀ (R : Type u) [CommRing R] := CochainComplex.singleFunctor (ModuleCat.{u} R) 0

omit [IsLocalRing R] [IsNoetherianRing R] in
private theorem homMap_precomp_postcomp {K L I J : Complex R} (f : K ⟶ L) (g : I ⟶ J) :
    precomp (R := R) f I ≫ postcomp (R := R) K g = postcomp (R := R) L g ≫ precomp (R := R) f J := by
  apply HomologicalComplex.hom_ext
  intro n
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  apply Cochain.ext
  intro p q hpq
  simp [precomp, postcomp, Cochain.zero_cochain_comp_v, Cochain.comp_zero_cochain_v]

omit [IsLocalRing R] [IsNoetherianRing R] in
private theorem homMap_eq {K L I J : Complex R} (f : K ⟶ L) (g : I ⟶ J) :
    homMap f g = precomp (R := R) f I ≫ postcomp (R := R) K g := rfl

omit [IsLocalRing R] [IsNoetherianRing R] in
private theorem homMap_precomp {K L I : Complex R} (f : K ⟶ L) :
    homMap f (𝟙 I) = precomp (R := R) f I := by
  rw [homMap_eq]
  have hid : postcomp (R := R) K (𝟙 I) = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact Cochain.comp_id
  rw [hid, Category.comp_id]

omit [IsLocalRing R] [IsNoetherianRing R] in
private theorem homMap_postcomp {K I J : Complex R} (g : I ⟶ J) :
    homMap (𝟙 K) g = postcomp (R := R) K g := by
  have hid : precomp (R := R) (𝟙 K) I = 𝟙 _ := by
    apply HomologicalComplex.hom_ext
    intro n
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact Cochain.id_comp
  rw [homMap_eq, hid, Category.id_comp]

private def hullScalar (E : residueFieldEnvelopeValue R) (a : A (R := R)) : hull E ⟶ hull E :=
  ModuleCat.ofHom (residueHullEndomorphismEquiv E a)

private def ringScalar (a : A (R := R)) : completedRingModule R ⟶ completedRingModule R :=
  a • 𝟙 _

private abbrev B (R : Type u) [CommRing R] [IsLocalRing R] :=
  (restrict R (completionRing R)).obj (completedRingModule R)

private abbrev D (E : residueFieldEnvelopeValue R) := dualComplexValue E

private abbrev Qd [HasDerivedCategory.{u+1} (ModuleCat.{u} R)] :
    Complex R ⥤ DerivedCategory (ModuleCat.{u} R) := DerivedCategory.Q

private abbrev stalk (n : ℤ) := CochainComplex.singleFunctor (ModuleCat.{u} R) n

set_option backward.isDefEq.respectTransparency false in
private lemma single_hull_postcomp (d : ℕ) (E : residueFieldEnvelopeValue R) (a : A (R := R)) :
    hullPostcomp E ((stalk (R := R) (d : ℤ)).obj (hull E)) (hullScalar E a) ≫
        (stalkEndIso d E).hom =
      (stalkEndIso d E).hom ≫ (stalk (R := R) (-(d : ℤ))).map
        ((restrict R (completionRing R)).map (ringScalar a)) := by
  apply HomologicalComplex.hom_ext
  intro n
  by_cases hn : n = -(d : ℤ)
  · subst n
    apply (cancel_mono (singleObjXSelf (.up ℤ) (-(d : ℤ)) (ModuleCat.of R (A (R := R)))).hom).mp
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply (residueHullEndomorphismEquiv E).injective
    ext y
    let Q := (stalk (R := R) (d : ℤ)).obj (hull E)
    let eQ := (singleObjXSelf (.up ℤ) (d : ℤ) (hull E))
    let eL := (singleObjXSelf (.up ℤ) (-(d : ℤ)) (ModuleCat.of R (A (R := R))))
    let c := ((restrict R (completionRing R)).map (ringScalar a))
    let f := (stalkEndIso d E).hom.f (-(d : ℤ)) z
    have hh : ((stalk (R := R) (-(d : ℤ))).map c).f (-(d : ℤ)) ≫ eL.hom = eL.hom ≫ c := by
      change ((single _ (.up ℤ) (-(d : ℤ))).map c).f _ ≫ eL.hom = _
      rw [single_map_f_self]
      change (eL.hom ≫ c ≫ eL.inv) ≫ eL.hom = eL.hom ≫ c
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    have hj : ((S₀ R).map (hullScalar E a)).f 0 ≫
        (singleObjXSelf (.up ℤ) 0 (hull E)).hom =
        (singleObjXSelf (.up ℤ) 0 (hull E)).hom ≫ hullScalar E a := by
      change ((single _ (.up ℤ) (0 : ℤ)).map (hullScalar E a)).f _ ≫ _ = _
      rw [single_map_f_self]
      simp
    simp only [HomologicalComplex.comp_f]
    change residueHullEndomorphismEquiv E
      (eL.hom ((stalkEndIso d E).hom.f _ ((hullPostcomp E Q (hullScalar E a)).f _ z))) y =
      residueHullEndomorphismEquiv E (eL.hom (((stalk _).map c).f _ f)) y
    have hh' : eL.hom (((stalk _).map c).f _ f) = a * eL.hom f :=
      ConcreteCategory.congr_hom hh f
    rw [hh']
    rw [map_mul, Module.End.mul_apply]
    let x : Q.X (d : ℤ) := eQ.inv y
    have hx : eQ.hom x = y := by simp [x]
    rw [← hx]
    have eq₁ := stalkEndIso_apply d E
      (show Cochain Q (hullInDegreeZero E) (-(d : ℤ)) from
        (hullPostcomp E Q (hullScalar E a)).f _ z) x
    have eq₂ := stalkEndIso_apply d E
      (show Cochain Q (hullInDegreeZero E) (-(d : ℤ)) from z) x
    dsimp only at eq₁ eq₂
    rw [eq₁, eq₂]
    change (singleObjXSelf (.up ℤ) 0 (hull E)).hom
        (((z.comp (Cochain.ofHom ((S₀ R).map (hullScalar E a))) (add_zero _)).v _ _ _) x) = _
    rw [Cochain.comp_zero_cochain_v, Cochain.ofHom_v]
    have hj' (w : (hullInDegreeZero E).X 0) :
        (singleObjXSelf (.up ℤ) 0 (hull E)).hom (((S₀ R).map (hullScalar E a)).f 0 w) =
          hullScalar E a ((singleObjXSelf (.up ℤ) 0 (hull E)).hom w) :=
      ConcreteCategory.congr_hom hj w
    exact hj' _
  · exact (isZero_single_obj_X (.up ℤ) (-(d : ℤ)) _ n hn).eq_of_tgt _ _


section DerivedHom

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} R)]

/-- The image of a cohomology class under localization to the derived category. -/
private def classToDerived {K L : Complex R} (n : ℤ) :
    CohomologyClass K L n →+ (Qd.obj K ⟶ (Qd.obj L)⟦n⟧) :=
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let s := (Qd (R := R)).commShiftIso n
  { toFun := fun x => e.inv.app K ≫ DerivedCategory.Qh.map (CohomologyClass.toHom x) ≫
      e.hom.app (L⟦n⟧) ≫ s.hom.app L
    map_zero' := by simp
    map_add' := by intros; simp [add_comp, comp_add] }

omit [IsLocalRing R] [IsNoetherianRing R] in
private lemma classToDerived_mk {K L : Complex R} (n : ℤ) (z : Cocycle K L n) :
    classToDerived n (CohomologyClass.mk z) =
      Qd.map (Cocycle.equivHomShift.symm z) ≫ ((Qd (R := R)).commShiftIso n).hom.app L := by
  dsimp [classToDerived]
  rw [CohomologyClass.toHom_mk, DerivedCategory.quotientCompQhIso_hom_naturality_assoc]
  simp

private def homologyDerived {K L : Complex R} [L.IsKInjective] (n : ℤ) :
    (linearHomComplex R K L).homology n ≃+ (Qd.obj K ⟶ (Qd.obj L)⟦n⟧) :=
  let e := DerivedCategory.quotientCompQhIso (ModuleCat.{u} R)
  let s := (Qd (R := R)).commShiftIso n
  (homologyLinearEquiv R K L n).toAddEquiv.trans
    (AddEquiv.ofBijective (classToDerived n)
      ((Iso.homCongr (e.app K) (e.app (L⟦n⟧) ≪≫ s.app L)).bijective.comp
        ((CochainComplex.IsKInjective.Qh_map_bijective _ (L⟦n⟧)).comp
          (CohomologyClass.toHom_bijective K L n))))

private def cycleClass {K L : Complex R} (n : ℤ) (z : Cocycle K L n) :
    (linearHomComplex R K L).homology n :=
  (linearLeftHomologyData R K L n).homologyIso.inv (CohomologyClass.mk z)

omit [IsLocalRing R] [IsNoetherianRing R] [HasDerivedCategory (ModuleCat R)] in
private lemma cycleClass_surjective {K L : Complex R} (n : ℤ) :
    Function.Surjective (cycleClass (K := K) (L := L) n) :=
  ((linearLeftHomologyData R K L n).homologyIso.symm.toLinearEquiv.surjective).comp
    CohomologyClass.mk_surjective

omit [IsLocalRing R] [IsNoetherianRing R] in
private lemma homologyDerived_cycleClass {K L : Complex R} [L.IsKInjective]
    (n : ℤ) (z : Cocycle K L n) :
    homologyDerived n (cycleClass n z) =
      Qd.map (Cocycle.equivHomShift.symm z) ≫ ((Qd (R := R)).commShiftIso n).hom.app L := by
  change classToDerived n
    ((linearLeftHomologyData R K L n).homologyIso.hom
      ((linearLeftHomologyData R K L n).homologyIso.inv (CohomologyClass.mk z))) = _
  rw [show (linearLeftHomologyData R K L n).homologyIso.hom
      ((linearLeftHomologyData R K L n).homologyIso.inv (CohomologyClass.mk z)) =
      CohomologyClass.mk z from ConcreteCategory.congr_hom
        (linearLeftHomologyData R K L n).homologyIso.inv_hom_id _, classToDerived_mk]

omit [IsLocalRing R] [IsNoetherianRing R] [HasDerivedCategory (ModuleCat R)] in
private lemma homologyMap_cycleClass {K K' L L' : Complex R}
    (f : K' ⟶ K) (g : L ⟶ L') (n : ℤ) (z : Cocycle K L n) :
    homologyMap (homMap f g) n (cycleClass n z) = cycleClass n ((z.precomp f).postcomp g) := by
  let h := linearLeftHomologyData R K L n
  let h' := linearLeftHomologyData R K' L' n
  let φ := (shortComplexFunctor (ModuleCat.{u} R) (.up ℤ) n).map (homMap f g)
  let γ : ShortComplex.LeftHomologyMapData φ h h' := default
  have hz : γ.φK z = (z.precomp f).postcomp g := by
    apply Subtype.ext
    exact ConcreteCategory.congr_hom γ.commi z
  have hm : h.π ≫ h.homologyIso.inv ≫ ShortComplex.homologyMap φ =
      γ.φK ≫ h'.π ≫ h'.homologyIso.inv := by
    rw [γ.homologyMap_eq]
    simp
  have he := ConcreteCategory.congr_hom hm z
  change homologyMap (homMap f g) n (cycleClass n z) =
    cycleClass n (γ.φK z) at he
  simpa only [hz] using he

private lemma homologyDerived_naturality {K K' L L' : Complex R}
    [L.IsKInjective] [L'.IsKInjective] (f : K' ⟶ K) (g : L ⟶ L') (n : ℤ)
    (x : (linearHomComplex R K L).homology n) :
    homologyDerived n (homologyMap (homMap f g) n x) =
      Qd.map f ≫ homologyDerived n x ≫ (Qd.map g)⟦n⟧' := by
  obtain ⟨z, rfl⟩ := cycleClass_surjective n x
  rw [homologyMap_cycleClass, homologyDerived_cycleClass, homologyDerived_cycleClass,
    Cocycle.equivHomShift_symm_postcomp, Cocycle.equivHomShift_symm_precomp]
  simp only [Functor.map_comp, Category.assoc, Functor.commShiftIso_hom_naturality]

end DerivedHom


section CechModel

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} R)]

private abbrev SD (R : Type u) [CommRing R] [HasDerivedCategory.{u+1} (ModuleCat.{u} R)] :=
  DerivedCategory.singleFunctor (ModuleCat.{u} R) 0

private abbrev SDMapScalar (a : A (R := R)) :=
  (SD R).map ((restrict R (completionRing R)).map (ringScalar a))

omit [HasDerivedCategory (ModuleCat R)] in
private lemma dual_map_scalar (E : residueFieldEnvelopeValue R)
    {U V : Complex R} (f : U ⟶ V) (a : A (R := R)) :
    (D E).map f.op ≫ hullPostcomp E U (hullScalar E a) =
      hullPostcomp E V (hullScalar E a) ≫ (D E).map f.op :=
  homMap_precomp_postcomp f _

set_option backward.isDefEq.respectTransparency false in
private theorem dualCechTarget
    (hG : AdvCommAlg.Gorenstein.Specs.LocalGorensteinValue R) (d : ℕ)
    (hd : ringKrullDim R = (d : WithBot ℕ∞)) (E : residueFieldEnvelopeValue R)
    (rs : List R) (hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R) :
    ∃ e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦(d : ℤ)⟧,
      ∀ a : A (R := R),
        Qd.map (hullPostcomp E (CechComplex rs) (hullScalar E a)) ≫ e.hom =
          e.hom ≫ (SDMapScalar a)⟦(d : ℤ)⟧' := by
  let C := CechComplex rs
  let H := (stalk (R := R) (d : ℤ)).obj (hull E)
  let L := (stalk (R := R) (-(d : ℤ))).obj (B R)
  let Q := Qd (R := R)
  obtain ⟨e⟩ := cech_represents_shifted_hull hG d hd E rs hrs
  obtain ⟨W, s, hs, t, ht⟩ := DerivedCategory.right_fac e.hom
  have ht' : IsIso (Q.map t) := by
    rw [← IsIso.hom_inv_id_assoc (Q.map s) (Q.map t), ← ht]
    infer_instance
  have hs' := matlisDualCochain_quasiIso E s
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ s).mp hs)
  have ht'' := matlisDualCochain_quasiIso E t
    ((DerivedCategory.isIso_Q_map_iff_quasiIso _ t).mp ht')
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ ((D E).map s.op)).mpr hs'
  have := (DerivedCategory.isIso_Q_map_iff_quasiIso _ ((D E).map t.op)).mpr ht''
  let es := asIso (Q.map ((D E).map s.op))
  let et := asIso (Q.map ((D E).map t.op))
  let eH : Q.obj ((D E).obj (op H)) ≅ Q.obj L := Q.mapIso (stalkEndIso d E)
  let k := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) (-(d : ℤ))
  let m := (DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
    (d : ℤ) (-(d : ℤ)) 0 (add_neg_cancel _)
  refine ⟨es ≪≫ et.symm ≪≫ eH ≪≫
    (k.app (B R)).symm ≪≫ (m.app (B R)).symm, ?_⟩
  intro a
  let p := fun U => Q.map (hullPostcomp E U (hullScalar E a))
  let b := (restrict R (completionRing R)).map (ringScalar a)
  have cs : p C ≫ es.hom = es.hom ≫ p W := by
    change _ ≫ Q.map _ = Q.map _ ≫ _
    rw [← Q.map_comp, ← Q.map_comp, dual_map_scalar]
  have ct : p W ≫ et.inv = et.inv ≫ p H := by
    rw [← cancel_mono et.hom]
    have ht₀ : et.hom ≫ p W = p H ≫ et.hom := by
      change Q.map _ ≫ Q.map _ = Q.map _ ≫ Q.map _
      rw [← Q.map_comp, ← Q.map_comp, dual_map_scalar]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, ← ht₀,
      Iso.inv_hom_id_assoc]
  have ce : p H ≫ eH.hom = eH.hom ≫ Q.map ((stalk _).map b) := by
    change Q.map (hullPostcomp E H (hullScalar E a)) ≫ Q.map (stalkEndIso d E).hom =
      Q.map (stalkEndIso d E).hom ≫ Q.map ((stalk _).map b)
    rw [← Q.map_comp, ← Q.map_comp, single_hull_postcomp]
  have ck : Q.map ((stalk _).map b) ≫ (k.app (B R)).inv =
      (k.app (B R)).inv ≫ (DerivedCategory.singleFunctor (ModuleCat.{u} R) (-(d : ℤ))).map b :=
    k.inv.naturality b
  have cm := m.inv.naturality b
  change p C ≫ es.hom ≫ et.inv ≫ eH.hom ≫
      (k.app (B R)).inv ≫ (m.app (B R)).inv =
    (es.hom ≫ et.inv ≫ eH.hom ≫
      (k.app (B R)).inv ≫ (m.app (B R)).inv) ≫ (SDMapScalar a)⟦(d : ℤ)⟧'
  simp only [Category.assoc]
  rw [reassoc_of% cs, reassoc_of% ct, reassoc_of% ce, reassoc_of% ck]
  exact congrArg (fun v => es.hom ≫ et.inv ≫ eH.hom ≫
    (k.app (B R)).inv ≫ v) cm

end CechModel

section LocalCohomology

private abbrev cechWith (rs : List R) :=
  S₀ R ⋙ Specs.CommutativeAlgebraNotes.AugmentedCechComplex.tensorFunctor R rs

private abbrev H (n : ℤ) := homologyFunctor (ModuleCat.{u} R) (.up ℤ) n

private abbrev LC (i : ℤ) := Specs.CommutativeAlgebraNotes.IdealTorsion.localCohomology.{u}
  (maximalIdeal R) i

private abbrev dualLC (E : residueFieldEnvelopeValue R) (n : ℤ) :=
  (LC (R := R) (-n)).op ⋙ matlisDualValue E

private abbrev Comparison (rs : List R) (n : ℤ) :=
  LC (R := R) (-n) ≅ cechWith rs ⋙ H (R := R) (-n)

private def localDualCech (E : residueFieldEnvelopeValue R) (rs : List R) (n : ℤ)
    (l : Comparison rs n) :
    dualLC E n ≅ (cechWith rs).op ⋙ dualCohomology E n :=
  Functor.isoWhiskerRight (NatIso.op l.symm ≪≫ Functor.opComp _ _) _ ≪≫
    (Functor.associator _ _ _) ≪≫
    Functor.isoWhiskerLeft _ (ExactDualCochainCohomology.cohomologyIso E n).symm

omit [IsNoetherianRing R] in
private lemma dualPostcomp_natural (E : residueFieldEnvelopeValue R)
    {X Y : ModuleCat.{u} R} (f : X ⟶ Y) (a : hull E ⟶ hull E) :
    dualPostcomp E Y a ≫ (matlisDualValue E).map f.op =
      (matlisDualValue E).map f.op ≫ dualPostcomp E X a := rfl

set_option backward.isDefEq.respectTransparency false in
omit [IsNoetherianRing R] in
private lemma localDualCech_postcomp (E : residueFieldEnvelopeValue R) (rs : List R) (n : ℤ)
    (l : Comparison rs n) (X : ModuleCat.{u} R) (a : hull E ⟶ hull E) :
    dualPostcomp E ((LC (R := R) (-n)).obj X) a ≫ (localDualCech E rs n l).hom.app (op X) =
      (localDualCech E rs n l).hom.app (op X) ≫
        homologyMap (hullPostcomp E ((cechWith rs).obj X) a) n := by
  let e := ExactDualCochainCohomology.cohomologyIso E n
  have hs := ExactDualCochainCohomology.cohomologyIso_postcomp E n ((cechWith rs).obj X) a
  simp only [localDualCech, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.opComp, Iso.refl_hom, Category.comp_id, Category.id_comp, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom]
  change dualPostcomp E _ a ≫ (matlisDualValue E).map (l.inv.app X).op ≫ e.inv.app _ =
    ((matlisDualValue E).map (l.inv.app X).op ≫ e.inv.app _) ≫ _
  rw [reassoc_of% dualPostcomp_natural E (l.inv.app X) a, Category.assoc]
  apply congrArg ((matlisDualValue E).map (l.inv.app X).op ≫ ·)
  let U := (cechWith rs).obj X
  let c : (H (R := R) n).obj ((D E).obj (op U)) ≅
      (matlisDualValue E).obj (op ((H (R := R) (-n)).obj U)) := e.app (op U)
  let a₀ := dualPostcomp E ((H (R := R) (-n)).obj U) a
  let a₁ : (H (R := R) n).obj ((D E).obj (op U)) ⟶ (H (R := R) n).obj ((D E).obj (op U)) :=
    (H (R := R) n).map (hullPostcomp E U a)
  change a₀ ≫ c.inv = c.inv ≫ a₁
  have hcomm : a₁ ≫ c.hom = c.hom ≫ a₀ := hs
  apply (cancel_epi c.hom).mp
  calc
    c.hom ≫ a₀ ≫ c.inv = (a₁ ≫ c.hom) ≫ c.inv :=
      (Category.assoc _ _ _).symm.trans (congrArg (· ≫ c.inv) hcomm.symm)
    _ = a₁ := by simp
    _ = c.hom ≫ c.inv ≫ a₁ := by simp

private def cechHomComparison (E : residueFieldEnvelopeValue R) (rs : List R)
    (X : ModuleCat.{u} R) :
    (D E).obj (op ((cechWith rs).obj X)) ≅
      linearHomComplex R ((S₀ R).obj X) ((D E).obj (op (CechComplex rs))) :=
  (D E).mapIso (tensorSwap ((S₀ R).obj X) (CechComplex rs)).op ≪≫
    tensorHomIso ((S₀ R).obj X) (CechComplex rs) (hullInDegreeZero E)

set_option backward.isDefEq.respectTransparency false in
private lemma cechHomComparison_natural (E : residueFieldEnvelopeValue R) (rs : List R)
    {X X' : ModuleCat.{u} R} (f : X' ⟶ X) :
    (D E).map ((cechWith rs).map f).op ≫ (cechHomComparison E rs X').hom =
      (cechHomComparison E rs X).hom ≫ homMap ((S₀ R).map f) (𝟙 _) := by
  let C := CechComplex rs
  let g := (S₀ R).map f
  let U := (S₀ R).obj X
  let U' := (S₀ R).obj X'
  let S := D E
  let J := hullInDegreeZero E
  let e := tensorHomIso U C J
  let e' := tensorHomIso U' C J
  have hs : S.map (tensorHom (𝟙 C) g).op ≫ S.map (tensorSwap U' C).hom.op =
      S.map (tensorSwap U C).hom.op ≫ S.map (tensorHom g (𝟙 C)).op := by
    rw [← S.map_comp, ← S.map_comp, ← op_comp, ← op_comp, tensorSwap_natural_left]
  have hid : homMap (𝟙 C) (𝟙 J) = 𝟙 _ := by
    rw [homMap_postcomp]
    apply HomologicalComplex.hom_ext
    intro i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact Cochain.comp_id
  have ht' : S.map (tensorHom g (𝟙 C)).op ≫ e'.hom = e.hom ≫ homMap g (𝟙 _) := by
    change precomp (R := R) (tensorHom g (𝟙 C)) J ≫ e'.hom = _
    rw [← homMap_precomp]
    simpa only [hid] using tensorHomIso_natural (P := U) (Q := C) (J := J) g (𝟙 C) (𝟙 J)
  change S.map (tensorHom (𝟙 C) g).op ≫ S.map (tensorSwap U' C).hom.op ≫ e'.hom =
      (S.map (tensorSwap U C).hom.op ≫ e.hom) ≫ homMap g (𝟙 _)
  rw [reassoc_of% hs, Category.assoc, ht']

set_option backward.isDefEq.respectTransparency false in
private lemma cechHomComparison_postcomp (E : residueFieldEnvelopeValue R) (rs : List R)
    (X : ModuleCat.{u} R) (a : hull E ⟶ hull E) :
    hullPostcomp E ((cechWith rs).obj X) a ≫ (cechHomComparison E rs X).hom =
      (cechHomComparison E rs X).hom ≫ homMap (𝟙 ((S₀ R).obj X))
        (hullPostcomp E (CechComplex rs) a) := by
  let C := CechComplex rs
  let U := (S₀ R).obj X
  let J := hullInDegreeZero E
  let g := (S₀ R).map a
  let sw := (tensorSwap U C).hom
  let e := tensorHomIso U C J
  have h₁ := homMap_precomp_postcomp (R := R) sw g
  have h₂ := tensorHomIso_natural (P := U) (Q := C) (J := J) (𝟙 U) (𝟙 C) g
  have hid : tensorHom (𝟙 U) (𝟙 C) = 𝟙 (tensorObj U C) := by
    exact MonoidalCategory.id_tensorHom_id U C
  rw [hid, homMap_postcomp, homMap_postcomp (K := C)] at h₂
  change postcomp (R := R) (tensorObj C U) g ≫ precomp (R := R) sw J ≫ e.hom =
    (precomp (R := R) sw J ≫ e.hom) ≫ homMap (𝟙 U) (postcomp (R := R) C g)
  rw [← reassoc_of% h₁, Category.assoc, h₂]

private def localDualHom (E : residueFieldEnvelopeValue R) (rs : List R)
    (n : ℤ) (l : Comparison rs n) (X : ModuleCat.{u} R) :
    (dualLC E n).obj (op X) ≅
      (linearHomComplex R ((S₀ R).obj X) ((D E).obj (op (CechComplex rs)))).homology n :=
  (localDualCech E rs n l).app (op X) ≪≫ (H (R := R) n).mapIso (cechHomComparison E rs X)

set_option backward.isDefEq.respectTransparency false in
private lemma localDualHom_natural (E : residueFieldEnvelopeValue R) (rs : List R)
    (n : ℤ) (l : Comparison rs n) {X X' : ModuleCat.{u} R} (f : X' ⟶ X) :
    (dualLC E n).map f.op ≫ (localDualHom E rs n l X').hom =
      (localDualHom E rs n l X).hom ≫ homologyMap (homMap ((S₀ R).map f) (𝟙 _)) n := by
  let F := H (R := R) n
  change (dualLC E n).map f.op ≫ (localDualCech E rs n l).hom.app _ ≫
      F.map (cechHomComparison E rs X').hom =
    ((localDualCech E rs n l).hom.app _ ≫ F.map (cechHomComparison E rs X).hom) ≫
      F.map (homMap ((S₀ R).map f) (𝟙 _))
  rw [NatTrans.naturality_assoc, Category.assoc]
  change _ ≫ F.map _ ≫ F.map _ = _ ≫ F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun m => (localDualCech E rs n l).hom.app (op X) ≫ F.map m)
    (cechHomComparison_natural E rs f)

set_option backward.isDefEq.respectTransparency false in
private lemma localDualHom_postcomp (E : residueFieldEnvelopeValue R) (rs : List R)
    (n : ℤ) (l : Comparison rs n) (X : ModuleCat.{u} R) (a : hull E ⟶ hull E) :
    dualPostcomp E ((LC (R := R) (-n)).obj X) a ≫ (localDualHom E rs n l X).hom =
      (localDualHom E rs n l X).hom ≫ homologyMap (homMap (𝟙 ((S₀ R).obj X))
        (hullPostcomp E (CechComplex rs) a)) n := by
  let F := H (R := R) n
  change dualPostcomp E _ a ≫ (localDualCech E rs n l).hom.app _ ≫
      F.map (cechHomComparison E rs X).hom =
    ((localDualCech E rs n l).hom.app _ ≫ F.map (cechHomComparison E rs X).hom) ≫
      F.map (homMap (𝟙 ((S₀ R).obj X)) (hullPostcomp E (CechComplex rs) a))
  rw [reassoc_of% localDualCech_postcomp E rs n l X a, Category.assoc]
  change _ ≫ F.map _ ≫ F.map _ = _ ≫ F.map _ ≫ F.map _
  rw [← F.map_comp, ← F.map_comp]
  exact congrArg (fun m => (localDualCech E rs n l).hom.app (op X) ≫ F.map m)
    (cechHomComparison_postcomp E rs X a)

end LocalCohomology

section Comparisons

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} R)]

private abbrev Tri (R : Type u) [CommRing R] [HasDerivedCategory.{u+1} (ModuleCat.{u} R)] :=
  DerivedCategory (ModuleCat.{u} R)

private abbrev ShiftedExt (X : ModuleCat.{u} R) (j : ℤ) :=
  ShiftedHom ((SD R).obj X) ((SD R).obj (B R)) j

private def shiftedTarget {N : Tri R} (d n : ℤ) (e : N ≅ ((SD R).obj (B R))⟦d⟧) :
    N⟦n⟧ ≅ ((SD R).obj (B R))⟦d + n⟧ :=
  (shiftFunctor (Tri R) n).mapIso e ≪≫
    (shiftFunctorAdd (Tri R) d n).symm.app ((SD R).obj (B R))

set_option backward.isDefEq.respectTransparency false in
omit [IsNoetherianRing R] in
private lemma shiftedTarget_comm {N : Tri R} (d n : ℤ)
    (e : N ≅ ((SD R).obj (B R))⟦d⟧) {f : N ⟶ N} {g : (SD R).obj (B R) ⟶ _}
    (w : f ≫ e.hom = e.hom ≫ g⟦d⟧') :
    f⟦n⟧' ≫ (shiftedTarget d n e).hom = (shiftedTarget d n e).hom ≫ g⟦d + n⟧' := by
  let q := (shiftFunctorAdd (Tri R) d n).inv
  change f⟦n⟧' ≫ e.hom⟦n⟧' ≫ q.app _ = (e.hom⟦n⟧' ≫ q.app _) ≫ g⟦d + n⟧'
  rw [← Functor.map_comp_assoc, w, Functor.map_comp, Category.assoc, Category.assoc]
  exact congrArg (e.hom⟦n⟧' ≫ ·) (q.naturality g)

private def localDualToShiftedHom (E : residueFieldEnvelopeValue R) (rs : List R)
    (d n : ℤ) (l : Comparison rs n)
    (e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦d⟧)
    (X : ModuleCat.{u} R) :
    (dualLC E n).obj (op X) ≃+ ShiftedExt X (d + n) :=
  let start := (DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0).app X
  let finish := shiftedTarget d n e
  letI := dualCech_isKInjective E rs
  (localDualHom E rs n l X).toLinearEquiv.toAddEquiv.trans
    ((homologyDerived n).trans
      { toEquiv := Iso.homCongr start.symm finish
        map_add' := by intros; simp [Iso.homCongr, add_comp, comp_add] })

set_option backward.isDefEq.respectTransparency false in
private lemma localDualToShiftedHom_natural (E : residueFieldEnvelopeValue R) (rs : List R)
    (d n : ℤ) (l : Comparison rs n)
    (e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦d⟧)
    {X X' : ModuleCat.{u} R} (f : X' ⟶ X) (x : (dualLC E n).obj (op X)) :
    localDualToShiftedHom E rs d n l e X' ((dualLC E n).map f.op x) =
      (SD R).map f ≫ localDualToShiftedHom E rs d n l e X x := by
  let s := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0
  let y := (localDualHom E rs n l X).hom x
  let K := (D E).obj (op (CechComplex rs))
  let := dualCech_isKInjective E rs
  have h : (localDualHom E rs n l X').hom ((dualLC E n).map f.op x) =
      homologyMap (homMap ((S₀ R).map f) (𝟙 K)) n y :=
    ConcreteCategory.congr_hom (localDualHom_natural E rs n l f) x
  change s.hom.app X' ≫ homologyDerived n
      ((localDualHom E rs n l X').hom ((dualLC E n).map f.op x)) ≫ (shiftedTarget d n e).hom =
    (SD R).map f ≫ (s.hom.app X ≫ homologyDerived n y ≫ (shiftedTarget d n e).hom)
  rw [h, homologyDerived_naturality]
  have h' : (SD R).map f ≫ s.hom.app X = s.hom.app X' ≫ Qd.map ((S₀ R).map f) :=
    s.hom.naturality f
  simp only [Category.assoc]
  rw [← reassoc_of% h']
  have hid : (Qd.map (𝟙 K))⟦n⟧' = 𝟙 _ := ((Qd (R := R)) ⋙ shiftFunctor (Tri R) n).map_id K
  rw [hid]
  exact congrArg (fun v => (SD R).map f ≫ s.hom.app X ≫ homologyDerived n y ≫ v)
    (Category.id_comp (shiftedTarget d n e).hom)

set_option backward.isDefEq.respectTransparency false in
private lemma localDualToShiftedHom_scalar (E : residueFieldEnvelopeValue R) (rs : List R)
    (d n : ℤ) (l : Comparison rs n)
    (e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦d⟧)
    (a : A (R := R))
    (w : Qd.map (hullPostcomp E (CechComplex rs) (hullScalar E a)) ≫ e.hom =
          e.hom ≫ (SDMapScalar a)⟦d⟧')
    (X : ModuleCat.{u} R) (x : (dualLC E n).obj (op X)) :
    localDualToShiftedHom E rs d n l e X
      (dualPostcomp E ((LC (R := R) (-n)).obj X) (hullScalar E a) x) =
      localDualToShiftedHom E rs d n l e X x ≫ (SDMapScalar a)⟦d + n⟧' := by
  let s := DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R) 0
  let y := (localDualHom E rs n l X).hom x
  let t := hullPostcomp E (CechComplex rs) (hullScalar E a)
  let := dualCech_isKInjective E rs
  have h : (localDualHom E rs n l X).hom
      (dualPostcomp E ((LC (R := R) (-n)).obj X) (hullScalar E a) x) =
        homologyMap (homMap (𝟙 ((S₀ R).obj X)) t) n y :=
    ConcreteCategory.congr_hom (localDualHom_postcomp E rs n l X (hullScalar E a)) x
  change s.hom.app X ≫ homologyDerived n
      ((localDualHom E rs n l X).hom (dualPostcomp E _ (hullScalar E a) x)) ≫
      (shiftedTarget d n e).hom =
    (s.hom.app X ≫ homologyDerived n y ≫ (shiftedTarget d n e).hom) ≫ (SDMapScalar a)⟦d + n⟧'
  rw [h, homologyDerived_naturality]
  simp only [Category.assoc]
  rw [shiftedTarget_comm d n e w]
  have hid := (Qd (R := R)).map_id ((S₀ R).obj X)
  rw [hid]
  exact congrArg (s.hom.app X ≫ ·) (Category.id_comp _)

omit [IsNoetherianRing R] in
private lemma shiftedExt_negSubsingleton (X : ModuleCat.{u} R) (j : ℤ) (hj : j < 0) :
    Subsingleton (ShiftedExt X j) := by
  let t := DerivedCategory.TStructure.t (C := ModuleCat.{u} R)
  have h₀ : t.IsLE ((SD R).obj X) 0 := inferInstanceAs (DerivedCategory.IsLE _ _)
  have h₁ : t.IsGE (((SD R).obj (B R))⟦j⟧) (-j) :=
    t.isGE_shift _ 0 j (-j) (add_neg_cancel j)
  refine ⟨fun x y => ?_⟩
  have h (v : ShiftedExt X j) : v = 0 := t.zero_of_isLE_of_isGE v 0 (-j) (by omega) h₀ h₁
  exact (h x).trans (h y).symm

private def fromShiftedExt (X : ModuleCat.{u} R) (j : ℤ) :
    ShiftedExt X j ≃+ signedRestrictedExt R X (completedRingModule R) j :=
  match j with
  | .ofNat n => (Ext.homAddEquiv (X := X) (Y := B R) (n := n)).symm
  | .negSucc k =>
    letI := shiftedExt_negSubsingleton X (.negSucc k) (Int.negSucc_lt_zero k)
    { toFun := fun _ => PUnit.unit
      invFun := fun _ => 0
      left_inv := fun _ => Subsingleton.elim _ _
      right_inv := fun _ => Subsingleton.elim _ _
      map_add' := fun _ _ => Subsingleton.elim (α := PUnit.{u+1}) _ _ }

set_option backward.isDefEq.respectTransparency false in
private lemma fromShiftedExt_precomp {X X' : ModuleCat.{u} R} (f : X' ⟶ X) (j : ℤ)
    (x : ShiftedExt X j) :
    fromShiftedExt X' j ((SD R).map f ≫ x) =
      restrictedPull R X X' f (completedRingModule R) j (fromShiftedExt X j x) := by
  cases j with
  | negSucc k => exact Subsingleton.elim (α := PUnit.{u+1}) _ _
  | ofNat n =>
    have h := (restrictedExtMaps R X X' _ _ f (𝟙 (completedRingModule R)) n
      (fromShiftedExt X (.ofNat n) x)).1
    refine Eq.trans ?_ h.symm
    apply Ext.ext
    simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.mk₀_comp]
    change (Ext.homAddEquiv (Ext.homAddEquiv.symm _)) =
      (SD R).map f ≫ Ext.homAddEquiv (Ext.homAddEquiv.symm x)
    simp

set_option backward.isDefEq.respectTransparency false in
private lemma fromShiftedExt_scalar (X : ModuleCat.{u} R) (j : ℤ)
    (a : A (R := R)) (x : ShiftedExt X j) :
    fromShiftedExt X j (x ≫ (SDMapScalar a)⟦j⟧') =
      a • fromShiftedExt X j x := by
  cases j with
  | negSucc k => exact Subsingleton.elim (α := PUnit.{u+1}) _ _
  | ofNat n =>
    have h := restrictedScalarAction R (completionRing R) X (completedRingModule R) n a
      (fromShiftedExt X (.ofNat n) x)
    refine Eq.trans ?_ h.symm
    apply Ext.ext
    simp only [Ext.comp_hom, Ext.mk₀_hom, ShiftedHom.comp_mk₀]
    change (Ext.homAddEquiv (Ext.homAddEquiv.symm _)) =
      Ext.homAddEquiv (Ext.homAddEquiv.symm x) ≫ (SDMapScalar a)⟦(n : ℤ)⟧'
    simp

end Comparisons

section Assembly

open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules (IsPowerTorsion scalar)

variable [HasDerivedCategory.{u+1} (ModuleCat.{u} R)]

set_option backward.isDefEq.respectTransparency false in
omit [HasDerivedCategory (ModuleCat R)] in
private lemma dual_scalar (E : residueFieldEnvelopeValue R) (h : IsPowerTorsion R E.carrier)
    (X : ModuleCat.{u} R) (a : A (R := R)) (x : (completedDual E h).obj (op X)) :
    (show (matlisDualValue E).obj (op X) from a • x) =
      dualPostcomp E X (hullScalar E a) x := by
  apply LinearMap.ext
  intro y
  let g : X →ₗ[R] E.carrier := x
  change scalar h a (g y) = residueHullEndomorphismEquiv E a (g y)
  exact (residueHullEndomorphismEquiv_apply E a (g y)).symm

private def firstComparison (E : residueFieldEnvelopeValue R) (h : IsPowerTorsion R E.carrier)
    (rs : List R) (d n : ℤ) (l : Comparison rs n)
    (e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦d⟧)
    (he : ∀ a : A (R := R),
      Qd.map (hullPostcomp E (CechComplex rs) (hullScalar E a)) ≫ e.hom =
        e.hom ≫ (SDMapScalar a)⟦d⟧')
    (X : ModuleCat.{u} R) :
    (localDual E h (-n)).obj (op X) ≃ₗ[A (R := R)]
      signedRestrictedExt R X (completedRingModule R) (d + n) :=
  { (localDualToShiftedHom E rs d n l e X).trans (fromShiftedExt X (d + n)) with
    map_smul' := by
      intro a x
      change fromShiftedExt X _ (localDualToShiftedHom E rs d n l e X
        (show (dualLC E n).obj (op X) from a • x)) = _
      let g : (dualLC E n).obj (op X) := x
      calc
        _ = fromShiftedExt X (d + n)
            (localDualToShiftedHom E rs d n l e X
              (dualPostcomp E ((LC (R := R) (-n)).obj X) (hullScalar E a) g)) :=
          congrArg (fun v => fromShiftedExt X (d + n) (localDualToShiftedHom E rs d n l e X v))
            (dual_scalar E h ((LC (R := R) (-n)).obj X) a x)
        _ = fromShiftedExt X (d + n)
            (localDualToShiftedHom E rs d n l e X g ≫ (SDMapScalar a)⟦d + n⟧') :=
          congrArg (fromShiftedExt X (d + n))
            (localDualToShiftedHom_scalar E rs d n l e a (he a) X g)
        _ = _ := fromShiftedExt_scalar X (d + n) a _ }

set_option backward.isDefEq.respectTransparency false in
private theorem firstComparison_natural (E : residueFieldEnvelopeValue R)
    (h : IsPowerTorsion R E.carrier) (rs : List R) (d n : ℤ) (l : Comparison rs n)
    (e : Qd.obj ((D E).obj (op (CechComplex rs))) ≅ ((SD R).obj (B R))⟦d⟧)
    (he : ∀ a : A (R := R),
      Qd.map (hullPostcomp E (CechComplex rs) (hullScalar E a)) ≫ e.hom =
        e.hom ≫ (SDMapScalar a)⟦d⟧')
    {X X' : ModuleCat.{u} R} (f : X' ⟶ X) :
    (localDual E h (-n)).map f.op ≫ (firstComparison E h rs d n l e he X').toModuleIso.hom =
      (firstComparison E h rs d n l e he X).toModuleIso.hom ≫
        restrictedPull R X X' f (completedRingModule R) (d + n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  change fromShiftedExt X' _ (localDualToShiftedHom E rs d n l e X'
    ((dualLC E n).map f.op x)) = restrictedPull R X X' f (completedRingModule R) (d + n)
      (fromShiftedExt X _ (localDualToShiftedHom E rs d n l e X x))
  exact Eq.trans (congrArg (fromShiftedExt X' (d + n))
    (localDualToShiftedHom_natural E rs d n l e f x)) (fromShiftedExt_precomp f (d + n) _)

end Assembly

private lemma completionToCoefficient_inv_natural {X X' : ModuleCat.{u} R}
    [Module.Finite R X] [Module.Finite R X'] (f : X' ⟶ X) (j : ℤ) :
    restrictedPull R X X' f (completedRingModule R) j ≫ (completionToCoefficient X' j).inv =
      (completionToCoefficient X j).inv ≫ (complete R).map (extPull f (ringModule R) j) := by
  rw [← cancel_epi (completionToCoefficient X j).hom,
    ← cancel_mono (completionToCoefficient X' j).hom]
  simpa only [Category.assoc, Iso.inv_hom_id, Iso.hom_inv_id_assoc, Category.comp_id]
    using (completionToCoefficient_natural f j).symm

/-- Gorenstein local duality for finite modules, including every integer degree. -/
theorem gorensteinLocalDuality : LocalDuality.{u} := by
  intro R _ _ _ hG d hd E
  let := HasDerivedCategory.standard (ModuleCat.{u} R)
  classical
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian (maximalIdeal R))
  let rs : List R := s.toList
  have hrs : Ideal.span {r | r ∈ rs} = maximalIdeal R := by
    have hset : {r | r ∈ rs} = (↑s : Set R) := by
      ext r
      exact Finset.mem_toList
    rw [hset]
    exact hs
  obtain ⟨e, he⟩ := dualCechTarget hG d hd E rs hrs
  let h := residueHull_powerTorsion E
  have perDegree (i : ℤ) :
      ∃ c : ∀ (X : ModuleCat.{u} R) [Module.Finite R X],
        (localDual E h i).obj (op X) ≅
          signedRestrictedExt R X (completedRingModule R) ((d : ℤ) - i),
      ∀ (X X' : ModuleCat.{u} R) [Module.Finite R X] [Module.Finite R X'] (f : X' ⟶ X),
        (localDual E h i).map f.op ≫ (c X').hom =
          (c X).hom ≫ restrictedPull R X X' f (completedRingModule R) ((d : ℤ) - i) := by
    obtain ⟨n, rfl⟩ : ∃ n : ℤ, -n = i := ⟨-i, neg_neg i⟩
    rw [sub_neg_eq_add]
    obtain ⟨l⟩ := localCohomologyCechComparison (maximalIdeal R) rs hrs (-n)
    refine ⟨fun X _ => (firstComparison E h rs (d : ℤ) n l e he X).toModuleIso, ?_⟩
    intro X X' _ _ f
    exact firstComparison_natural E h rs (d : ℤ) n l e he f
  choose c hc using perDegree
  refine ⟨h, fun X _ i => c i X, fun X _ i => (completionToCoefficient X ((d : ℤ) - i)).symm, ?_⟩
  intro X X' _ _ f i
  exact ⟨hc i X X' f, completionToCoefficient_inv_natural f _⟩

end CommutativeAlgebraNotes.GorensteinLocalDuality
