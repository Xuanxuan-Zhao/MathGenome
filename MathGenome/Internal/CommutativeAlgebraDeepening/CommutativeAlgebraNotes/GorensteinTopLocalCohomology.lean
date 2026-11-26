import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MinimalInjectiveResolution
import MathGenome.Internal.AdvancedCommutativeAlgebra.AdvCommAlg.Gorenstein.GorensteinExtProfile
import Mathlib.LinearAlgebra.Pi

/-! The top local cohomology of a Gorenstein local ring. -/

noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing
open AdvCommAlg.Depth AdvCommAlg.Gorenstein

namespace CommutativeAlgebraNotes

open _root_.Specs.CommutativeAlgebraNotes.GorensteinTopLocalCohomology
  (torsionComplex derivedTorsionOfRing derivedComparisonChoiceType)

universe u w

variable {R : Type u} [CommRing R] [IsLocalRing R]

private theorem gorenstein_torsion_terms_nat [IsNoetherianRing R]
    (hG : LocalGorenstein R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : MinimalInjectiveResolution (ModuleCat.of R R)) (E : ResidueFieldEnvelope R) :
    (∀ i : ℕ, i ≠ d → IsZero ((torsionComplex J).X (i : ℤ))) ∧
      Nonempty ((torsionComplex J).X (d : ℤ) ≅ ModuleCat.of R E.carrier) := by
  let I := J.toInjectiveResolution
  let F := idealTorsionFunctor (maximalIdeal R)
  let termIso (i : ℕ) :
      (torsionComplex J).X (i : ℤ) ≅ F.obj (I.cocomplex.X i) :=
    F.mapIso (I.cochainComplexXIso (i : ℤ) i rfl)
  have termInjective (i : ℕ) : Module.Injective R (I.cocomplex.X i) :=
    Module.injective_module_of_injective_object R _ (inj := I.injective i)
  constructor
  · intro i hi
    obtain ⟨socleIso, _⟩ := minimalInjectiveResolution_residueExt_socle J i
    have := localGorenstein_ext_vanishing R hG d hd i hi
    have : Subsingleton (Socle R (I.cocomplex.X i)) := socleIso.symm.injective.subsingleton
    have : FiniteDimensional (ResidueField R) (Socle R (I.cocomplex.X i)) := inferInstance
    obtain ⟨e⟩ := injective_torsion_equiv_hullPower E (termInjective i) inferInstance
    rw [Module.finrank_eq_zero_of_subsingleton] at e
    have hT : Subsingleton (idealTorsion (maximalIdeal R) (I.cocomplex.X i)) :=
      e.injective.subsingleton
    exact (ModuleCat.isZero_iff_subsingleton.mpr hT :
      IsZero (F.obj (I.cocomplex.X i))).of_iso (termIso i)
  · obtain ⟨socleIso, _⟩ := minimalInjectiveResolution_residueExt_socle J d
    obtain ⟨extIso⟩ := localGorenstein_ext_equiv R hG d hd
    let e := socleIso.symm.trans extIso
    have : FiniteDimensional (ResidueField R) (Socle R (I.cocomplex.X d)) :=
      FiniteDimensional.of_injective e.toLinearMap e.injective
    have hdim : Module.finrank (ResidueField R) (Socle R (I.cocomplex.X d)) = 1 :=
      e.finrank_eq.trans (Module.finrank_self _)
    obtain ⟨equiv⟩ := injective_torsion_equiv_hullPower E (termInjective d) inferInstance
    rw [hdim] at equiv
    exact ⟨termIso d ≪≫ (equiv.trans (LinearEquiv.funUnique (Fin 1) R E.carrier)).toModuleIso⟩

/-- Maximal-ideal torsion in the minimal resolution is zero away from the
dimension and is the chosen hull in the dimension. -/
theorem gorenstein_torsion_term_profile [IsNoetherianRing R]
    (hG : LocalGorenstein R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : MinimalInjectiveResolution (ModuleCat.of R R)) (E : ResidueFieldEnvelope R) :
    (∀ i : ℤ, i ≠ (d : ℤ) → IsZero ((torsionComplex J).X i)) ∧
      Nonempty ((torsionComplex J).X (d : ℤ) ≅ ModuleCat.of R E.carrier) := by
  obtain ⟨haway, htop⟩ := gorenstein_torsion_terms_nat hG d hd J E
  refine ⟨fun i hi => ?_, htop⟩
  by_cases hn : 0 ≤ i
  · obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hn
    exact haway n (fun h => hi (congrArg (fun a : ℕ => (a : ℤ)) h))
  · exact (idealTorsionFunctor (maximalIdeal R)).map_isZero
      (CochainComplex.isZero_of_isStrictlyGE J.toInjectiveResolution.cochainComplex
        0 i (lt_of_not_ge hn))

/-- The comparison with a stalk extends the prescribed isomorphism in the
top degree. Replacing this isomorphism postcomposes by a hull automorphism. -/
theorem gorenstein_torsion_complex_comparison [IsNoetherianRing R]
    (hG : LocalGorenstein R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (J : MinimalInjectiveResolution (ModuleCat.of R R)) (E : ResidueFieldEnvelope R) :
    let A := ModuleCat.of R E.carrier
    let stalk := CochainComplex.singleFunctor (ModuleCat.{u} R) (d : ℤ)
    ∃ compare : (((torsionComplex J).X (d : ℤ)) ≅ A) → (torsionComplex J ≅ stalk.obj A),
      (∀ e, HomologicalComplex.Hom.isoApp (compare e) (d : ℤ) ≪≫
        HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (d : ℤ) A = e) ∧
      ∀ e f, compare f = compare e ≪≫ stalk.mapIso (e.symm ≪≫ f) := by
  classical
  dsimp only
  let A := ModuleCat.of R E.carrier
  let K := torsionComplex J
  let L := (CochainComplex.singleFunctor (ModuleCat.{u} R) (d : ℤ)).obj A
  let atTop := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) (d : ℤ) A
  have hzero := (gorenstein_torsion_term_profile hG d hd J E).1
  have hdifferential (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) : K.d i j = 0 := by
    by_cases hi : i = (d : ℤ)
    · have hj : j ≠ (d : ℤ) := by
        change i + 1 = j at hij
        omega
      exact (hzero j hj).eq_of_tgt _ _
    · exact (hzero i hi).eq_of_src _ _
  let component (e : K.X (d : ℤ) ≅ A) (i : ℤ) : K.X i ≅ L.X i :=
    if hi : i = (d : ℤ) then
      K.XIsoOfEq hi ≪≫ e ≪≫ (HomologicalComplex.singleObjXIsoOfEq
        (ComplexShape.up ℤ) (d : ℤ) A i hi).symm
    else
      (hzero i hi).iso (HomologicalComplex.isZero_single_obj_X
        (ComplexShape.up ℤ) (d : ℤ) A i hi)
  let compare (e : K.X (d : ℤ) ≅ A) : K ≅ L :=
    HomologicalComplex.Hom.isoOfComponents (component e) (fun i j hij => by
      rw [hdifferential i j hij]
      simp [L])
  have htop (e : K.X (d : ℤ) ≅ A) :
      HomologicalComplex.Hom.isoApp (compare e) (d : ℤ) = e ≪≫ atTop.symm := by
    rw [HomologicalComplex.Hom.isoOfComponents_app]
    simp [component, atTop, HomologicalComplex.singleObjXSelf]
  refine ⟨compare, fun e => ?_, fun e f => ?_⟩
  · change HomologicalComplex.Hom.isoApp (compare e) (d : ℤ) ≪≫ atTop = e
    rw [htop]
    simp
  · apply Iso.ext
    apply HomologicalComplex.to_single_hom_ext
    have hcomponent (g : K.X (d : ℤ) ≅ A) :
        (compare g).hom.f (d : ℤ) = g.hom ≫ atTop.inv :=
      congrArg Iso.hom (htop g)
    change (compare f).hom.f (d : ℤ) =
      (compare e).hom.f (d : ℤ) ≫
        ((HomologicalComplex.single (ModuleCat.{u} R) (ComplexShape.up ℤ) (d : ℤ)).map
          (e.inv ≫ f.hom)).f (d : ℤ)
    rw [hcomponent, hcomponent, HomologicalComplex.single_map_f_self]
    change f.hom ≫ atTop.inv =
      (e.hom ≫ atTop.inv) ≫ atTop.hom ≫ (e.inv ≫ f.hom) ≫ atTop.inv
    simp

/-- A chosen minimal resolution computes the total right derived torsion
functor evaluated at the ring in degree zero. -/
theorem minimalResolution_torsion_computes_derived
    [HasDerivedCategory.{w} (ModuleCat.{u} R)] (J : MinimalInjectiveResolution (ModuleCat.of R R)) :
    Nonempty (derivedTorsionOfRing R ≅ DerivedCategory.Q.obj (torsionComplex J)) := by
  let C := ModuleCat.{u} R
  let I := J.toInjectiveResolution
  let F := idealTorsionFunctor (maximalIdeal R)
  let K : CochainComplex.Plus C :=
    ⟨(CochainComplex.singleFunctor C 0).obj (ModuleCat.of R R), ⟨0, inferInstance⟩⟩
  let L : CochainComplex (InjectiveObject C) ℤ :=
    HomologicalComplex.liftObjectProperty _ I.cochainComplex inferInstance
  have hL : L.IsStrictlyGE 0 := by
    rw [← CochainComplex.isStrictlyGE_mapHomologicalComplex_obj_iff _ (InjectiveObject.ι C)]
    exact (inferInstance : I.cochainComplex.IsStrictlyGE 0)
  let Lplus : CochainComplex.Plus (InjectiveObject C) := ⟨L, ⟨0, hL⟩⟩
  let Y := (InjectiveObject.ι C).mapCochainComplexPlus.obj Lplus
  let ι : K ⟶ Y := ObjectProperty.homMk I.ι'
  have hι : CochainComplex.Plus.quasiIso C ι := (inferInstance : QuasiIso I.ι')
  let e := Localization.isoOfHom DerivedCategory.Plus.Q (CochainComplex.Plus.quasiIso C) ι hι
  let comparison := F.rightDerivedFunctorPlus.mapIso e ≪≫
    (asIso (F.rightDerivedFunctorPlusUnit.app Y)).symm
  exact ⟨DerivedCategory.Plus.ι.mapIso comparison⟩

/-- Postcomposition by the hull automorphism also gives the change of
comparison after passing to the derived category and shifting. -/
theorem gorenstein_derived_torsion_comparison : derivedComparisonChoiceType.{u, w} := by
  intro R _ _ _ _ hG d hd J E compute
  dsimp only
  obtain ⟨chainCompare, htop, hchange⟩ := gorenstein_torsion_complex_comparison hG d hd J E
  refine ⟨chainCompare, htop, fun e f => ?_⟩
  let C := ModuleCat.{u} R
  let A := ModuleCat.of R E.carrier
  let shiftedStalk := DerivedCategory.singleFunctor C 0 ⋙
    shiftFunctor (DerivedCategory C) (-(d : ℤ))
  let shiftIso := (DerivedCategory.singleFunctors C).shiftIso
    (-(d : ℤ)) (d : ℤ) 0 (neg_add_cancel _)
  have shift_naturality (a : A ≅ A) :
      (DerivedCategory.singleFunctor C (d : ℤ)).mapIso a ≪≫ (shiftIso.app A).symm =
        (shiftIso.app A).symm ≪≫ shiftedStalk.mapIso a := by
    apply Iso.ext
    exact shiftIso.inv.naturality a.hom
  change (compute ≪≫ DerivedCategory.Q.mapIso (chainCompare f) ≪≫ (shiftIso.app A).symm) =
    (compute ≪≫ DerivedCategory.Q.mapIso (chainCompare e) ≪≫ (shiftIso.app A).symm) ≪≫
      shiftedStalk.mapIso (e.symm ≪≫ f)
  rw [hchange e f, Functor.mapIso_trans]
  simp only [Iso.trans_assoc]
  change compute ≪≫ DerivedCategory.Q.mapIso (chainCompare e) ≪≫
    (DerivedCategory.singleFunctor C (d : ℤ)).mapIso (e.symm ≪≫ f) ≪≫ (shiftIso.app A).symm = _
  rw [shift_naturality]

/-- For a Noetherian Gorenstein local ring of dimension `d`, the total
right derived maximal-ideal torsion of the ring is `E[-d]`. -/
theorem gorenstein_top_localCohomology [IsNoetherianRing R]
    [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    (hG : LocalGorenstein R) (d : ℕ) (hd : ringKrullDim R = (d : WithBot ℕ∞))
    (E : ResidueFieldEnvelope R) :
    Nonempty (derivedTorsionOfRing R ≅
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R) 0).obj
        (ModuleCat.of R E.carrier))⟦-(d : ℤ)⟧) := by
  obtain ⟨J⟩ := exists_minimalInjectiveResolution (ModuleCat.of R R)
  obtain ⟨e⟩ := (gorenstein_torsion_term_profile hG d hd J E).2
  obtain ⟨compare, _, _⟩ := gorenstein_torsion_complex_comparison hG d hd J E
  obtain ⟨compute⟩ := minimalResolution_torsion_computes_derived J
  let shiftIso := (DerivedCategory.singleFunctors (ModuleCat.{u} R)).shiftIso
    (-(d : ℤ)) (d : ℤ) 0 (neg_add_cancel _)
  exact ⟨compute ≪≫ DerivedCategory.Q.mapIso (compare e) ≪≫
    (shiftIso.app (ModuleCat.of R E.carrier)).symm⟩

end CommutativeAlgebraNotes
