import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.ArtinianLocalCohomology
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MinimalInjectiveResolution
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.MatlisDualityAfterCompletion
import Mathlib.Algebra.Category.ModuleCat.Ext.Finite
import Mathlib.Algebra.Category.ModuleCat.Ulift
import Mathlib.RingTheory.Finiteness.Small

/-! Artinianness of local cohomology and finiteness of its Matlis dual. -/

noncomputable section

namespace CommutativeAlgebraNotes

open CategoryTheory IsLocalRing AdvCommAlg.Depth
open scoped ZeroObject
open Specs.CommutativeAlgebraNotes.CompletionOfTorsionModules
  (Completion IsPowerTorsion)
open Specs.CommutativeAlgebraNotes.ArtinianLocalCohomology
open MinimalInjectiveResolutionSoclesSpecs (residueObject)

universe u v w

variable {R : Type u} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]

private theorem localCohomology_artinian_nat (X : ModuleCat.{u} R) [Module.Finite R X]
    (n : ℕ) : IsArtinian R ((localCohomology (maximalIdeal R) (n : ℤ)).obj X) := by
  obtain ⟨J⟩ := exists_minimalInjectiveResolution X
  obtain ⟨E⟩ := residueFieldEnvelope_exists R
  let I := J.toInjectiveResolution
  let F := idealTorsionFunctor (maximalIdeal R)
  let K := (F.mapHomologicalComplex (ComplexShape.up ℕ)).obj I.cocomplex
  obtain ⟨e, _⟩ := minimalInjectiveResolution_residueExt_socle J n
  let : Module.Finite R (residueObject R) := inferInstanceAs
    (Module.Finite R (R ⧸ maximalIdeal R))
  let : Module.Finite R (ResidueExt X n) := ModuleCat.finite_ext R (residueObject R) X n
  let : Module.Finite (ResidueField R) (ResidueExt X n) :=
    Module.Finite.of_restrictScalars_finite R (ResidueField R) (ResidueExt X n)
  have hSocle : FiniteDimensional (ResidueField R) (Socle R (I.cocomplex.X n)) :=
    Module.Finite.equiv e
  let : Injective (I.cocomplex.X n) := I.injective n
  have hInjective : Module.Injective R (I.cocomplex.X n) :=
    Module.injective_module_of_injective_object R (I.cocomplex.X n)
  obtain ⟨eTorsion⟩ := injective_torsion_equiv_hullPower E hInjective hSocle
  let : IsArtinian R E.carrier := residueHull_artinian E
  let : IsArtinian R (K.X n) := isArtinian_of_linearEquiv eTorsion.symm
  let : IsArtinian R (K.cycles n) := isArtinian_of_injective (K.iCycles n).hom
    ((ModuleCat.mono_iff_injective _).mp inferInstance)
  let : IsArtinian R (K.homology n) := isArtinian_of_surjective _ (K.homologyπ n).hom
    ((ModuleCat.epi_iff_surjective _).mp inferInstance)
  rw [localCohomology_of_nonneg _ _ (Int.natCast_nonneg n), Int.toNat_natCast]
  let eDerived : K.homology n ≃ₗ[R] ((F.rightDerived n).obj X) :=
    (I.isoRightDerivedObj F n).symm.toLinearEquiv
  exact isArtinian_of_linearEquiv eDerived

/-- Lifting the universe commutes with taking maximal-ideal torsion. -/
private def torsionUliftIso :
    idealTorsionFunctor (maximalIdeal R) ⋙ ModuleCat.uliftFunctor.{w, v} R ≅
      ModuleCat.uliftFunctor.{w, v} R ⋙ idealTorsionFunctor (maximalIdeal R) := by
  refine NatIso.ofComponents ?_ ?_
  · intro X
    let I := maximalIdeal R
    have h (x : ULift.{w} X) :
        x.down ∈ idealTorsion I X ↔ x ∈ idealTorsion I (ULift.{w} X) := by
      simp only [mem_idealTorsion, ← ULift.down_inj]
      rfl
    exact (show ULift.{w} (idealTorsion I X) ≃ₗ[R] idealTorsion I (ULift.{w} X) from
      { toFun := fun x => ⟨ULift.up x.down.val, (h _).mp x.down.property⟩
        invFun := fun x => ULift.up ⟨x.val.down, (h _).mpr x.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }).toModuleIso
  · intro X Y f
    exact ModuleCat.hom_ext (LinearMap.ext fun _ => rfl)

/-- The lifted injective resolution computes local cohomology in the larger universe. -/
private def localCohomologyUliftEquiv [Small.{v} R] (X : ModuleCat.{v} R) (i : ℤ) :
    letI := small_lift.{u, w} R
    ((localCohomology.{v} (maximalIdeal R) i).obj X) ≃ₗ[R]
      ((localCohomology.{max v w} (maximalIdeal R) i).obj ((ModuleCat.uliftFunctor.{w, v} R).obj X)) := by
  letI := small_lift.{u, w} R
  cases i with
  | ofNat n =>
    let F := idealTorsionFunctor.{v} (maximalIdeal R)
    let G := idealTorsionFunctor.{max v w} (maximalIdeal R)
    let L := ModuleCat.uliftFunctor.{w, v} R
    let c := ComplexShape.up ℕ
    let I := injectiveResolution X
    let J : InjectiveResolution (L.obj X) :=
      { cocomplex := (L.mapHomologicalComplex c).obj I.cocomplex
        injective := fun j => by
          change Injective (L.obj (I.cocomplex.X j))
          infer_instance
        ι := ((HomologicalComplex.singleMapHomologicalComplex L c 0).inv.app X) ≫
          (L.mapHomologicalComplex c).map I.ι }
    let K := (F.mapHomologicalComplex c).obj I.cocomplex
    let e := (NatIso.mapHomologicalComplex (torsionUliftIso (R := R)) c).app I.cocomplex
    let eH : (HomologicalComplex.homologyFunctor _ c n).obj
        ((L.mapHomologicalComplex c).obj K) ≅ L.obj (K.homology n) :=
      (K.sc n).mapHomologyIso L
    let e' := L.mapIso (I.isoRightDerivedObj F n) ≪≫ eH.symm ≪≫
      (HomologicalComplex.homologyFunctor _ c n).mapIso e ≪≫ (J.isoRightDerivedObj G n).symm
    exact (ULift.moduleEquiv.symm : _ ≃ₗ[R]
      (L.obj ((F.rightDerived n).obj X))).trans e'.toLinearEquiv
  | negSucc n =>
    change ((0 : ModuleCat.{v} R ⥤ ModuleCat.{v} R).obj X) ≃ₗ[R]
      ((0 : ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} R).obj
        ((ModuleCat.uliftFunctor.{w, v} R).obj X))
    let : Subsingleton ((0 : ModuleCat.{v} R ⥤ ModuleCat.{v} R).obj X) :=
      ModuleCat.isZero_iff_subsingleton.mp (Functor.zero_obj X)
    let : Subsingleton ((0 : ModuleCat.{max v w} R ⥤ ModuleCat.{max v w} R).obj
        ((ModuleCat.uliftFunctor.{w, v} R).obj X)) :=
      ModuleCat.isZero_iff_subsingleton.mp (Functor.zero_obj _)
    exact LinearEquiv.ofSubsingleton _ _

/-- A finite module has a model in the ring's universe, with the same local cohomology. -/
private theorem localCohomology_artinian_small [Small.{v} R]
    (X : ModuleCat.{v} R) [Module.Finite R X] (i : ℤ) :
    IsArtinian R ((localCohomology (maximalIdeal R) i).obj X) ∧
      Small.{u} ((localCohomology (maximalIdeal R) i).obj X) := by
  let : Small.{u} X := Module.Finite.small.{u} R X
  let Y := ModuleCat.of R (Shrink.{u} X)
  let e : X ≃ₗ[R] Y := (Shrink.linearEquiv R X).symm
  let : Module.Finite R Y := Module.Finite.equiv e
  let L := ModuleCat.uliftFunctor.{u, v} R
  let L' := ModuleCat.uliftFunctor.{v, u} R
  let eLift : L.obj X ≃ₗ[R] L'.obj Y :=
    ULift.moduleEquiv.trans (e.trans ULift.moduleEquiv.symm)
  let G := localCohomology.{max u v} (maximalIdeal R) i
  let eH : ((localCohomology (maximalIdeal R) i).obj X) ≃ₗ[R]
      ((localCohomology.{u} (maximalIdeal R) i).obj Y) :=
    (localCohomologyUliftEquiv.{u, v, u} X i).trans
      ((G.mapIso eLift.toModuleIso).toLinearEquiv.trans
        (localCohomologyUliftEquiv.{u, u, v} Y i).symm)
  let : IsArtinian R ((localCohomology.{u} (maximalIdeal R) i).obj Y) := by
    cases i with
    | ofNat n => exact localCohomology_artinian_nat Y n
    | negSucc n =>
      change IsArtinian R ((0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R).obj Y)
      let : Subsingleton ((0 : ModuleCat.{u} R ⥤ ModuleCat.{u} R).obj Y) :=
        ModuleCat.isZero_iff_subsingleton.mp (Functor.zero_obj Y)
      exact isArtinian_of_finite
  exact ⟨isArtinian_of_linearEquiv eH.symm, small_of_injective eH.injective⟩

/-- Every maximal-ideal local cohomology module of a finite module is Artinian. -/
theorem localCohomology_artinian : localCohomologyArtinianType.{u, v} := by
  intro R _ _ _ _ X _ i
  exact (localCohomology_artinian_small X i).1

/-- The Matlis dual of maximal-ideal local cohomology is finite over the completion. -/
theorem localCohomology_matlisDual_finite : localCohomologyDualFiniteType.{u, v} := by
  intro R _ _ _ _ E X _ i
  let H := (localCohomology (maximalIdeal R) i).obj X
  have hE : IsPowerTorsion R E.carrier := by
    let : IsArtinian R E.carrier := residueHull_artinian E
    intro x
    change x ∈ idealTorsion (maximalIdeal R) E.carrier
    rw [idealTorsion_eq_top_of_isArtinian]
    exact Submodule.mem_top
  refine ⟨hE, ?_⟩
  let := CompletionOfTorsionModules.completionModule hE
  let := CompletionOfTorsionModules.completionScalarTower hE
  obtain ⟨F⟩ := residueFieldEnvelope_exists (Completion R)
  obtain ⟨hA, _, _, _, _⟩ := matlisDualityAfterCompletion F
  obtain ⟨hH, hSmall⟩ := localCohomology_artinian_small X i
  let : Small.{u} H := hSmall
  let H' := ModuleCat.of R (Shrink.{u} H)
  let eH : H' ≃ₗ[R] H := Shrink.linearEquiv R H
  let : IsArtinian R H := hH
  let A : (CompleteMatlisDualitySpecs.artinianModules R).FullSubcategory :=
    ⟨H', isArtinian_of_linearEquiv eH.symm⟩
  obtain ⟨e, _⟩ := residueFieldEnvelope_equiv E
    (MatlisHullUnderCompletion.restrictResidueFieldEnvelope F)
  let := MatlisHullUnderCompletion.restrictedHullModule F
  let := MatlisHullUnderCompletion.restrictedHullScalarTower F
  let : Module.Finite (Completion R) (H' →ₗ[R] F.carrier) := hA (Opposite.op A)
  let precomp := LinearMap.lcomp (Completion R) F.carrier eH.symm.toLinearMap
  let : Module.Finite (Completion R) (H →ₗ[R] F.carrier) :=
    Module.Finite.of_surjective precomp (fun φ =>
      ⟨φ.comp eH.toLinearMap, LinearMap.ext fun x =>
        congrArg φ (eH.apply_symm_apply x)⟩)
  let f := (MatlisHullUnderCompletion.powerTorsionHomEquiv
    (MatlisHullUnderCompletion.restrictedHull_powerTorsion F)).symm e.symm.toLinearMap
  let g : (H →ₗ[R] F.carrier) →ₗ[Completion R] (H →ₗ[R] E.carrier) :=
    { toFun := fun φ => e.symm.toLinearMap.comp φ
      map_add' _ _ := LinearMap.ext fun x => e.symm.map_add _ _
      map_smul' s φ := LinearMap.ext fun x => f.map_smul s (φ x) }
  exact Module.Finite.of_surjective g (fun φ => ⟨e.toLinearMap.comp φ,
    LinearMap.ext fun x => e.symm_apply_apply (φ x)⟩)

end CommutativeAlgebraNotes
