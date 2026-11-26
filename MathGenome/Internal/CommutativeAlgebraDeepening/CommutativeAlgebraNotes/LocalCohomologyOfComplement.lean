import MathGenome.Internal.CommutativeAlgebraDeepening.Specs.CommutativeAlgebraNotes.LocalCohomologyOfComplement
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
import MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.DerivedCechComparison
import Mathlib.Algebra.Homology.SingleHomology
import Mathlib.CategoryTheory.Preadditive.LeftExact
import Batteries.Tactic.OpenPrivate

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor CategoryTheory.Limits
open CategoryTheory.Pretriangulated HomologicalComplex
open Specs.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement
open Specs.CommutativeAlgebraNotes.LocalCohomologyOfComplement
open Specs.CommutativeAlgebraNotes.IdealTorsion
open Specs.CommutativeAlgebraNotes.AugmentedCechComplex (tensorFunctor)
open Specs.CommutativeAlgebraNotes.InjectiveCechComparison (singleZero projection)

namespace CommutativeAlgebraNotes

universe u

set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

theorem complementRestriction_app (R : CommRingCat.{u}) (I : Ideal R)
    (M : ModuleCat.{u} R) :
    (complementRestriction R I).app M = tilde.toOpen M (complement R I) :=
  tilde.toOpen_res M ⊤ (complement R I) (homOfLE le_top)

section

attribute [local instance] HasDerivedCategory.standard

variable {R : CommRingCat.{u}}

private abbrev Mod (R : CommRingCat.{u}) := ModuleCat.{u} R
private abbrev D (R : CommRingCat.{u}) := DerivedCategory (Mod R)
private noncomputable abbrev H (R : CommRingCat.{u}) :=
  DerivedCategory.homologyFunctor (Mod R)

private theorem exists_generating_list [IsNoetherianRing R] (I : Ideal R) :
    ∃ rs : List R, Ideal.span {r | r ∈ rs} = I := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
  refine ⟨s.toList, ?_⟩
  simp only [Finset.mem_toList]
  exact hs

private theorem affineDerivedHomology_isZero
    (e : singleZero R ⋙ DerivedCategory.Q ≅ derivedSections R ⊤)
    (M : (Mod R)) (q : ℤ) (hq : q ≠ 0) :
    IsZero ((H R q).obj ((derivedSections R ⊤).obj M)) := by
  let c := (DerivedCategory.homologyFunctorFactors (Mod R) q).app ((singleZero R).obj M)
  refine (HomologicalComplex.isZero_single_obj_homology (.up ℤ) 0 M q hq).of_iso ?_
  exact (H R q).mapIso (e.app M).symm ≪≫ c

private noncomputable def connecting {A B : (Mod R) ⥤ (D R)}
    (δ : B ⟶ A ⋙ shiftFunctor (D R) (1 : ℤ)) (q : ℤ) :
    B ⋙ H R q ⟶ A ⋙ H R (q + 1) :=
  whiskerRight δ (H R q) ≫
    (whiskerLeft A ((H R 0).shiftIso 1 q (q + 1) (add_comm 1 q)).hom)

private noncomputable def localCohomologyCechIso [IsNoetherianRing R]
    (I : Ideal R) (rs : List R) (hrs : Ideal.span {r | r ∈ rs} = I) (q : ℤ) :
    (singleZero R ⋙ tensorFunctor R rs ⋙ DerivedCategory.Q) ⋙ H R q ≅
      localCohomology.{u} I q :=
  isoWhiskerLeft (singleZero R ⋙ tensorFunctor R rs)
    (DerivedCategory.homologyFunctorFactors (Mod R) q) ≪≫
    (localCohomologyCechComparison I rs hrs q).some.symm

theorem localCohomologyComplement_higher : ComplementHigherCohomology.{u} := by
  intro R _ I q hq
  obtain ⟨rs, hrs⟩ := exists_generating_list I
  obtain ⟨eX, _, _, δ, _, hT⟩ := cechNaturalDerivedComparison R I rs hrs
  haveI : IsIso (connecting δ q) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro M
    let T := Triangle.mk
      (DerivedCategory.Q.map (projection rs ((singleZero R).obj M)) ≫ eX.hom.app M)
      ((derivedRestriction R (le_top : complement R I ≤ ⊤)).app M) (δ.app M)
    change IsIso ((H R 0).homologySequenceδ T q (q + 1) rfl)
    have ht : T ∈ distTriang (D R) := hT M
    have hm := (H R 0).homologySequence_exact₃ T ht q (q + 1) rfl
    have he := (H R 0).homologySequence_exact₁ T ht q (q + 1) rfl
    haveI : Mono ((H R 0).homologySequenceδ T q (q + 1) rfl) :=
      hm.mono_g_iff.mpr ((affineDerivedHomology_isZero eX M q (by omega)).eq_of_src _ _)
    haveI : Epi ((H R 0).homologySequenceδ T q (q + 1) rfl) :=
      he.epi_f_iff.mpr ((affineDerivedHomology_isZero eX M (q + 1) (by omega)).eq_of_tgt _ _)
    exact isIso_of_mono_of_epi _
  exact ⟨asIso (connecting δ q) ≪≫ localCohomologyCechIso I rs hrs (q + 1)⟩


open private sections_leftExact from MathGenome.Internal.CommutativeAlgebraDeepening.CommutativeAlgebraNotes.CechCohomologyOfOpenComplement

private noncomputable def sectionsStalkUnit (U : (Spec R).Opens) :
    (tilde.functor R ⋙ sections R U) ⋙ singleZero R ⋙ DerivedCategory.Q ⟶
      derivedSections R U :=
  let F := sections R U
  whiskerLeft (tilde.functor R)
      (whiskerRight (singleMapHomologicalComplex F (.up ℤ) 0).inv DerivedCategory.Q) ≫
    whiskerLeft (tilde.functor R ⋙ sheafStalkPlus R)
      (whiskerLeft F.mapCochainComplexPlus (DerivedCategory.Plus.QCompιIso (Mod R)).inv ≫
        whiskerRight F.rightDerivedFunctorPlusUnit DerivedCategory.Plus.ι)

private theorem sectionsStalkUnit_restrict {U V : (Spec R).Opens} (h : U ≤ V) (M : (Mod R)) :
    (sectionsStalkUnit V).app M ≫ (derivedRestriction R h).app M =
      DerivedCategory.Q.map ((singleZero R).map ((restrict R h).app (tilde M))) ≫
        (sectionsStalkUnit U).app M := by
  let F := sections R V
  let G := sections R U
  let τ := restrict R h
  let K := (sheafStalkPlus R).obj (tilde M)
  let S := DerivedCategory.Plus.QCompιIso (Mod R)
  let Q := DerivedCategory.Q (C := (Mod R))
  let L := DerivedCategory.Plus.ι (C := (Mod R))
  let f := (singleMapHomologicalComplex F (.up ℤ) 0).inv.app (tilde M)
  let g := (singleMapHomologicalComplex G (.up ℤ) 0).inv.app (tilde M)
  let ψ := τ.mapCochainComplexPlus.app K
  change (Q.map f ≫
      (S.inv.app (F.mapCochainComplexPlus.obj K) ≫ L.map (F.rightDerivedFunctorPlusUnit.app K))) ≫
      L.map (τ.rightDerivedFunctorPlus.app _) =
    Q.map ((singleZero R).map (τ.app (tilde M))) ≫
      (Q.map g ≫ (S.inv.app (G.mapCochainComplexPlus.obj K) ≫
        L.map (G.rightDerivedFunctorPlusUnit.app K)))
  have hc : f ≫ ψ.hom = (singleZero R).map (τ.app (tilde M)) ≫ g := by
    change f ≫ (τ.mapHomologicalComplex (.up ℤ)).app
        ((CochainComplex.singleFunctor (Spec R).Modules 0).obj (tilde M)) = _
    rw [natTransMapHomologicalComplex_app_single_obj, ← Category.assoc,
      Iso.inv_hom_id_app, Category.id_comp]
  have hn : Q.map ψ.hom ≫ S.inv.app (G.mapCochainComplexPlus.obj K) =
      S.inv.app (F.mapCochainComplexPlus.obj K) ≫ L.map (DerivedCategory.Plus.Q.map ψ) :=
    S.inv.naturality ψ
  have hf := τ.rightDerivedFunctorPlus_fac_app K
  change F.rightDerivedFunctorPlusUnit.app K ≫ τ.rightDerivedFunctorPlus.app _ =
      DerivedCategory.Plus.Q.map ψ ≫ G.rightDerivedFunctorPlusUnit.app K at hf
  simp only [Category.assoc]
  rw [← L.map_comp, hf, L.map_comp]
  rw [← reassoc_of% hn, ← Q.map_comp_assoc, hc, Q.map_comp, Category.assoc]

private noncomputable def singleZeroHomologyIso :
    (singleZero R ⋙ DerivedCategory.Q) ⋙ H R 0 ≅ 𝟭 (Mod R) :=
  isoWhiskerLeft (singleZero R) (DerivedCategory.homologyFunctorFactors (Mod R) 0) ≪≫
    homologyFunctorSingleIso (Mod R) (.up ℤ) 0

private noncomputable def sectionsDegreeZeroUnit (U : (Spec R).Opens) :
    tilde.functor R ⋙ sections R U ⟶ derivedSections R U ⋙ H R 0 :=
  (whiskerLeft (tilde.functor R ⋙ sections R U) singleZeroHomologyIso.inv) ≫
    whiskerRight (sectionsStalkUnit U) (H R 0)

private theorem sectionsDegreeZeroUnit_isIso (U : (Spec R).Opens) :
    IsIso (sectionsDegreeZeroUnit U) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  let F := sections R U
  let K := (sheafStalkPlus R).obj (tilde M)
  let S := DerivedCategory.Plus.QCompιIso (Mod R)
  letI : PreservesFiniteLimits F := sections_leftExact R U
  letI : K.obj.IsStrictlyGE 0 := by
    change ((CochainComplex.singleFunctor (Spec R).Modules 0).obj (tilde M)).IsStrictlyGE 0
    infer_instance
  haveI : IsIso ((DerivedCategory.Plus.homologyFunctor (Mod R) 0).map
      (F.rightDerivedFunctorPlusUnit.app K)) :=
    AdvancedHomologicalAlgebra.AcyclicTermComparison.rightComparison_lowest_degree F K 0
  change IsIso (singleZeroHomologyIso.inv.app (F.obj (tilde M)) ≫
    (H R 0).map (DerivedCategory.Q.map
      ((singleMapHomologicalComplex F (.up ℤ) 0).inv.app (tilde M)) ≫
      (S.inv.app (F.mapCochainComplexPlus.obj K) ≫
        DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K))))
  simp only [Functor.map_comp]
  haveI : IsIso ((H R 0).map
      (DerivedCategory.Plus.ι.map (F.rightDerivedFunctorPlusUnit.app K))) :=
    inferInstanceAs (IsIso ((DerivedCategory.Plus.homologyFunctor (Mod R) 0).map _))
  infer_instance


private theorem sectionsDegreeZeroUnit_restrict {U V : (Spec R).Opens} (h : U ≤ V) (M : (Mod R)) :
    (sectionsDegreeZeroUnit V).app M ≫ (H R 0).map ((derivedRestriction R h).app M) =
      (restrict R h).app (tilde M) ≫ (sectionsDegreeZeroUnit U).app M := by
  let f := (restrict R h).app (tilde M)
  let e := singleZeroHomologyIso (R := R)
  change (e.inv.app _ ≫ (H R 0).map ((sectionsStalkUnit V).app M)) ≫
      (H R 0).map ((derivedRestriction R h).app M) =
    f ≫ (e.inv.app _ ≫ (H R 0).map ((sectionsStalkUnit U).app M))
  rw [Category.assoc, ← (H R 0).map_comp, sectionsStalkUnit_restrict, (H R 0).map_comp]
  have hn : f ≫ e.inv.app _ =
      e.inv.app _ ≫ (H R 0).map (DerivedCategory.Q.map ((singleZero R).map f)) :=
    e.inv.naturality f
  rw [← Category.assoc f, hn, Category.assoc]
  rfl

private lemma idealTorsion_preservesFiniteLimits (I : Ideal R) :
    PreservesFiniteLimits (idealTorsionFunctor.{u} I) := by
  let F := idealTorsionFunctor.{u} I
  haveI {X Y : (Mod R)} (f : X ⟶ Y) : PreservesLimit (parallelPair f 0) F := by
    let c := ModuleCat.kernelCone f
    apply preservesLimit_of_preserves_limit_cone (ModuleCat.kernelIsLimit f)
    refine (c.isLimitMapConeEquiv F).symm ?_
    have hi : Function.Injective (F.map c.ι) := by
      intro x y h
      exact Subtype.ext (Subtype.ext (congrArg (fun z : F.obj X => z.val) h))
    have he : Function.Exact (F.map c.ι) (F.map f) := by
      intro x
      constructor
      · intro hx
        have hfx : f x.val = 0 := congrArg Subtype.val hx
        let y : LinearMap.ker f.hom := ⟨x.val, hfx⟩
        have hy : y ∈ idealTorsion I (LinearMap.ker f.hom) := by
          obtain ⟨n, hn, hx⟩ := (mem_idealTorsion I x.val).mp x.property
          refine (mem_idealTorsion I y).mpr ⟨n, hn, ?_⟩
          intro a ha
          exact Subtype.ext (hx a ha)
        exact ⟨⟨y, hy⟩, rfl⟩
      · rintro ⟨y, rfl⟩
        exact Subtype.ext y.val.property
    exact ModuleCat.isLimitKernelFork (F.map c.ι) (F.map f) he hi
  exact preservesFiniteLimits_of_preservesKernels F

theorem localCohomologyComplement_exact : ComplementExactSequence.{u} := by
  intro R _ I
  obtain ⟨rs, hrs⟩ := exists_generating_list I
  obtain ⟨eX, _, _, δ, _, hT⟩ := cechNaturalDerivedComparison R I rs hrs
  let U := complement R I
  let u₀ := sectionsDegreeZeroUnit U
  let c := localCohomologyCechIso I rs hrs 1
  let d : tilde.functor R ⋙ sections R U ⟶ localCohomology.{u} I 1 :=
    u₀ ≫ connecting δ 0 ≫ c.hom
  letI : PreservesFiniteLimits (idealTorsionFunctor.{u} I) :=
    idealTorsion_preservesFiniteLimits I
  let e := asIso ((idealTorsionFunctor.{u} I).toRightDerivedZero)
  refine ⟨e, d, rfl, ?_⟩
  intro M
  let a := (e.inv ≫ idealTorsionInclusion I).app M
  let b := (complementRestriction R I).app M
  change Function.Injective a ∧ Function.Exact a b ∧
    Function.Exact b (d.app M) ∧ Function.Surjective (d.app M)
  have hi : Function.Injective ((idealTorsionInclusion I).app M) := Subtype.val_injective
  have hei := (ModuleCat.mono_iff_injective (e.inv.app M)).mp inferInstance
  let T := Triangle.mk
    (DerivedCategory.Q.map (projection rs ((singleZero R).obj M)) ≫ eX.hom.app M)
    ((derivedRestriction R (le_top : U ≤ ⊤)).app M) (δ.app M)
  have ht : T ∈ distTriang (D R) := hT M
  let boundary := (H R 0).homologySequenceδ T 0 1 (by decide)
  haveI : IsIso u₀ := sectionsDegreeZeroUnit_isIso U
  have hd : d.app M = u₀.app M ≫ boundary ≫ c.hom.app M := rfl
  refine ⟨hi.comp hei, ?_, ?_, ?_⟩
  · intro x
    change (complementRestriction R I).app M x = 0 ↔ x ∈ Set.range a
    rw [complementRestriction_app]
    have hk := tildeComplement_torsionKernel R I M x
    refine hk.trans ⟨?_, ?_⟩
    · intro hx
      refine ⟨e.hom.app M ⟨x, hx⟩, ?_⟩
      simp [a]
      rfl
    · rintro ⟨z, rfl⟩
      exact (e.inv.app M z).property
  · let x₀ := (toSections R ⊤).app M ≫ (sectionsDegreeZeroUnit (⊤ : (Spec R).Opens)).app M
    haveI : IsIso (sectionsDegreeZeroUnit (⊤ : (Spec R).Opens)) := sectionsDegreeZeroUnit_isIso ⊤
    haveI : IsIso ((toSections R ⊤).app M) := tilde.isIso_toOpen_top
    haveI : IsIso x₀ := show IsIso (_ ≫ _) from inferInstance
    have hb : b ≫ u₀.app M = x₀ ≫ (H R 0).map T.mor₂ := by
      change ((toSections R ⊤).app M ≫ (restrict R (le_top : U ≤ ⊤)).app (tilde M)) ≫
          (sectionsDegreeZeroUnit U).app M =
        x₀ ≫ (H R 0).map ((derivedRestriction R (le_top : U ≤ ⊤)).app M)
      rw [Category.assoc, ← sectionsDegreeZeroUnit_restrict, ← Category.assoc]
    have hw : (H R 0).map T.mor₂ ≫ boundary = 0 :=
      (H R 0).comp_homologySequenceδ T ht 0 1 (by decide)
    have w : b ≫ d.app M = 0 := by
      rw [hd, ← Category.assoc, ← Category.assoc, hb, Category.assoc x₀, hw, comp_zero, zero_comp]
    let S := ShortComplex.mk b (d.app M) w
    have hS := (H R 0).homologySequence_exact₃ T ht 0 1 (by decide)
    have h : S.Exact := by
      apply ShortComplex.exact_of_iso _ hS
      apply Iso.symm
      refine ShortComplex.isoMk (asIso x₀) (asIso (u₀.app M)) (c.app M).symm hb.symm ?_
      change u₀.app M ≫ boundary = d.app M ≫ c.inv.app M
      simp only [hd, Category.assoc, Iso.hom_inv_id_app]
      exact (Category.comp_id _).symm
    exact (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp h
  · have he := (H R 0).homologySequence_exact₁ T ht 0 1 (by decide)
    haveI : Epi boundary :=
      he.epi_f_iff.mpr ((affineDerivedHomology_isZero eX M 1 (by decide)).eq_of_tgt _ _)
    rw [hd]
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance

end

end CommutativeAlgebraNotes
